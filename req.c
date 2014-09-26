#include <errno.h>
/* #include <setjmp.h> */
/* #include <signal.h> */
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "req.h"

void error(const char* m, ...)
{
    va_list args;
    va_start(args, m);
    vfprintf(stderr, m, args);
    va_end(args);
    fprintf(stderr, "\n");
    exit(1);
}

void stdError(const char* m)
{
    error("%s: %s", m, strerror(errno));
}

const char * const UnknownTypeMessage = "Unknown expression type";

/* --- Misc --- */

static Flag fileExists(const char* filename)
{
    FILE* file = fopen(filename, "r");
    if (file) {
        fclose(file);
        return true;
    } else
        return false;
}
    
/* --- Input stream --- */

#define CS_BUFFER_SIZE 256

CharStream makeCharStream(FILE* file)
{
    CharStream result;
    result.file = file;
    result.buffer = allot(CS_BUFFER_SIZE);
    result.scan_ptr = result.buffer;
    *result.scan_ptr = '\0';
    result.cur_char = '\n';
    charStreamAdvance(&result);
    return result;
}

CharStream stringToCharStream(const char *string)
{
    CharStream result;
    result.file = NULL;
    result.buffer = allot(strlen(string)+1);
    strcpy(result.buffer, string);
    result.scan_ptr = result.buffer + (*string ? 1 : 0);
    result.cur_char = *string ? *string : EOF;
    return result;
}

void closeCharStream(CharStream* cs)
{
    if (cs->file)
        fclose(cs->file);
    free(cs->buffer);
}

/* Get the next character from the file; return the current character. */
int charStreamAdvance(CharStream* cs)
{
    int result = charStreamCurrent(cs);
    if (*cs->scan_ptr == '\0') {	/* end of current line in buffer */
        if (result == EOF)
            return EOF;
        if (cs->file == stdin)
            printf("> ");		/* prompt for next line */
	else if (cs->file == NULL) {
	    cs->cur_char = EOF;
	    return result;
	}
        cs->scan_ptr = cs->buffer;
        if (!fgets(cs->buffer, CS_BUFFER_SIZE, cs->file))
            if (ferror(cs->file))
                stdError("Read error");
            else {
                cs->cur_char = EOF;
                *cs->scan_ptr = '\0';
            }
        else
            cs->cur_char = *cs->scan_ptr++;
    } else 
        cs->cur_char = *cs->scan_ptr++;
    return result;
}

void showPlaceInCurrentLine(const CharStream* cs)
{
    if (cs->cur_char != EOF) {
        printf("%s", cs->buffer);
        printf("%*s\n", cs->scan_ptr - cs->buffer, "^");
    }
}

/* --- Top-level commands --- */

static Expr evaluate(Expr);

/* Read and evaluate each expression in turn from file. */
static void load(const char* filename)
{
    FILE* file = fopen(filename, "r");
    if (!file) stdError(filename);
    {
        CharStream chars = makeCharStream(file);
        ParseStream exprs;
        parseExprs(&exprs, &chars);
        while (moreExprs(&exprs)) {
            Expr expr = nextExpr(&exprs);
            deref(evaluate(expr));
            deref(expr);
        }
        closeCharStream(&chars);
    }
}

static Rator assignment_rator, reduced_assignment_rator, 
            load_rator, trace_rator;
static Expr ok_sym;

Flag tracing = false;

/* If expr is a top-level command, perform the appropriate action; */
/* otherwise simplify it. Return the result. */
static Expr evaluate(Expr expr)
{
    if (type(expr) == EXP_APP) {
        Rator rator = appRator(expr);
        unsigned N = numRands(expr);
        if (ratorEqual(rator, assignment_rator) && N == 2) {
            installRule(nthRand(expr, 0), nthRand(expr, 1));
            return ref(ok_sym);
        } else if (ratorEqual(rator, reduced_assignment_rator) && N == 2) {
            Expr pattern = simplify(nthRand(expr, 0));
            Expr subst = simplify(nthRand(expr, 1));
            installRule(pattern, subst);
            deref(subst);
            deref(pattern);
            return ref(ok_sym);
        } else if (ratorEqual(rator, load_rator) && N == 1) {
            Expr arg = nthRand(expr, 0);
            if (type(arg) != EXP_STRING)
                return simplify(expr);
            else {
                load(String2pchar(litString(arg)));
                return ref(ok_sym);
            }
        } else if (ratorEqual(rator, trace_rator) && N == 1) {
            Expr result;
            tracing = true;
            result = simplify(nthRand(expr, 0));
            tracing = false;
            return result;
        } else
            return simplify(expr);
    } else
        return simplify(expr);
}

static void setupCommands(void)
{
    assignment_rator = Symbol2Rator(name2Symbol("=="));
    reduced_assignment_rator = Symbol2Rator(name2Symbol(":="));
    load_rator = Symbol2Rator(name2Symbol("load"));
    trace_rator = Symbol2Rator(name2Symbol("trace"));
    ok_sym = makeSymbol(name2Symbol("ok"));
}

/* --- Main program --- */

/*
static jmp_buf top_level_cont;

static void BreakKeyHandler(int foo)
{
    longjmp(top_level_cont, 1);
}
*/

/* Repeatedly read an expression, evaluate it, and print the result. */
static void driverLoop(CharStream chars)
{
    ParseStream exprs;
    parseExprs(&exprs, &chars);
    while (moreExprs(&exprs)) {
        Expr expr = nextExpr(&exprs);
/*	if (setjmp(top_level_cont) == 0) { */
            Expr simplified;
/*	    signal(SIGINT, BreakKeyHandler);	// move this to evaluate() when you get it working */
            simplified = evaluate(expr);
/*	    signal(SIGINT, SIG_DFL); */
            printlnExpr(simplified);
            deref(simplified);
/*	} else */
/*	    ; */
        deref(expr);
    }
    closeCharStream(&chars);
}

static int tryToLoad(const char *filename)
{
    if (!fileExists(filename)) 
	return 0;
    load(filename);
    return 1;
}

static void loadStartupScript(void)
{
    if (getenv("REQRC"))
	if (tryToLoad(getenv("REQRC")))
	    return;
    
    if (getenv("HOME")) {
	char filename[FILENAME_MAX+1];
	strncpy(filename, getenv("HOME"), sizeof filename);
	strncat(filename, "/.reqrc", sizeof filename);
	if (tryToLoad(filename))
	    return;
    }

    tryToLoad(".reqrc");
}

int main(int argc, char** argv)
{
    setupParser();
    setupRules();
    setupPrimitives();
    setupCommands();
    loadStartupScript();

    if (argc == 1)
	driverLoop(makeCharStream(stdin));
    else if (argc == 2)
	driverLoop(stringToCharStream(argv[1]));
    else
        error("usage: req optional-expression");
    return 0;
}
