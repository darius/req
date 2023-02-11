#include <assert.h>
#include <ctype.h>
#include <math.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "req.h"

#ifdef debug
static void trace(char* m, ...)
{
    va_list args;
    printf("\n");
    va_start(args, m);
    vprintf(m, args);
    va_end(args);
}
#endif

static ParseStream* theParseStream;

/* Ought to use stderr for these... */
static void lexicalError(char* m, ...)
{
    va_list args;
    printf("Lexical error: ");
    va_start(args, m);
    vprintf(m, args);
    va_end(args);
    printf("\n");
    showPlaceInCurrentLine(theParseStream->stream);
    exit(1);
}

static void syntaxError(char* m, ...)
{
    va_list args;
    printf("\nSyntax error: ");
    va_start(args, m);
    vprintf(m, args);
    va_end(args);
    printf("\n");
    showPlaceInCurrentLine(theParseStream->stream);	/* this has gotta change */
    exit(1);
}

/* --- Restriction names --- */

Symbol RestricNames[6];

void setupParser(void)
{
    RestricNames[EXP_NUMBER] = name2Symbol("number");
    RestricNames[EXP_STRING] = name2Symbol("string");
    RestricNames[EXP_FILE] = name2Symbol("file");
    RestricNames[EXP_SYMBOL] = name2Symbol("symbol");
    RestricNames[EXP_VAR] = name2Symbol("var");
    RestricNames[EXP_APP] = name2Symbol("app");
}

/* --- Operator info --- */

OpInfo NonOperatorInfo = { -1, -1, -1, -1 };

static OpInfo* makeOpInfo(int post, int pref, int inf, Flag right_to_left)
{
    OpInfo* result = allot(sizeof(OpInfo));
    result->postprec = 2*post;
    result->prefprec = 2*pref;
    result->lprec = 2*inf + (right_to_left ? 1 : 0);
    result->rprec = 2*inf + (right_to_left ? 0 : 1);
    return result;
}

OpInfo* makePrefixOpInfo(int pref)   { return makeOpInfo(-1, pref, -1, true); }
OpInfo* makePostfixOpInfo(int post)  { return makeOpInfo(post, -1, -1, true); }
OpInfo* makeInfixOpInfo(int inf)     { return makeOpInfo(-1, -1, inf, false); }
OpInfo* makeInfixRLOpInfo(int inf)   { return makeOpInfo(-1, -1, inf, true); }

static char opchars[] = "+-*/<=>^!&|:;~";
static char punct_chars[] = "()[]{},";

/* --- Scanning --- */

#define current()	( charStreamCurrent(theParseStream->stream) )
#define advance()	( charStreamAdvance(theParseStream->stream) )

/* Some token types */
#define SYMBOL		'A'
#define VARIABLE	'?'
#define NUMBER		'0'
#define STRING		'\''
#define END_LINE	'\n'
#define END_FILE	'\0'

#define token		( theParseStream->current_token )

#define tokenType()	( token.type )
#define tokenSymbol()	( token.contents.symbol )
#define tokenVariable()	( token.contents.variable )
#define tokenOp()	( *symbolOpInfo(tokenSymbol()) )
#define tokenNumber()	( token.contents.number )
#define tokenString()	( token.contents.string )
#define tokenPunct()	( token.contents.punct )

enum char_type { 
    OPCHAR, SEPARATOR, LINE_END_CHAR, FILE_END_CHAR, 
    DIGIT, PUNCTUATION, COMMENT, QUOTE, QUESTION, OTHER 
};

static enum char_type kind(int c)
{
    if (isdigit(c) || c == '.')
        return DIGIT;
    if (c == '\n')
        return LINE_END_CHAR;
    if (isspace(c))
        return SEPARATOR;
    if (c == '#')
        return COMMENT;
    if (c == EOF)
        return FILE_END_CHAR;
    if (c == '\'')
        return QUOTE;
    if (c == '?')
        return QUESTION;
    if (strchr(opchars, c))
        return OPCHAR;
    if (strchr(punct_chars, c))
        return PUNCTUATION;
    if (!isprint(c))
        lexicalError("Unprintable character - %c", c);
    return OTHER;
}

static void skipBlanks()
{
    for (;;) {	
        while (kind(current()) == SEPARATOR)
            advance();
        if (current() == '\n'
          && !charStreamIsInteractive(theParseStream->stream)) {
            advance();
            continue;
        }
        if (current() != '#')	/* '#' means comment */
            break;
        do {			/* skip to end of line */
            advance();
        } while (current() != '\n' && current() != EOF);
    }
}

static char buffer[513];
static char* buffer_ptr;

#define clearBuffer()	( buffer_ptr = buffer )

static void shift(int c)
{
    if (buffer_ptr - buffer >= sizeof(buffer))
        lexicalError("Token too long - %*.*s", 
                     sizeof(buffer), sizeof(buffer), buffer);
    *buffer_ptr++ = (char)c;
}

static void scanNumber(void)
{
    clearBuffer();
    while (isdigit(current()))
        shift(advance());
    if (current() == '.') {
        shift(advance());
        if (!isdigit(current()))
            lexicalError("Expecting digits after decimal point");
        do {
            shift(advance());
        } while (isdigit(current()));
    }
    shift('\0');
    tokenNumber() = (Number) atof(buffer);
    tokenType() = NUMBER;
}

static void scanString(void)
{
    advance();		/* skip leading quote */
    clearBuffer();
    while (current() != '\'') {
        if (current() == EOF)
            lexicalError("Unexpected end of file; expecting '");
        shift(advance());
    }
    advance();
    shift('\0');
    tokenString() = pchar2String(buffer);
    tokenType() = STRING;
}

static Symbol scanSymbol(void)
{
    clearBuffer();
    while (kind(current()) == OTHER || isdigit(current()))
        shift(advance());
    shift('\0');
    return name2Symbol(buffer);
}

static int lookupRestriction(Symbol name)
{
    unsigned i;
    for (i = 0; i < sizeof(RestricNames)/sizeof(*RestricNames); ++i)
        if (name == RestricNames[i])
            return i;
    lexicalError("Unknown restriction name - %s", symbolName(name));
    return 0;
}

static void scanVariable(void)
{
    Symbol var_name;
    int restriction;
    advance();		/* skip '?' */
    if (kind(current()) != OTHER)
        lexicalError("Expecting variable name");
    tokenType() = VARIABLE;
    var_name = scanSymbol();
    if (kind(current()) == QUESTION) {		/* restriction follows */
        advance();
        if (kind(current()) != OTHER)
            lexicalError("Expecting variable restriction");
        restriction = lookupRestriction(scanSymbol());
    } else
        restriction = NO_RESTRICTION;
    tokenVariable() = makeVariable(var_name, restriction);
}

static void getToken(void)
{
    if (theParseStream->delayed) {
        advance();
        theParseStream->delayed = false;
    }
    skipBlanks();
    switch (kind(current())) {
        case LINE_END_CHAR: 
            tokenType() = END_LINE;
            theParseStream->delayed = true;
            break;
        case FILE_END_CHAR:
            tokenType() = END_FILE;
            break;
        case QUOTE: 
            scanString();
            break;
        case QUESTION:
            scanVariable();
            break;
        case PUNCTUATION:
            tokenType() = (char)advance();
            break;
        case DIGIT:
            scanNumber();
            break;
        case OTHER:
            tokenSymbol() = scanSymbol();
            tokenType() = SYMBOL;
            break;
        case OPCHAR:
            clearBuffer();
            do {
                shift(advance());
            } while (kind(current()) == OPCHAR);
            shift('\0');
            tokenSymbol() = name2Symbol(buffer);
            tokenType() = SYMBOL;
            break;
        default: NOT_REACHED;
    }
}

static void needToken(void)
{
    while (tokenType() == END_LINE)
        getToken();
}

/* --- Parsing --- */

static Expr parseExpression(int);

static Expr parseRands(Rator rator)
{
    Expr result = makeApp0(rator);
    derefRator(rator);
    needToken();
    if (tokenType() == ')') {
        getToken();
        return result;
    }
    for (;;) {
        Expr rand = parseExpression(0);
        Expr temp = addRand(result, rand);
        deref(rand);
        deref(result);
        result = temp;
        needToken();
        if (tokenType() == ')') {
            getToken();
            break;
        }
        if (tokenType() != ',')
            syntaxError("Expecting comma or right parenthesis after operand");
        getToken();
    }
    return result;
}

static Expr parseFactor(void)
{
    needToken();
    switch (tokenType()) {
        case NUMBER: {
            Expr result = makeNumber(tokenNumber());
            getToken();
            return result;
        }
        case STRING: {
            Expr result = makeString(tokenString());
            getToken();
            return result;
        }
        case VARIABLE: {
            Expr maybe_rator = tokenVariable();
            getToken();
            if (tokenType() == '(') {		/* procedure application */
                getToken();
                return parseRands(maybe_rator);
            } else				/* literal variable */
                return maybe_rator;
        }
        case SYMBOL: {
            Expr maybe_rator = makeSymbol(tokenSymbol());
            if (0 < prefixPrecedence(tokenOp())) {
                OpInfo op = tokenOp();
                getToken();
                if (tokenType() == ')')		/* literal symbol */
                    return maybe_rator;
                else {				/* prefix operator */
                    Expr result, rand = parseExpression(prefixPrecedence(op));
                    result = makeApp1(maybe_rator, rand);
                    derefRator(maybe_rator);
                    deref(rand);
                    return result;
                }
            } else {
                getToken();
                if (tokenType() == '(') {	/* procedure application */
                    getToken();
                    return parseRands(maybe_rator);
                } else				/* literal symbol */
                    return maybe_rator;
            }
        }
        case '(': {
            Expr result;
            getToken();
            result = parseExpression(0);
            needToken();
            if (tokenType() != ')') syntaxError("Missing ')'");
            getToken();
            return result;
        }
        default: 
	    syntaxError("Unexpected token type");
	    return theNullExpr;
    }
}

static Expr parseExpression(int prec)
{
    Expr left = parseFactor();
    while (tokenType() == SYMBOL) {
        if (prec <= postfixPrecedence(tokenOp())) {
            Rator rator = Symbol2Rator(tokenSymbol());
            Expr new_left = makeApp1(rator, left);
            derefRator(rator);
            deref(left);
            left = new_left;
            getToken();
        } else if (prec <= leftPrecedence(tokenOp())) {
            int right_prec = rightPrecedence(tokenOp());
            Rator rator = Symbol2Rator(tokenSymbol());
            Expr right, new_left;
            getToken();
            right = parseExpression(right_prec);
            new_left = makeApp2(rator, left, right);
            derefRator(rator);
            deref(right);
            deref(left);
            left = new_left;
        } else
            break;
    }
    return left;
}

void parseExprs(ParseStream* pResult, CharStream* chars)
{
    pResult->stream = chars;
    pResult->delayed = false;
    theParseStream = pResult;
    getToken();
}

Flag moreExprs(ParseStream* ps)
{
    if (ps->current_token.type == END_FILE) return false;
    if (ps->current_token.type != END_LINE) return true;
    theParseStream = ps;
    needToken();
    return ps->current_token.type != END_FILE;
}

Expr nextExpr(ParseStream* ps)
{
    theParseStream = ps;
    return parseExpression(0);
}
