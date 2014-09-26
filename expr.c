#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "req.h"

void* allot(size_t size)
{
    void* result = malloc(size);
    if (!result && size != 0) 
        error("Out of memory - allot");
    return result;
}

/* --- Strings --- */

String pchar2String(const char* pchar)
{
    char* result = allotString(strlen(pchar));
    strcpy(result, pchar);
    return result;
}

String number2String(Number n)
{
    char buffer[21];		/* ought to be enough */
    sprintf(buffer, "%g", (double) n);
    return pchar2String(buffer);
}

String stringAppend(const String s1, const String s2)
{
    char* result = allotString(strlen(s1) + strlen(s2));
    strcpy(result, s1);
    strcat(result, s2);
    return result;
}

/* --- Expressions --- */

#ifdef debug	/* the DEBUG macro doesn't work here; arg is too long */
void checkExprRep(Expr expr)
{
    static char err[] = "Expr rep violation";
    if (expr->ref_count == 0) error(err);
    switch (type(expr)) {
        case EXP_NUMBER:
        case EXP_STRING:
            break;
        case EXP_FILE:
            if (fileIsOpen(expr) != true && fileIsOpen(expr) != false)
                error(err);
            break;
        case EXP_SYMBOL:
            checkSymbolRep(exprSymbol(expr));
            break;
        case EXP_VAR:
            checkSymbolRep(varName(expr));
            if (varRestriction(expr) < -1 || EXP_APP < varRestriction(expr))
                error(err);
            break;
        case EXP_APP: {
            unsigned i, N = numRands(expr);
            if (N > 50) error(err);		/* a reasonable presumption */
            checkExprRep(appRator(expr));
            for (i = 0; i < N; ++i)
                checkExprRep(nthRand(expr, i));
            break;
        }
        default: UNKNOWN_TYPE;
    }
}
#endif 

#define allotExpr()		allot(sizeof(struct Expr))
#define freeExpr		free

Expr ref(Expr expr)
{
    DEBUG(checkExprRep(expr);)
    ++expr->ref_count;
    return expr;
}

void freeRands(unsigned N, Expr* rands)
{
    unsigned i;
    for (i = 0; i < N; ++i)
        deref(rands[i]);
    free(rands);
}

void deref(Expr expr)
{
    DEBUG(checkExprRep(expr);)
    if (--expr->ref_count == 0) {
        switch (type(expr)) {
            case EXP_NUMBER:
            case EXP_SYMBOL:
            case EXP_VAR:
                break;
            case EXP_FILE:
                if (!fileIsOpen(expr))
                    fclose(litFile(expr));
                break;
            case EXP_STRING:
                freeString(litString(expr));
                break;
            case EXP_APP:
                deref(appRator(expr));
                freeRands(numRands(expr), appRands(expr));
                break;
            default: UNKNOWN_TYPE;
        }
        freeExpr(expr);
    }
}

static Expr makeExpr(enum ExprType type)
{
    Expr result = allotExpr();
    result->type = type;
    result->ref_count = 1;
    result->fully_reduced = false;
    return result;
}
    
Expr makeNumber(Number value)
{
    Expr result = makeExpr(EXP_NUMBER);
    litNumber(result) = value;
    DEBUG(checkExprRep(result);)
    return result;
}

Expr makeString(String string)
{
    Expr result = makeExpr(EXP_STRING);
    litString(result) = string;
    DEBUG(checkExprRep(result);)
    return result;
}

/* Pre: file is open. */
Expr makeFile(FILE* file)
{
    Expr result= makeExpr(EXP_FILE);
    litFile(result) = file;
    fileIsOpen(result) = true;
    DEBUG(checkExprRep(result);)
    return result;
}

Expr makeSymbol(Symbol symbol)
{
    Expr result = makeExpr(EXP_SYMBOL);
    exprSymbol(result) = symbol;
    DEBUG(checkExprRep(result);)
    return result;
}

Expr makeVariable(Symbol var_name, int restriction)
{
    Expr result = makeExpr(EXP_VAR);
    varName(result) = var_name;
    varRestriction(result) = restriction;
    DEBUG(checkExprRep(result);)
    return result;
}

Expr makeApp(Rator rator, unsigned num_rands, Expr* rands)
{
    Expr result = makeExpr(EXP_APP);
    appRator(result) = ref(rator);
    numRands(result) = num_rands;
    appRands(result) = rands;
    DEBUG(checkExprRep(result);)
    return result;
}

Expr makeApp1(Rator rator, Expr rand)
{
    Expr* rands = allotRands(1);
    rands[0] = ref(rand);
    return makeApp(rator, 1, rands);
}

Expr makeApp2(Rator rator, Expr rand1, Expr rand2)
{
    Expr* rands = allotRands(2);
    rands[0] = ref(rand1);
    rands[1] = ref(rand2);
    return makeApp(rator, 2, rands);
}

Expr addRand(Expr app, Expr rand)
{
    unsigned i, N;
    Expr* rands;
    assert(type(app) == EXP_APP);
    N = numRands(app);
    rands = allotRands(N+1);
    for (i = 0; i < N; ++i)
        rands[i] = ref(nthRand(app, i));
    rands[N] = ref(rand);
    return makeApp(appRator(app), N+1, rands);
}

static int infixPrecedence(OpInfo op)
{
    int l = leftPrecedence(op);
    int r = rightPrecedence(op);
    return l < r ? l : r;
}

static void _fprintExpr(Expr expr, FILE* file, char* string_format, int prec)
{
    DEBUG(checkExprRep(expr);)
    switch (type(expr)) {
        case EXP_NUMBER: 
            fprintf(file, "%.10g", (double) litNumber(expr)); break;
        case EXP_STRING: 
            fprintf(file, string_format, String2pchar(litString(expr))); break;
        case EXP_FILE:   
            fprintf(file, "[file]"); break;
        case EXP_SYMBOL: 
            fprintf(file, "%s", symbolName(exprSymbol(expr))); break;
        case EXP_VAR: {
            static char* restrics[] = {
                "number", "string", "file", "symbol", "var", "app"
            };
            fprintf(file, "?%s", symbolName(varName(expr))); 
            if (varRestriction(expr) != NO_RESTRICTION)
                fprintf(file, "?%s", restrics[varRestriction(expr)]);
            break;
        }
        case EXP_APP: {
            unsigned i;
	    Expr rator = appRator(expr);
	    OpInfo *op = type(rator) == EXP_SYMBOL 
	                 ? symbolOpInfo(exprSymbol(rator))
	                 : NULL;
	    if (op && 0 < infixPrecedence(*op) && numRands(expr) == 2) {
	        int in_prec = infixPrecedence(*op);
		if (in_prec < prec)
		    fprintf(file, "(");
		_fprintExpr(appRands(expr)[0], file, string_format, 
			    leftPrecedence(*op));
		fprintf(file, " %s ", symbolName(exprSymbol(rator)));
		_fprintExpr(appRands(expr)[1], file, string_format,
			    rightPrecedence(*op));
		if (in_prec < prec)
		    fprintf(file, ")");
	    } else if (op && 0 < prefixPrecedence(*op) && numRands(expr) == 1) {
	        int pre_prec = prefixPrecedence(*op);
		if (pre_prec < prec)
		    fprintf(file, "(");
		fprintf(file, "%s ", symbolName(exprSymbol(rator)));
		_fprintExpr(appRands(expr)[0], file, string_format, pre_prec);
		if (pre_prec < prec)
		    fprintf(file, ")");
	    } else if (op && 0 < postfixPrecedence(*op) && numRands(expr)==1) {
	        int post_prec = postfixPrecedence(*op);
		if (post_prec < prec)
		    fprintf(file, "(");
		_fprintExpr(appRands(expr)[0], file, string_format, post_prec);
		fprintf(file, " %s", symbolName(exprSymbol(rator)));
		if (post_prec < prec)
		    fprintf(file, ")");
	    } else {
	        _fprintExpr(appRator(expr), file, string_format, 10000);
		fprintf(file, "(");
		for (i = 0; i < numRands(expr); ++i) {
		    if (i != 0) fprintf(file, ", ");
		    _fprintExpr(nthRand(expr, i), file, string_format, 0);
		}
		fprintf(file, ")");
	    }
	    break;
        }
        default: UNKNOWN_TYPE;
    }
}

void fprintExpr(Expr expr, FILE* file)
{
    _fprintExpr(expr, file, "'%s'", 0);
}

void fdisplayExpr(Expr expr, FILE* file)
{
    _fprintExpr(expr, file, "%s", 0);
}

void printlnExpr(Expr expr)
{
    printExpr(expr);
    printf("\n");
}

Flag exprIsTrue(Expr expr)
{
    DEBUG(checkExprRep(expr);)
    return type(expr) == EXP_NUMBER && litNumber(expr) == 1;
}

Flag exprIsFalse(Expr expr)
{
    DEBUG(checkExprRep(expr);)
    return type(expr) == EXP_NUMBER && litNumber(expr) == 0;
}

Flag exprEqual(Expr exp1, Expr exp2)
{
    if (type(exp1) != type(exp2)) return false;
    switch (type(exp1)) {
        case EXP_NUMBER: return litNumber(exp1) == litNumber(exp2);
        case EXP_STRING: return stringEqual(litString(exp1), litString(exp2));
        case EXP_FILE:	 return litFile(exp1) == litFile(exp2);
        case EXP_SYMBOL: return exprSymbol(exp1) == exprSymbol(exp2);
        case EXP_VAR:	 return varName(exp1) == varName(exp2)
                            && varRestriction(exp1) == varRestriction(exp2);
        case EXP_APP: {
            unsigned i, N;
            if (numRands(exp1) != numRands(exp2)) return false;
            if (!ratorEqual(appRator(exp1), appRator(exp2))) return false;
            N = numRands(exp1);
            for (i = 0; i < N; ++i)
                if (!exprEqual(nthRand(exp1, i), nthRand(exp2, i)))
                    return false;
            return true;
        }
        default: UNKNOWN_TYPE; return false;
    }
}

