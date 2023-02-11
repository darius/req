#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "req.h"

/* --- List primitives --- */

static Symbol nil;
static Rator cons, append_rator;
static Expr L2;		/* List to append */

static Expr append(Expr L1)
{
    if (type(L1) == EXP_SYMBOL && exprSymbol(L1) == nil) {
        return ref(L2);
    } else if (type(L1) == EXP_APP 
             && ratorEqual(appRator(L1), cons)
             && numRands(L1) == 2) {
        Expr rest = append(nthRand(L1, 1));
        if (isNull(rest))
            return makeApp2(cons, nthRand(L1, 0),
                                  makeApp2(append_rator, nthRand(L1, 1), L2));
        else {
            Expr result = makeApp2(cons, nthRand(L1, 0), rest);
            deref(rest);
            return result;
        }
    } else
        return theNullExpr;
}

static Expr prim_append(Expr expr)
{
    if (numRands(expr) != 2) return theNullExpr;
    L2 = nthRand(expr, 1);
    return append(nthRand(expr, 0));
}

/* --- String primitives --- */

static Expr prim_sub(Expr expr)
{
    if (numRands(expr) != 2) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_STRING) return theNullExpr;
    if (type(nthRand(expr, 1)) != EXP_NUMBER) return theNullExpr;
    {
        const char* string = litString(nthRand(expr, 0));
        const Number index = litNumber(nthRand(expr, 1));
        const size_t i = (size_t) index;
        if (i != index) return theNullExpr;
        if (stringLength(string) <= i) return theNullExpr;
        {
            char* result = allotString(1);
            result[0] = string[i];
            result[1] = '\0';
            return makeString(result);
        }
    }
}

static Expr prim_length(Expr expr)
{
    if (numRands(expr) != 1) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_STRING) return theNullExpr;
    return makeNumber(stringLength(litString(nthRand(expr, 0))));
}

static Expr prim_stringAppend(Expr expr)
{
    Expr rand0, rand1;
    if (numRands(expr) != 2) return theNullExpr;
    if (type(rand0 = nthRand(expr, 0)) != EXP_STRING) return theNullExpr;
    if (type(rand1 = nthRand(expr, 1)) != EXP_STRING) return theNullExpr;
    return makeString(stringAppend(litString(rand0), litString(rand1)));
}

static Expr prim_number2string(Expr expr)
{
    if (numRands(expr) != 1) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_NUMBER) return theNullExpr;
    return makeString(number2String(litNumber(nthRand(expr, 0))));
}

static Expr prim_symbol2string(Expr expr)
{
    if (numRands(expr) != 1) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_SYMBOL) return theNullExpr;
    return makeString(pchar2String(symbolName(exprSymbol(nthRand(expr, 0)))));
}

static Expr prim_translit(Expr expr)
{
    if (numRands(expr) != 3) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_STRING) return theNullExpr;
    if (type(nthRand(expr, 1)) != EXP_STRING) return theNullExpr;
    if (type(nthRand(expr, 2)) != EXP_STRING) return theNullExpr;
    {
        const char* from = litString(nthRand(expr, 0));
        const char* to   = litString(nthRand(expr, 1));
        const size_t from_length = stringLength(from);
        const size_t to_length = stringLength(to);
        if (from_length != to_length)
            return theNullExpr;
        else {
            const char* data = litString(nthRand(expr, 2));
            char* result = allotString(stringLength(data));
            unsigned i;
            for (i = 0; data[i]; ++i) {
                const char* lookup = strchr(from, data[i]);
                result[i] = lookup ? to[lookup - from] : data[i];
            }
            result[i] = '\0';
            return makeString(result);
        }
    }
}

/* --- Variable stuff --- */

static Expr prim_varName(Expr expr)
{
    if (numRands(expr) != 1 || type(nthRand(expr, 0)) != EXP_VAR)
        return theNullExpr;
    return makeSymbol(varName(nthRand(expr, 0)));
}

static Expr none_symbol;

static Expr prim_varRestric(Expr expr)
{
    if (numRands(expr) != 1 || type(nthRand(expr, 0)) != EXP_VAR)
        return theNullExpr;
    return varRestriction(nthRand(expr, 0)) == NO_RESTRICTION
            ? ref(none_symbol)
            : makeSymbol(RestricNames[varRestriction(nthRand(expr, 0))]);
}

/* --- Misc side-effecting primitives --- */

static Expr tally(Expr expr)
{
    static unsigned long counter = 0;
    if (numRands(expr) != 0) return theNullExpr;
    return makeNumber((Number)(counter++));
}

static Expr prim_error(Expr expr)
{
    fprintf(stderr, "\n");
    fprintExpr(expr, stderr);
    exit(1);
}

static Expr prim_quit(Expr expr)
{
    if (numRands(expr) != 0) return theNullExpr;
    exit(0);
}

static Expr prim_system(Expr expr)
{
    if (numRands(expr) != 1) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_STRING) return theNullExpr;
    return makeNumber(system(litString(nthRand(expr, 0))));
}

/* --- Numeric primitives --- */

static Flag randsAreNumbers(Expr expr)
{
    unsigned i, N = numRands(expr);
    for (i = 0; i < N; ++i)
        if (type(nthRand(expr, i)) != EXP_NUMBER)
            return false;
    return true;
}

#define isTrue(number)		( (number) != 0 )

/* Change these logical ops to use exprIsTrue, exprIsFalse ? */
/* Could also make 'em more efficient in practice making 'em strictly binary. */
static Expr or(Expr expr)
{
    if (!randsAreNumbers(expr)) return theNullExpr;
    {
        unsigned i, N = numRands(expr);
        Flag result = false;
        for (i = 0; i < N; ++i)
            result |= isTrue(litNumber(nthRand(expr, i)));
        return makeNumber(result);
    }
}

static Expr and(Expr expr)
{
    if (!randsAreNumbers(expr)) return theNullExpr;
    {
        unsigned i, N = numRands(expr);
        Flag result = true;
        for (i = 0; i < N; ++i)
            result &= isTrue(litNumber(nthRand(expr, i)));
        return makeNumber(result);
    }
}

static Expr not(Expr expr)
{
    if (numRands(expr) != 1) return theNullExpr;
    {
        Expr rand = nthRand(expr, 0);
        if (type(rand) != EXP_NUMBER) return theNullExpr;
        return makeNumber(!isTrue(litNumber(rand)));
    }
}

enum ComparisonType { LT, LE, GE, GT };

#define makeFlag(n) makeNumber(n)

static Expr compare(Expr expr, enum ComparisonType cmp)
{
    Flag result;
    if (numRands(expr) != 2) return theNullExpr;
    if (type(nthRand(expr, 0)) != type(nthRand(expr, 1))) return theNullExpr;
    switch (type(nthRand(expr, 0))) {
        case EXP_NUMBER: {
            Number v1 = litNumber(nthRand(expr, 0));
            Number v2 = litNumber(nthRand(expr, 1));
            switch (cmp) {
                case LT: result = v1 < v2;  break;
                case LE: result = v1 <= v2; break;
                case GE: result = v1 >= v2; break;
                case GT: result = v1 > v2;  break;
                default: NOT_REACHED;
            }
            break;
        }
        case EXP_STRING: {
            int diff = stringCompare(litString(nthRand(expr, 0)),
                                     litString(nthRand(expr, 1)));
            switch (cmp) {
                case LT: result = diff < 0;  break;
                case LE: result = diff <= 0; break;
                case GE: result = diff >= 0; break;
                case GT: result = diff > 0;  break;
                default: NOT_REACHED;
            }
            break;
        }
        default: return theNullExpr;
    }
    return makeFlag(result);
}

static Expr less(Expr expr)		{ return compare(expr, LT); }
static Expr lessOrEq(Expr expr)		{ return compare(expr, LE); }
static Expr greaterOrEq(Expr expr)	{ return compare(expr, GE); }
static Expr greater(Expr expr)		{ return compare(expr, GT); }

static Expr equal(Expr expr)
{
    if (numRands(expr) != 2) return theNullExpr;
    return makeFlag(exprEqual(nthRand(expr, 0), nthRand(expr, 1)));
}

static Expr notEqual(Expr expr)
{
    if (numRands(expr) != 2) return theNullExpr;
    return makeFlag(!exprEqual(nthRand(expr, 0), nthRand(expr, 1)));
}

/* Pointer equality test. */
static Expr prim_eq(Expr expr)
{
    if (numRands(expr) != 2) return theNullExpr;
    return makeFlag(nthRand(expr, 0) == nthRand(expr, 1));
}

static Flag isInteger(Number n)		{ return n == (long)n; }

/* Binary arithmetic operations */

enum ArithOp { ADD, SUB, MUL, DIV, IDIV, MOD, POW };

static Expr arith(Expr expr, enum ArithOp op)
{
    if (!randsAreNumbers(expr)) return theNullExpr;
    if (numRands(expr) != 2) return theNullExpr;
    {
        Number v1 = litNumber(nthRand(expr, 0));
        Number v2 = litNumber(nthRand(expr, 1));
        Number result;
        switch (op) {
            case ADD: result = v1 + v2; break;
            case SUB: result = v1 - v2; break;
            case MUL: result = v1 * v2; break;
            case DIV: if (v2 == 0) return theNullExpr;
                      result = v1 / v2; break;
            case IDIV:
                if (!isInteger(v1) || !isInteger(v2)) return theNullExpr;
                if (v2 == 0) return theNullExpr;
                result = (long)v1 / (long)v2;
                break;
            case MOD:
                if (!isInteger(v1) || !isInteger(v2)) return theNullExpr;
                if (v2 == 0) return theNullExpr;
                result = (long)v1 % (long)v2;
                break;
            case POW: 
                if (v1 < 0 && v2 != (long)v2) return theNullExpr;
                result = pow(v1, v2); 
                break;
            default: NOT_REACHED;
        }
        return makeNumber(result);
    }
}

static Expr add(Expr expr)		{ return arith(expr, ADD); }
static Expr subtract(Expr expr)		{ return arith(expr, SUB); }
static Expr multiply(Expr expr)		{ return arith(expr, MUL); }
static Expr divide(Expr expr)		{ return arith(expr, DIV); }
static Expr int_divide(Expr expr)	{ return arith(expr, IDIV); }
static Expr _remainder(Expr expr)	{ return arith(expr, MOD); }
static Expr power(Expr expr)		{ return arith(expr, POW); }

static Expr negate(Expr expr)
{
    if (!randsAreNumbers(expr)) return theNullExpr;
    if (numRands(expr) != 1) return theNullExpr;
    return makeNumber(-litNumber(nthRand(expr, 0)));
}

/* --- Random numbers --- */

static Expr ok_symbol;

static unsigned long seed = 0;

static Expr prim_random(Expr expr)
{
    const double scale = 4294967296.0;	/* = 2^32 */
    if (numRands(expr) != 0) return theNullExpr;
    seed = 1664525 * seed + 1013904223;
    return makeNumber(seed / scale);
}

static Expr prim_randomize(Expr expr)
{
    if (!randsAreNumbers(expr)) return theNullExpr;
    if (numRands(expr) != 1) return theNullExpr;
    seed = (unsigned long) litNumber(nthRand(expr, 0));
    return ok_symbol;
}

/* --- Math functions from math.h --- */

static Expr math(Expr expr, Number (*f)(Number))
{
    if (numRands(expr) != 1) return theNullExpr;
    if (type(nthRand(expr, 0)) != EXP_NUMBER) return theNullExpr;
    {
        Number result = (*f)(litNumber(nthRand(expr, 0)));
	/* here we might check for NaN... */
        return makeNumber(result);
    }
}

static Expr prim_atan(Expr expr)	{ return math(expr, atan);	}
static Expr prim_floor(Expr expr)	{ return math(expr, floor);	}
static Expr prim_ceiling(Expr expr)	{ return math(expr, ceil);	}
static Expr prim_abs(Expr expr)		{ return math(expr, fabs);	}
static Expr prim_sqrt(Expr expr)	{ return math(expr, sqrt);	}
static Expr prim_sin(Expr expr)		{ return math(expr, sin);	}
static Expr prim_cos(Expr expr)		{ return math(expr, cos);	}
static Expr prim_tan(Expr expr)		{ return math(expr, tan);	}
static Expr prim_asin(Expr expr)	{ return math(expr, asin);	}
static Expr prim_acos(Expr expr)	{ return math(expr, acos);	}
static Expr prim_exp(Expr expr)		{ return math(expr, exp);	}
static Expr prim_log(Expr expr)		{ return math(expr, log);	}
static Expr prim_log10(Expr expr)	{ return math(expr, log10);	}

/* --- I/O --- */

static Expr failed_symbol;

static Expr prim_write(Expr expr)
{
    FILE* file;
    if (numRands(expr) == 2 && type(nthRand(expr, 1)) == EXP_FILE)
        file = litFile(nthRand(expr, 1)); /* note we don't check if it's open*/
    else if (numRands(expr) == 1) 
        file = stdout;
    else
        return theNullExpr;
    fprintExpr(nthRand(expr, 0), file);
    return ref(ok_symbol);
}

static Expr prim_display(Expr expr)
{
    FILE* file;
    if (numRands(expr) == 2 && type(nthRand(expr, 1)) == EXP_FILE)
        file = litFile(nthRand(expr, 1));
    else if (numRands(expr) == 1) 
        file = stdout;
    else
        return theNullExpr;
    fdisplayExpr(nthRand(expr, 0), file);
    return ref(ok_symbol);
}

static Expr prim_fileOpen(Expr expr)
{
    if (numRands(expr) != 2 
      || type(nthRand(expr, 0)) != EXP_STRING
      || type(nthRand(expr, 1)) != EXP_STRING)
        return theNullExpr;
    {
        FILE* file = fopen(String2pchar(litString(nthRand(expr, 0))), 
                           String2pchar(litString(nthRand(expr, 1))));
        return file ? makeFile(file) : ref(failed_symbol);
    }
}

static Expr prim_fileClose(Expr expr)
{
    if (numRands(expr) != 1 || type(nthRand(expr, 0)) != EXP_FILE)
        return theNullExpr;
    fclose(litFile(nthRand(expr, 0)));
    fileIsOpen(expr) = false;
    return ref(ok_symbol);
}

/* --- Syntax primitives --- */

static Expr installOpInfo(Expr expr, OpInfo* (*constructor)(int))
{
    if (numRands(expr) != 2
      || type(nthRand(expr, 0)) != EXP_SYMBOL
      || type(nthRand(expr, 1)) != EXP_NUMBER)
        return theNullExpr;
    symbolOpInfo(exprSymbol(nthRand(expr, 0))) = 
      (*constructor)((int)litNumber(nthRand(expr, 1)));
    return ref(ok_symbol);
}

static Expr prefixOp(Expr expr)
{ return installOpInfo(expr, makePrefixOpInfo);	}

static Expr postfixOp(Expr expr)
{ return installOpInfo(expr, makePostfixOpInfo); }

static Expr infixOp(Expr expr)
{ return installOpInfo(expr, makeInfixOpInfo); }

static Expr infixRLOp(Expr expr)
{ return installOpInfo(expr, makeInfixRLOpInfo); }

/* --- Primitive table --- */

static const struct {
    char* name;
    Reducer* reducer;
} PrimitiveTable[] = {
    { "declarePrefix", prefixOp },
    { "declarePostfix", postfixOp },
    { "declareInfix", infixOp },
    { "declareInfixRL", infixRLOp },
/*      { "prefixPrecedence", prim_prefixPrec }, */
/*	{ "postfixPrecedence", prim_postfixPrec }, */
/*	{ "infixPrecedence", prim_infixPrec }, */
/*	{ "associativity", prim_associativity }, */
    { "varName", prim_varName },
    { "varRestric", prim_varRestric },
    { "or", or },
    { "and", and },
    { "not", not },
    { "<", less },
    { "<=", lessOrEq },
    { "=", equal },
    { "!=", notEqual },
    { ">=", greaterOrEq },
    { ">", greater },
    { "eq", prim_eq },
    { "+", add },
    { "-", subtract },
    { "~", negate },
    { "*", multiply },
    { "/", divide },
    { "div", int_divide },
    { "mod", _remainder },
    { "^", power },
    { "random", prim_random },
    { "randomize", prim_randomize },
    { "arctan", prim_atan },
    { "floor", prim_floor },
    { "ceiling", prim_ceiling },
    { "abs", prim_abs },
    { "sqrt", prim_sqrt },
    { "sin", prim_sin },
    { "cos", prim_cos },
    { "tan", prim_tan },
    { "arcsin", prim_asin },
    { "arccos", prim_acos },
    { "exp", prim_exp },
    { "log", prim_log },
    { "log10", prim_log10 },
    { "sub", prim_sub },
    { "length", prim_length },
    { "&", prim_stringAppend },
    { "number2string", prim_number2string },
    { "symbol2string", prim_symbol2string },
    { "translit", prim_translit },
    { "append", prim_append },
    { "tally", tally },
    { "error", prim_error },
    { "fileOpen", prim_fileOpen },
    { "fileClose", prim_fileClose },
    { "write", prim_write },
    { "display", prim_display },
    { "system", prim_system },
    { "quit", prim_quit }
};

void setupPrimitives(void)
{
    unsigned i;
    for (i = 0; i < sizeof(PrimitiveTable)/sizeof(*PrimitiveTable); ++i)
        name2Symbol(PrimitiveTable[i].name)->primitive_reducer = 
            PrimitiveTable[i].reducer;

    nil = name2Symbol("nil");
    cons = Symbol2Rator(name2Symbol("::"));
    append_rator = Symbol2Rator(name2Symbol("append"));
    ok_symbol = makeSymbol(name2Symbol("ok"));
    failed_symbol = makeSymbol(name2Symbol("failed"));
    none_symbol = makeSymbol(name2Symbol("none"));

    installRule(makeSymbol(name2Symbol("newline")), 
                makeString(pchar2String("\n")));
}

