#include "req.h"

static Rule* non_indexed_rules = NULL;

#define isIndexible(expr) \
    ( (type(expr) == EXP_APP && type(appRator(expr)) == EXP_SYMBOL) \
     || type(expr) == EXP_SYMBOL )
#define indexedRules(expr) \
    ( type(expr) == EXP_APP ? exprSymbol(appRator(expr))->rules : exprSymbol(expr)->rules )
    
void installRule(Expr pattern, Expr subst)
{
    Rule* new_rule = allot(sizeof(Rule));
    new_rule->pattern = ref(pattern);
    new_rule->subst = ref(subst);
    if (type(pattern) == EXP_APP && type(appRator(pattern)) == EXP_SYMBOL) {
        new_rule->next = exprSymbol(appRator(pattern))->rules;
        exprSymbol(appRator(pattern))->rules = new_rule;
    } else if (type(pattern) == EXP_SYMBOL) {
        new_rule->next = exprSymbol(pattern)->rules;
        exprSymbol(pattern)->rules = new_rule;
    } else {
        new_rule->next = non_indexed_rules;
        non_indexed_rules = new_rule;
    }
}

/* --- The environment --- */

typedef struct {
    Symbol variable;
    Expr value;
} Binding;

#define MAX_BINDINGS 100

typedef unsigned Env;

static Env env;
static Binding bindings[MAX_BINDINGS];

static void bind(Symbol variable, Expr value)
{
    if (env == MAX_BINDINGS)
        error("Out of environment space");
    bindings[env].variable = variable;
    bindings[env].value = ref(value);
    ++env;
}

#define saveEnv()	env

static void restoreEnv(Env old_env)
{
    for (; env != old_env; --env)
        deref(bindings[env-1].value);
}

static Expr envLookup(Symbol variable)
{
    unsigned i;
    for (i = env; i != 0; --i)
        if (bindings[i-1].variable == variable)
            return ref(bindings[i-1].value);
    return theNullExpr;
}

/* --- Matching --- */

/* Returns expr identical to pattern except that variables bound in env are */
/* replaced with their values. */
static Expr instantiate(Expr pattern)
{
    switch (type(pattern)) {
        case EXP_NUMBER: 
        case EXP_STRING:
        case EXP_FILE:
        case EXP_SYMBOL: return ref(pattern);
        case EXP_VAR: {
            Expr result = envLookup(varName(pattern));
            if (!isNull(result))
                return result;
/*	    error("Unbound variable - ?%s", symbolName(varName(pattern))); */
            return ref(pattern);
        }
        case EXP_APP: {
            unsigned N = numRands(pattern);
            Expr* rands = allotRands(N);
            Rator rator = instantiate(appRator(pattern));
            Expr result;
            unsigned i;
            for (i = 0; i < N; ++i)
                rands[i] = instantiate(nthRand(pattern, i));
            result = makeApp(rator, N, rands);
            derefRator(rator);
            return result;
        }
        default: UNKNOWN_TYPE; return theNullExpr;
    }
}

/* Post: returns true and env is extended so that instantiate(pattern) = datum */
/*    or returns false and no such extension is possible without violating  */
/*       variable restrictions (and env is left alone). */
/* We leave out the EXP_FILE case because it can't occur in any pattern the */
/* user types in. */
static Flag match(Expr pattern, Expr datum)
{
    switch (type(pattern)) {
        case EXP_NUMBER: 
            return type(datum) == EXP_NUMBER && 
                   litNumber(pattern) == litNumber(datum);
        case EXP_STRING:
            return type(datum) == EXP_STRING &&
                   stringEqual(litString(pattern), litString(datum));
        case EXP_SYMBOL:
            return type(datum) == EXP_SYMBOL &&
                   exprSymbol(pattern) == exprSymbol(datum);
        case EXP_VAR: {
            Expr value = envLookup(varName(pattern));
            if (!isNull(value)) {
                Flag result = exprEqual(value, datum);
                deref(value);
                return result;
            } else if (varRestriction(pattern) == NO_RESTRICTION 
                    || varRestriction(pattern) == type(datum)) {
                bind(varName(pattern), datum);
                return true;
            } else
                return false;
        }
        case EXP_APP:
            if (type(datum) != EXP_APP || numRands(pattern) != numRands(datum))
                return false;
            else {
                unsigned i, N = numRands(pattern);
                Env saved_env = saveEnv();
                if (!match(appRator(pattern), appRator(datum)))
                    return false;
                for (i = 0; i < N; ++i)
                    if (!match(nthRand(pattern, i), nthRand(datum, i))) {
                        restoreEnv(saved_env);
                        return false;
                    }
                return true;
            }
        default: UNKNOWN_TYPE; return false;
    }
}

/* --- Simplification --- */

/* This might be a good place to slip in the kbhit() check, too: */
#define trace(expr)	do { if (tracing) printlnExpr(expr); } while (0)

/* If expr is not a redex, return theNullExpr. */
/* If it is, perform the reduction and return the result. */
static Expr reduce(Expr expr)
{
    {						/* try the rule base */
        Env saved_env = saveEnv();
        if (isIndexible(expr)) {
            Rule* r = indexedRules(expr);
            for (; r; r = r->next)
                if (match(r->pattern, expr)) {
                    Expr result = instantiate(r->subst);
                    trace(result);
                    restoreEnv(saved_env);
                    return result;
                }
        }
        {
            Rule* r = non_indexed_rules;
            for (; r; r = r->next)
                if (match(r->pattern, expr)) {
                    Expr result = instantiate(r->subst);
                    trace(result);
                    restoreEnv(saved_env);
                    return result;
                }
        }
    }
    /* try a primitive reducer */
    if (type(expr) == EXP_APP && type(appRator(expr)) == EXP_SYMBOL) {
        Reducer* r = primitiveReducer(exprSymbol(appRator(expr)));
        if (r)
            return (*r)(expr);	/* note this doesn't get traced... */
    }
    return theNullExpr;
}

/* Special forms - if, where, begin */

static Expr fullyReduce(Expr expr);

/* Syntax of if: if(then(<predicate>, else(<consequent>, <alternative>))) */
static Rator if_rator, then_rator, else_rator;

/* Reduce <predicate>; if true, return <consequent>;  */
/* if false, return <alternative>;  */
/* otherwise, expression is not further reducible. */
static Expr reduceIf(Expr expr)
{
    if (numRands(expr) != 1) 
        return theNullExpr;
    else {
        Expr then_expr = nthRand(expr, 0);
        if (type(then_expr) != EXP_APP || 
            !ratorEqual(appRator(then_expr), then_rator) ||
            numRands(then_expr) != 2)
            return theNullExpr;
        else {
            Expr else_expr = nthRand(then_expr, 1);
            if (type(else_expr) != EXP_APP ||
                !ratorEqual(appRator(else_expr), else_rator) ||
                numRands(else_expr) != 2)
                return theNullExpr;
            else {
                Expr pred = nthRand(then_expr, 0);
                Expr reduced_pred = fullyReduce(pred);
                Flag changed = !isNull(reduced_pred);
                Expr result;
                {
                    Expr p = changed ? reduced_pred : pred;
                    if (exprIsTrue(p))
                        result = ref(nthRand(else_expr, 0));
                    else if (exprIsFalse(p))
                        result = ref(nthRand(else_expr, 1));
                    else if (!changed)
                        return theNullExpr;
                    else
                        result = makeApp1(if_rator, 
                                   makeApp2(then_rator, p, else_expr));
                    trace(result);
                }
                if (changed) deref(reduced_pred);
                return result;
            }
        }
    }
}

/* Syntax of where: with(<body>, ->(<pattern>, <datum>)) */
static Rator where_rator, bind_rator;

/* Instantiate into <body>  */
/* the bindings of <pattern> matched to the value of <datum> */
static Expr reduceWhere(Expr expr)
{
    Expr binding;
    if (numRands(expr) != 2) return theNullExpr;
    binding = nthRand(expr, 1);
    if (type(binding) != EXP_APP 
      || !ratorEqual(appRator(binding), bind_rator) || numRands(binding) != 2)
        return theNullExpr;
    {
        Env saved_env = saveEnv();
        Expr binding_value = simplify(nthRand(binding, 1));
        if (!match(nthRand(binding, 0), binding_value)) {
            deref(binding_value);  /* ought to build reduced where expr...? */
            return theNullExpr;
        }
        {
            Expr result = instantiate(nthRand(expr, 0));
            restoreEnv(saved_env);
            deref(binding_value);
            return result;
        }
    }
}

static Rator begin_rator;
static Expr ok_symbol;

/* Reduce each operand in order from left to right, with the last operand */
/* yielding the value of the whole expression. */
static Expr reduceBegin(Expr expr)
{
    if (numRands(expr) == 0)
        return ref(ok_symbol);
    else {
        unsigned i, N = numRands(expr);
        for (i = 0; i < N-1; ++i)
            deref(simplify(nthRand(expr, i)));
        return ref(nthRand(expr, N-1));
    }
}

static Rator quote_rator;

/* Perform applicative-order reduction of expr to its normal form. */
static Expr fullyReduce(Expr expr)
{
    Flag same = true;
    if (expr->fully_reduced) return theNullExpr;
    ref(expr);
    for (;;) {
        if (type(expr) == EXP_APP) {
            if (type(appRator(expr)) == EXP_SYMBOL) {
                Rator rator = appRator(expr);
                if (ratorEqual(rator, if_rator)) {
                    Expr one_step_result = reduceIf(expr);
                    if (!isNull(one_step_result)) {
                        deref(expr);
                        expr = one_step_result;
                        same = false;
                        continue;
                    }
                } else if (ratorEqual(rator, where_rator)) {
                    Expr one_step_result = reduceWhere(expr);
                    if (!isNull(one_step_result)) {
                        deref(expr);
                        expr = one_step_result;
                        same = false;
                        continue;
                    }
                } else if (ratorEqual(rator, begin_rator)) {
                    Expr one_step_result = reduceBegin(expr);
                    if (!isNull(one_step_result)) {
                        deref(expr);
                        expr = one_step_result;
                        same = false;
                        continue;
                    }
                } else if (ratorEqual(rator, quote_rator) && numRands(expr) == 1) {
                    Expr result = ref(nthRand(expr, 0));
                    deref(expr);
                    result->fully_reduced = true;
                    return result;
                }
            }
            {				/* try to reduce rator & rands */
                Flag same_rands = true;
                unsigned i, N = numRands(expr);
                Expr* rands = allotRands(N);
                for (i = 0; i < N; ++i) {
                    rands[i] = fullyReduce(nthRand(expr, i));
                    if (isNull(rands[i]))
                        rands[i] = ref(nthRand(expr, i));
                    else
                        same_rands = false;
                }
                {
                    Rator rator = fullyReduce(appRator(expr));
                    if (isNull(rator)) {
                        if (!same_rands) {
                            Expr one_step_result = 
                              makeApp(appRator(expr), N, rands);
                            trace(one_step_result);
                            deref(expr);
                            expr = one_step_result;
                            same = false;
                            continue;
                        } else
                            freeRands(N, rands);
                    } else {
                        Expr one_step_result = makeApp(rator, N, rands);
                        derefRator(rator);
                        trace(one_step_result);
                        deref(expr);
                        expr = one_step_result;
                        same = false;
                        continue;
                    }
                }
            }
        }
        {				/* reduce expr if it is a redex */
            Expr one_step_result = reduce(expr);
            if (isNull(one_step_result))
                break;
            else {
                deref(expr);
                expr = one_step_result;
                same = false;
                continue;
            }
        }
    }
    expr->fully_reduced = true;
    if (!same)
        return expr;
    else {
        deref(expr);
        return theNullExpr;
    }
}

Expr simplify(Expr expr)
{
    Expr result = fullyReduce(expr);
    return isNull(result) ? ref(expr) : result;
}

void setupRules(void)
{
    if_rator = Symbol2Rator(name2Symbol("if"));
    then_rator = Symbol2Rator(name2Symbol("then"));
    else_rator = Symbol2Rator(name2Symbol("else"));
    
    where_rator = Symbol2Rator(name2Symbol("with"));
    bind_rator = Symbol2Rator(name2Symbol("->"));
    
    begin_rator = Symbol2Rator(name2Symbol("begin"));
    
    quote_rator = Symbol2Rator(name2Symbol("quote"));
    
    ok_symbol = makeSymbol(name2Symbol("ok"));
}

