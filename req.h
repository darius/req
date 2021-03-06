#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* #define GRAPHICS */
/* #define debug */
/* #include "bug.h"		// debugging macros */
#define DEBUG(x)

/* Report an error and abort. */
void error(const char* format, ...);

/* Report an error generated by a standard-library procedure, and abort. */
void stdError(const char* irritant);

typedef enum { false, true } Flag;

#define NOT_REACHED		assert(false)

/* --- Data values --- */

typedef double Number;

/* A String is an immutable string of chars. */
/* Alas, I can't define it as const char* because of freeString. */
typedef char* String;

#define allotString(size)	allot((size)+1)
#define freeString(string)	free(string)

#define String2pchar(string)	( (const char*)(string) )
String pchar2String(const char*);

String number2String(Number n);
String stringAppend(const String, const String);
#define stringEqual(s1, s2)	( !strcmp((s1), (s2)) )
#define stringCompare(s1, s2)	strcmp((s1), (s2))
#define stringLength(s)		strlen(s)

/* --- Rules --- */
/* There are 2 kinds: primitives and user-defined substitution rules. */

/* A substitution rule: if a subexpression of an Expr matches pattern, we */
/* call that subexpression a redex. We may replace it by subst with bound */
/* variables replaced by their bindings from the match. */
typedef struct Rule {
    struct Rule * next;			/* used for lists of rules */
    struct Expr *pattern, *subst;
} Rule;

/* A procedure that embodies a primitive reduction rule; call it delta. */
/* If expr is a delta-redex, return the result of the reduction; */
/* else return theNullExpr. */
typedef struct Expr * Reducer(struct Expr * expr);

/* --- Syntax info --- */
/* We'll be handling this differently soon... */

typedef struct {
    int postprec;			/* postfix precedence */
    int prefprec;			/* prefix precedence  */
    int lprec, rprec;			/* left and right infix precedences */
} OpInfo;

#define postfixPrecedence(opinfo)	( (opinfo).postprec )
#define prefixPrecedence(opinfo)	( (opinfo).prefprec )
#define leftPrecedence(opinfo)		( (opinfo).lprec )
#define rightPrecedence(opinfo)		( (opinfo).rprec )

extern OpInfo NonOperatorInfo;		/* syntax info for non-operators */

OpInfo* makePrefixOpInfo(int);
OpInfo* makePostfixOpInfo(int);
OpInfo* makeInfixOpInfo(int);
OpInfo* makeInfixRLOpInfo(int);		/* right-to-left associativity */

/* --- Symbols --- */
/* *** Um, actually they aren't that much like strings... */
/* Unique names. They behave like strings, except they can be compared by */
/* pointer equality, and they have associated data on how to parse lines that */
/* contain them (e.g. the symbol '+' has syntax info that enables parsing of */
/* '2+2' into the Expr +(2,2) ) and on how to reduce Expr's involving them */
/* (e.g. '+' has a primitive_reducer that reduces +(2,2) to 4). */

typedef struct Symbol {
    struct Symbol *next;		/* next in hash bucket */
    OpInfo* opinfo;			/* syntax data */
    Reducer* primitive_reducer; 	/* reduction rule for apps whose rator is this symbol; or NULL */
    Rule* rules;			/* user-defined rules indexed under this symbol */
    char name[32];			/* name */
} *Symbol;

#define symbolName(symbol)		( (symbol)->name )
#define primitiveReducer(symbol) 	( (symbol)->primitive_reducer )
#define symbolOpInfo(symbol)		( (symbol)->opinfo )

/* Allot space for a new symbol. */
#define allotSymbol()	allot(sizeof(struct Symbol))

/* Return symbol whose name is given; create it if necessary */
/* (with no reduction rules and default syntax behavior). */
Symbol name2Symbol(const char*);

/* Make sure it's a valid Symbol. */
DEBUG(void checkSymbolRep(Symbol);)

/* --- Expressions --- */
/* This is the core data structure that the interpreter massages from */
/* an input program to a final result. */

/* Expr is an inductively defined datatype: */
/* Expr ::= Number | String | Symbol  */
/*	 |  variable(Symbol, restriction) */
/* 	 |  file(FILE*, is_open) |  */
/*	 |  app(Rator, Rands)	(an application with operator and operands) */
/* Rator ::= Expr */
/* Rands ::= Expr list		{ i.e., 0 or more Expr's } */
/* Thus, a typical Expr, which you type in as 'f(?x+1)',  */
/* which is parsed as f(+(?x,1)), becomes  */
/* app('f', { app('+', { variable('x', no-restriction), 1 } ) } ) */
/* where I use {} around each rands list. */

/* We represent an Expr in C as a pointer to a tagged union  */
/* with a reference counter. The rands list is represented as an array, */
/* with a num_rands field in the parent app. */
/* We also add a flag that speeds up reduction. */
/* The above example might then be: */
/* (leaving out the ref_count and fully_reduced fields) */
/*	0x10: { EXP_APP, { 0x20, 1, 0x30 } }  */
/*	0x20: { EXP_SYMBOL, (Symbol)'f' } */
/*	0x30: { EXP_APP, { 0x40, 2, 0x50 } } */
/*	0x40: { EXP_SYMBOL, (Symbol)'+' } */
/*	0x50: { EXP_VAR, { (Symbol)'x', NO_RESTRICTION } } */
/*	0x60: { EXP_NUMBER, (Number)1.0 } */

typedef struct Expr * Rator;
#define Symbol2Rator(symbol)		makeSymbol(symbol)
#define ratorEqual(rator1, rator2)	exprEqual((rator1), (rator2))
#define derefRator(rator)		deref(rator)
#define fprintRator(rator, file)	fprintExpr((rator), (file))

typedef struct Expr {
    enum ExprType { 
        EXP_NUMBER, EXP_STRING, EXP_FILE, 
        EXP_SYMBOL, EXP_VAR, EXP_APP 
    } type;
    union {
        Number number;
        String string;
        struct {		/* there should never be 2 Exprs denoting the same file */
            FILE* file;
            Flag is_open;
        } file;
        Symbol symbol;
        struct {
            Symbol name;
            int restriction;	/* ExprType or NO_RESTRICTION */
        } variable;
        struct {
            Rator rator;	/* it might be more efficient to fold this into the rands array */
            unsigned num_rands;
            struct Expr **rands;
        } app;
    } contents;
    unsigned ref_count;  /* # of references to this Expr */
    Flag fully_reduced;  /* is this Expr in normal form? */
} *Expr;

/* A special value, of C type Expr, which is NEVER equal to a valid Expr. */
/* We use it to indicate a special case in a function returning an Expr. */
#define theNullExpr		NULL
#define isNull(expr)		( (expr) == theNullExpr )

/* Variable restrictions */
#define NO_RESTRICTION -1
extern Symbol RestricNames[6];	/* 6 = # of Expr types */

/* Selectors */
#define type(expr)		( (expr)->type )

#define litNumber(expr)		( (expr)->contents.number )

#define litString(expr)		( (expr)->contents.string )

#define litFile(expr)		( (expr)->contents.file.file )
#define fileIsOpen(expr)	( (expr)->contents.file.is_open )

#define exprSymbol(expr)	( (expr)->contents.symbol )

#define varName(expr)		( (expr)->contents.variable.name )
#define varRestriction(expr) 	( (expr)->contents.variable.restriction )

/* Neither appRator nor nthRand creates a new ref to its value. */
#define appRator(expr)		( (expr)->contents.app.rator )
#define numRands(expr)		( (expr)->contents.app.num_rands )
#define appRands(expr)		( (expr)->contents.app.rands )
#define nthRand(expr, n)	( (expr)->contents.app.rands[n] )

/* Memory management */
Expr ref(Expr expr);		/* create a new reference to expr */
void deref(Expr expr);		/* destroy a reference to expr */

void* allot(size_t size);	/* allot size bytes of memory */

#define allotRands(n)	allot((n) * sizeof(struct Expr))
void freeRands(unsigned n, Expr* rands);

/* Constructors */
Expr makeNumber(Number value);
Expr makeString(String string);
Expr makeFile(FILE* file);
Expr makeSymbol(Symbol symbol);
Expr makeVariable(Symbol var_name, int restriction);
Expr makeApp(Rator rator, unsigned num_rands, Expr* rands);
/* makeApp<n> & addRand all create new refs to their rator & rands */
#define makeApp0(rator)	makeApp((rator), 0, NULL)
Expr makeApp1(Rator rator, Expr rand);
Expr makeApp2(Rator rator, Expr rand1, Expr rand2);

/* Return app with same rator and one extra rand appended. */
Expr addRand(Expr app, Expr rand);

/* Predicates */
Flag exprIsTrue(Expr);
Flag exprIsFalse(Expr);

Flag exprEqual(Expr, Expr);

/* I/O */
void fprintExpr(Expr, FILE*);		/* print to file */
void fdisplayExpr(Expr, FILE*);		/* like print, but strings are unquoted */

#define printExpr(expr)		fprintExpr((expr), stdout)
#define displayExpr(expr)	fdisplayExpr((expr), stdout)
void printlnExpr(Expr);		/* print expr followed by newline */

/* Make sure it's a valid Expr. */
DEBUG(void checkExprRep(Expr);)

extern const char * const UnknownTypeMessage;
#define UNKNOWN_TYPE error(UnknownTypeMessage)

/* --- Input stream --- */

/* Put a comment here, ok? */
typedef struct {
    int cur_char;
    char* buffer;
    char* scan_ptr;
    FILE* file;
} CharStream;

CharStream makeCharStream(FILE*);
void closeCharStream(CharStream*);

#define charStreamCurrent(pCS)	( (pCS)->cur_char )
int charStreamAdvance(CharStream*);	/* return current char and advance */

#define charStreamIsInteractive(pCS)	( (pCS)->file == stdin )

/* This procedure helps show the user where a syntax error occurred. */
void showPlaceInCurrentLine(const CharStream*);

/* --- Parsing --- */

void setupParser(void);

typedef struct {
    char type;
    union {
        Symbol symbol;
        Expr variable;
        Number number;
        String string;
    } contents;
} Token;

typedef struct {	/* A stream of parsed expr's. */
    CharStream* stream;
    Flag delayed;
    Token current_token;
} ParseStream;

void parseExprs(ParseStream*, CharStream*);
Flag moreExprs(ParseStream*);
Expr nextExpr(ParseStream* ps);	/* Pre: moreExprs(ps); returns next expr in ps */

/* --- Simplification --- */

void setupRules(void);

/* Install a new rule in the rule base; creates new refs to pattern & subst. */
/* Supersedes earlier rules that match same redex. */
void installRule(Expr pattern, Expr subst);

/* Reduce expr in applicative order to normal form if possible  */
/* (it may not terminate); return new ref to result. */
Expr simplify(Expr);

extern Flag tracing; /* true for blow-by-blow monitoring of reduction process */

/* --- Primitives --- */

void setupPrimitives(void);

#ifdef GRAPHICS
void setupGraphicsPrimitives(void);
#endif
