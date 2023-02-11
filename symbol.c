#include <stdlib.h>
#include <string.h>

#include "req.h"

#define TABLE_SIZE 71

static Symbol hashtable[TABLE_SIZE] = { NULL, NULL, NULL /* ... */ };

static unsigned hash(const char* s)
{
    unsigned h = 0;
    for (; *s; s++)
        h = 2*h + *s;
    return h % TABLE_SIZE;
}

Symbol name2Symbol(const char* name)
{
    Symbol* bucket = hashtable + hash(name);
    Symbol p = *bucket;
    for (; p; p = p->next)
        if (!strcmp(name, symbolName(p)))
            return p;
    {				/* Symbol doesn't exist; create it. */
        Symbol result = allotSymbol();
        if (sizeof(result->name) < strlen(name)+1)
            error("Variable name too long: %s", name);	/* should print warning and truncate, instead */
        strcpy(result->name, name);
        result->primitive_reducer = NULL; /* set up with no operator binding */
        result->opinfo = &NonOperatorInfo;	/* and normal syntax */
        result->rules = NULL;			/* and no reduction rules */
        result->next = *bucket;
        *bucket = result;
        return result;
    }
}

DEBUG(
void checkSymbolRep(Symbol symbol) { }
)

