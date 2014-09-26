CC = gcc
CFLAGS = -O2 -Wall -ansi -pedantic -g

OBJS = expr.o parse.o prim.o req.o rule.o symbol.o


all: req

req: $(OBJS)
	$(CC) $(CFLAGS) $(OBJS) -lm -o req

clean:
	rm -f $(OBJS) req

expr.o: expr.c req.h
parse.o: parse.c req.h
prim.o: prim.c req.h
req.o: req.c req.h
rule.o: rule.c req.h
symbol.o: symbol.c req.h
