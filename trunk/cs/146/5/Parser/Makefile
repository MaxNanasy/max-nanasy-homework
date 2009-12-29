YACC = yacc -d
CFLAGS = -I../common

Parser: ../common/list.o CommandLine.o parser.o lexer.o
../adt/adt:
	$(MAKE) -C ../adt
CommandLine.o: Command.o Word.o Redirect.o
	$(LD) -r Command.o Word.o Redirect.o -o CommandLine.o
Command.o: Command.c
Command.c: ../adt/adt Command.adt
	< Command.adt ../adt/adt Command > Command.c 3> Command.h
Word.o: Word.c
Word.c: ../adt/adt Word.adt
	< Word.adt ../adt/adt Word > Word.c 3> Word.h
Parser.o: Parser.h CommandLine.o
lexer.o: parser.o
