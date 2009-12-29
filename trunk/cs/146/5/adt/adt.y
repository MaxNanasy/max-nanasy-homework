%{
#include <stdio.h>
#include <stdbool.h>
#include <stdlib.h>
#include <ctype.h>
#include "list.h"

typedef List Types;

typedef struct field {
  Types types;
  char *name;
} *Field;

Field newField (List types, char *name)
{
  Field field = (Field) malloc (sizeof (struct field));
  field -> types = types;
  field -> name  = name;
  return field;
}

typedef enum declaration {
  DC_DataDeclaration,
  DC_LiteralCode
} *Declaration;

typedef struct dataDeclaration {
  enum declaration type;
  Field field;
  char *prefix;
} *DataDeclaration;

DataDeclaration newDataDeclaration (Field field, char *prefix)
{
  DataDeclaration dataDeclaration = (DataDeclaration) malloc (sizeof (struct dataDeclaration));
  dataDeclaration -> type   = DC_DataDeclaration;
  dataDeclaration -> field  = field             ;
  dataDeclaration -> prefix = prefix            ;
  return dataDeclaration;
}

typedef struct literalCode {
  enum declaration type;
  char *code;
  bool source;
} *LiteralCode;

LiteralCode newLiteralCode (char *code, bool source)
{
  LiteralCode literalCode = (LiteralCode) malloc (sizeof (struct literalCode));
  literalCode -> type   = DC_LiteralCode;
  literalCode -> code   = code          ;
  literalCode -> source = source        ;
  return literalCode;
}

static Queue currentProductions, currentFields, currentTypes;
static Declaration currentDeclaration;
static bool isEOF;

void yyerror(const char *message)
{
  fprintf (stderr, "parser: %s\n", message);
}

int yywrap()
{
  return 1;
}
%}

%union {
  char *string;
}

%token LITERAL_SOURCE_CODE LITERAL_HEADER_CODE END_OF_FILE
%token WORD FIRST_WORD
%token TYPE DATA
%left '|' ','

%type <string> WORD LITERAL_SOURCE_CODE LITERAL_HEADER_CODE

%%

start: LITERAL_SOURCE_CODE { currentDeclaration = (Declaration) newLiteralCode ($1, true ); YYACCEPT; }
     | LITERAL_HEADER_CODE { currentDeclaration = (Declaration) newLiteralCode ($1, false); YYACCEPT; }
     | END_OF_FILE { isEOF = true; YYACCEPT; }
     | initialize dataDeclaration { YYACCEPT; }

initialize: { currentProductions = newQueue (); currentFields = newQueue (); currentTypes = newQueue (); }
dataDeclaration: DATA WORD WORD '=' productions ';' { currentDeclaration = (Declaration) newDataDeclaration (newField (currentProductions -> firstList, $2), $3); }
productions:
           | productionss
productionss: production
            | productionss '|' productionss
production: WORD '(' fields ')' { enqueue (newField (currentFields -> firstList, $1), currentProductions); currentFields -> firstList = NULL; }
fields:
      | fieldss
fieldss: field
       | fieldss ',' fieldss
field: types WORD { enqueue (newField (currentTypes -> firstList, $2), currentFields); currentTypes -> firstList = NULL; }
types: singleType
     | types singleType
singleType: WORD            { enqueue ($1 , currentTypes);  }
          | '*'             { enqueue ("*", currentTypes); }
          | leftParenthesis types rightParenthesis
 leftParenthesis: '(' { enqueue ("(", currentTypes); }
rightParenthesis: ')' { enqueue (")", currentTypes); }

%%

void printField (Field field, FILE *stream)
{
  List types;
  for (types = field -> types; types != NULL; types = types -> tail)
    fprintf (stream, "%s ", (char *) types -> head);
  fputs (field -> name, stream);
}

void printProduction (Field production)
{
  List fields;
  printf ("%s (", (char *) production -> name);
  if ((fields = production -> types) != NULL) {
    printField (fields -> head, stdout);
    for (fields = fields -> tail; fields != NULL; fields = fields -> tail) {
      fputs (", ", stdout);
      printField (fields -> head, stdout);
    }
  }
  putchar (')');
}

void printDataDeclaration (Field dataDeclaration)
{
  List productions;
  printf ("data %s =", (char *) dataDeclaration -> name);
  if ((productions = dataDeclaration -> types) != NULL) {
    putchar (' '); printProduction (productions -> head);
    for (productions = productions -> tail; productions != NULL; productions = productions -> tail) {
      fputs (" | ", stdout);
      printProduction (productions -> head);
    }
  }
  puts (";");
}

char *uppercase (char *string)
{
  string [0] = toupper (string [0]);
  return string;
}

char *lowercase (char *string)
{
  string [0] = tolower (string [0]);
  return string;
}

void printFieldAsC (Field field, FILE *stream)
{
  printField (field, stream);
}

void printConstructorPrototype (Field production, FILE *stream)
{
  List fields;
  fprintf (stream, "%s new%s (", uppercase (production -> name), uppercase (production -> name));
  if ((fields = production -> types) != NULL) {
    printFieldAsC (fields -> head, stream);
    for (fields = fields -> tail; fields != NULL; fields = fields -> tail) {
      fputs (", ", stream);
      printFieldAsC (fields -> head, stream);
    }
  }
  fputc (')', stream);
}

void printProductionAsC (Field production, char *dataName, char *prefix, FILE *headerStream)
{
  List fields;
  fprintf (headerStream, "typedef struct %s {\n  enum %s type;\n", lowercase (production -> name), lowercase (dataName));
  for (fields = production -> types; fields != NULL; fields = fields -> tail) {
    fputs ("  ", headerStream);
    printFieldAsC (fields -> head, headerStream);
    fputs (";\n", headerStream);
  }
  fprintf (headerStream, "} *%s;\n\n", uppercase (production -> name));
  printConstructorPrototype (production, headerStream);
  fputs (";\n\n", headerStream);
  printConstructorPrototype (production, stdout);
  printf ("\n{\n  %s", uppercase (production -> name)); printf (" %s", lowercase (production -> name)); printf (" = (%s", uppercase (production -> name)); printf (") malloc (sizeof (struct %s", lowercase (production -> name)); printf ("));\n  debug (\"Allocated %s\\n\");\n", uppercase (production -> name));
  printf ("  %s -> type =", lowercase (production -> name)); printf (" %s_%s;\n", prefix, uppercase (production -> name));
  for (fields = production -> types; fields != NULL; fields = fields -> tail)
    printf ("  %s -> %s = %s;\n", lowercase (production -> name), ((Field) fields -> head) -> name, ((Field) fields -> head) -> name);
  printf ("  return %s;\n}\n\n", lowercase (production -> name));
}

void printDataDeclarationAsC (Field dataDeclaration, char *prefix, FILE *headerStream)
{
  List productions;
  fprintf (headerStream, "typedef enum %s {", lowercase (dataDeclaration -> name));
  if ((productions = dataDeclaration -> types) != NULL) {
    fprintf (headerStream, "\n  %s_%s", prefix, uppercase (((Field) productions -> head) -> name));
    for (productions = productions -> tail; productions != NULL; productions = productions -> tail)
      fprintf (headerStream, ",\n  %s_%s", prefix, uppercase (((Field) productions -> head) -> name));
    fputc ('\n', headerStream);
  }
  dataDeclaration -> name [0] = toupper (dataDeclaration -> name [0]);
  fprintf (headerStream, "} *%s;\n\n", uppercase (dataDeclaration -> name));
  for (productions = dataDeclaration -> types; productions != NULL; productions = productions -> tail)
    printProductionAsC (productions -> head, dataDeclaration -> name, prefix, headerStream);
}

void printDeclarationAsC (Declaration declaration, FILE *headerStream)
{
  switch (*declaration) {
  case DC_DataDeclaration:
    printDataDeclarationAsC (((DataDeclaration) declaration) -> field, ((DataDeclaration) declaration) -> prefix, headerStream);
    break;
  case DC_LiteralCode:
    fprintf (((LiteralCode) declaration) -> source ? stdout : headerStream, "%s\n", ((LiteralCode) declaration) -> code);
    break;
  }
}

int main (int argc, char *argv [])
{
  FILE *headerStream;
  char *c;
  isEOF = false;
  if (!(headerStream = fdopen (3, "w"))) { perror ("adt"); return 1; }
  printf ("#include <stdlib.h>\n#include \"debug.h\"\n#include \"%s.h\"\n", argv [1]);
  for (c = argv [1]; *(c ++) = toupper (*c););
  fprintf (headerStream, "#ifndef %s_H\n#define %s_H\n", argv [1], argv [1]);
  for (;;)
    if (! yyparse ()) {
      if (isEOF) break;
      printDeclarationAsC (currentDeclaration, headerStream);
    }
  fputs ("#endif\n", headerStream);
  return 0;
}
