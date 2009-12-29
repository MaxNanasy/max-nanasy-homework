%{
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include "CommandLine.h"
#include "Parser.h"
#include "list.h"

  struct redirectInfo { enum redirectType redirectType; bool isFileDescriptor; } rd_output = { RD_Output, false }, rd_append = { RD_Append, false }, rd_input = { RD_Input, false }, rd_io = { RD_IO, false }, rd_fd_output = { RD_Output, true }, rd_fd_input = { RD_Input, true };

static Queue currentWords, currentRedirects, currentWordSegments;

void yyerror(const char *message)
{
  fprintf (stderr, "parser: %s\n", message);
}

int yywrap()
{
  return 1;
}
%}

%token END_OF_FILE LINE_SEPARATOR
%token WORD_SEGMENT LAST_WORD_SEGMENT
%token PIPE
%token       REDIRECT_OUTPUT       APPEND_OUTPUT       REDIRECT_INPUT       REDIRECT_IO
%token    WL_REDIRECT_OUTPUT    WL_APPEND_OUTPUT    WL_REDIRECT_INPUT    WL_REDIRECT_IO
%token    FD_REDIRECT_OUTPUT                        FD_REDIRECT_INPUT
%token WL_FD_REDIRECT_OUTPUT                     WL_FD_REDIRECT_INPUT

%union {
  struct list         *word        ;
  enum   wordSegment  *wordSegment ;
  enum   command      *command     ;
  struct redirectInfo *redirectInfo;
}
%type <word>         word
%type <wordSegment>  WORD_SEGMENT LAST_WORD_SEGMENT
%type <command    >  command commandLine
%type <redirectInfo> redirectOperatorWithLeft redirectOperatorWithoutLeft
%left PIPE

%%

start: initialize commandLine { freeQueue (currentWords); freeQueue (currentRedirects); currentCommand = $2; YYACCEPT; }
     | END_OF_FILE { isEOF = true; YYACCEPT; }
initialize: { currentWords = newQueue (); currentWordSegments = newQueue (); currentRedirects = newQueue (); }

commandLine: command LINE_SEPARATOR

command: simpleCommand { $$ = (Command) newSimpleCommand (currentWords -> firstList, currentRedirects -> firstList);
                         currentWords -> firstList = NULL; currentRedirects -> firstList = NULL; }
       | command PIPE command { $$ = (Command) newPipeCommand ($1, $3); }

simpleCommand:
             | simpleCommand simpleCommandElement

simpleCommandElement: word { enqueue ($1, currentWords); }
                    | word redirectOperatorWithLeft    word { enqueue (newRedirect ($2 -> redirectType, $2 -> isFileDescriptor, $1  , $3), currentRedirects); }
                    |      redirectOperatorWithoutLeft word { enqueue (newRedirect ($1 -> redirectType, $1 -> isFileDescriptor, NULL, $2), currentRedirects); }

redirectOperatorWithLeft   : WL_REDIRECT_OUTPUT    { $$ = &rd_output   ; }
                           | WL_APPEND_OUTPUT      { $$ = &rd_append   ; }
                           | WL_REDIRECT_INPUT     { $$ = &rd_input    ; }
                           | WL_REDIRECT_IO        { $$ = &rd_io       ; }
                           | WL_FD_REDIRECT_OUTPUT { $$ = &rd_fd_output; }
                           | WL_FD_REDIRECT_INPUT  { $$ = &rd_fd_input ; }
redirectOperatorWithoutLeft: REDIRECT_OUTPUT       { $$ = &rd_output   ; }
                           | APPEND_OUTPUT         { $$ = &rd_append   ; }
                           | REDIRECT_INPUT        { $$ = &rd_input    ; }
                           | REDIRECT_IO           { $$ = &rd_io       ; }
                           | FD_REDIRECT_OUTPUT    { $$ = &rd_fd_output; }
                           | FD_REDIRECT_INPUT     { $$ = &rd_fd_input ; }
word:       initOfWord LAST_WORD_SEGMENT { enqueue ($2, currentWordSegments); $$ = currentWordSegments -> firstList; currentWordSegments -> firstList = NULL; }

initOfWord:
          | initOfWord WORD_SEGMENT      { enqueue ($2, currentWordSegments); }
