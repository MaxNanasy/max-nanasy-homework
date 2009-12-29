#include <stdio.h>
#include <stdbool.h>
#include "Parser.h"
#include "CommandLine.h"

void printWordSegment (WordSegment wordSegment)
{
  char *c;
  switch (*wordSegment) {
  case WS_SimpleWordSegment:
    for (c = ((SimpleWordSegment) wordSegment) -> string; *c; ++ c)
      if (*c == '\'')
        fputs ("'\\''", stdout);
      else
        putchar (*c);
    break;
  }
}


void printWord (Word word)
{
  List wordSegments;
  putchar ('\'');
  for (wordSegments = word; wordSegments != NULL; wordSegments = wordSegments -> tail)
    printWordSegment (wordSegments -> head);
  fputs ("'", stdout);
}

void printRedirect (Redirect redirect)
{
  if (redirect -> left)
    printWord (redirect -> left);
  switch (redirect -> redirectType) {
  case RD_Output:
    putchar ('>');
    break;
  case RD_Append:
    fputs (">>", stdout);
    break;
  case RD_Input:
    putchar ('<');
    break;
  case RD_IO:
    fputs ("<>", stdout);
    break;
  }
  if (redirect -> rightIsFileDescriptor)
    putchar ('&');
  printWord (redirect -> right);
}

unsigned int lengthOfCommand (Command command)
{
  switch (*command) {
  case CMD_SimpleCommand:
    return 1;
  case CMD_PipeCommand:
    return lengthOfCommand (((PipeCommand) command) -> producer) + lengthOfCommand (((PipeCommand) command) -> consumer);
  }
}

void printCommand (Command command)
{
  List words, wordSegments, redirects;
  switch (*command) {
  case CMD_SimpleCommand:
    for (redirects = ((SimpleCommand) command) -> redirects; redirects != NULL; redirects = redirects -> tail) {
      printRedirect (redirects -> head); putchar (' '); }
    for (words = ((SimpleCommand) command) -> words; words != NULL; words = words -> tail) {
      printWord (words -> head); putchar (' '); }
    break;
  case CMD_PipeCommand:
    printCommand (((PipeCommand) command) -> producer);
    fputs ("| ", stdout);
    printCommand (((PipeCommand) command) -> consumer);
    break;
  }
}

int main (int argc, char *argv [])
{
  isEOF = false;
  for (;;) {
    fputs ("? ", stdout);
    if (! yyparse ()) {
      if (isEOF) break;
      printf ("%d: ", lengthOfCommand (currentCommand));
      printCommand (currentCommand);
      //      freeCommand (currentCommand);
      putchar ('\n');
    }
  }
  return 0;
}
