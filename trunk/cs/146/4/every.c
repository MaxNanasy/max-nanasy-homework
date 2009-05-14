#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <setjmp.h>

#define EVERY_VAR ("EVERY")

struct lineSet {
  unsigned int every, outOf;
};

void echoLine (jmp_buf env, FILE *stream)
{
  int character;
  for (;;) {
    character = getc (stream);
    switch (character) {
    case '\n':
      putchar (character);
      return;
    case EOF:
      longjmp (env, 1);
    default:
      putchar (character);
    }
  }
}

void disregardLine (jmp_buf env, FILE *stream)
{
  int character;
  while ((character = getc (stream)) != '\n')
    if (character == EOF)
      longjmp (env, 1);
}

void processLineSet (jmp_buf env, struct lineSet set, FILE *stream)
{
  int n;
  for (;;) {
    for (n = 0; n < set.every; ++ n) echoLine      (env, stream);
    for (     ; n < set.outOf; ++ n) disregardLine (env, stream);
  }
}

struct lineSet parseLineSet (char *string)
{
  struct lineSet set;
  int parsePosition;
  if (string [0] == '\0') set.every = set.outOf = 1;
  else {
    parsePosition = sscanf (string, "%u", &set.outOf);
    if (string [parsePosition] == '\0') set.every = 1;
    else sscanf (string + parsePosition, ",%u", &set.every);
  }
  return set;
}

int main (int argc, char *argv [])
{

  char *valEVERY;
  size_t length;
  struct lineSet set;
  char **filenames = argv + 1;
  FILE *stream;
  jmp_buf env;

  if (argc > 1 && argv [1][0] == '-') {
    set = parseLineSet (argv [1] + 1);
    ++ filenames;
  }
  else
    set = parseLineSet ((valEVERY = getenv (EVERY_VAR)) ? valEVERY : "");

  if (! * filenames) {
    if (! setjmp (env))
      processLineSet (env, set, stdin);
  }
  else
    for (; * filenames; ++ filenames) {
      stream = fopen (* filenames, "r");
      if (! setjmp (env))
        processLineSet (env, set, stream);
    }


  return 0;

}
