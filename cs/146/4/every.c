#include <stdlib.h>
#include <stdio.h>
#include <setjmp.h>

#define EVERY_VAR ("EVERY")

struct lineSet { unsigned int every, outOf; };

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

void processStream (struct lineSet set, FILE *stream)
{
  int n;
  jmp_buf env;
  if (! setjmp (env))
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
  struct lineSet set;
  char **filenames = argv + 1;
  FILE *stream;

  if (argc > 1 && argv [1][0] == '-') {
    set = parseLineSet (argv [1] + 1);
    ++ filenames;
  }
  else
    set = parseLineSet ((valEVERY = getenv (EVERY_VAR)) ? valEVERY : "");

  if (! * filenames)
    processStream (set, stdin);
  else
    for (; * filenames; ++ filenames) {
      if (! (stream = fopen (* filenames, "r"))) {
        fprintf (stderr, "%s: ", * filenames);
        perror ("fopen");
        exit (EXIT_FAILURE);
      }
      processStream (set, stream);
    }

  return 0;

}
