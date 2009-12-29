#include <stdlib.h>
#include <stdbool.h>
#include "CommandLine.h"
#include "debug.h"

Redirect newRedirect (enum redirectType redirectType, bool rightIsFileDescriptor, Word left, Word right)
{
  Redirect redirect = (Redirect) malloc (sizeof (struct redirect));
  debug ("Allocated Redirect\n");
  redirect -> redirectType          = redirectType         ;
  redirect -> rightIsFileDescriptor = rightIsFileDescriptor;
  redirect -> left                  = left                 ;
  redirect -> right                 = right                ;
  return redirect;
}
