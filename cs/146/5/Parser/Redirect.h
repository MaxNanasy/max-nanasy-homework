#include <stdbool.h>
#include "Word.h"

enum redirectType {
  RD_Output,
  RD_Append,
  RD_Input,
  RD_IO
};

typedef struct redirect {
  enum redirectType redirectType;
  bool rightIsFileDescriptor;
  Word left, right;
} *Redirect;

Redirect newRedirect (enum redirectType, bool, Word, Word);
void freeRedirect (Redirect);
