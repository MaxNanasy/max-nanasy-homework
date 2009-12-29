#ifndef DEBUG_H
#define DEBUG_H

#include <stdarg.h>
#include <stdio.h>

//#define DEBUG

#ifdef DEBUG
#define debug(format, ...) fprintf (stderr, format, ## __VA_ARGS__) // macro from http://redhat.com/docs/manuals/enterprise/RHEL-4-Manual/gcc/variadic-macros.html
#else
#define debug(format, ...)
#endif

#endif
