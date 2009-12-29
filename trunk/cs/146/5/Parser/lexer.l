%{
#include <string.h>
#include <stdbool.h>
#include "y.tab.h"
#include "CommandLine.h"

#define returnSimpleWordSegment(X, Y) do { yylval.wordSegment = (WordSegment) newSimpleWordSegment (strdup (X)); return Y; } while (false);

bool withLeft = false;
%}

%option stack

%x SINGLE_QUOTE DOUBLE_QUOTE BACKSLASH

SIMPLE_WORD_SEGMENT_ELEMENT [A-Za-z0-9_.+\-*/\[\]\{\}]
SIMPLE_WORD_SEGMENT         {SIMPLE_WORD_SEGMENT_ELEMENT}+
FOLLOWING_WORD_SEGMENT      [A-Za-z0-9_.+\-*/\[\]\{\}]{+}[\'\"\\]
FOLLOWING_REDIRECT_OPERATOR [<>]
SQ_SIMPLE_WORD              [^\']+
DQ_SIMPLE_WORD              [^\"]+
REDIRECT_OPERATOR           (>|>>|<|<>)

%%

{SIMPLE_WORD_SEGMENT}/{FOLLOWING_WORD_SEGMENT}      returnSimpleWordSegment (yytext, WORD_SEGMENT     );
{SIMPLE_WORD_SEGMENT}/{FOLLOWING_REDIRECT_OPERATOR} withLeft = true; returnSimpleWordSegment (yytext, LAST_WORD_SEGMENT);
{SIMPLE_WORD_SEGMENT}                               returnSimpleWordSegment (yytext, LAST_WORD_SEGMENT);
[ \t]               ;

#.*                 ;
[;\n]               return LINE_SEPARATOR;
<<EOF>>             return END_OF_FILE;

\|                  return PIPE;

">"                 return withLeft ? withLeft = false, WL_REDIRECT_OUTPUT    : REDIRECT_OUTPUT   ;
">>"                return withLeft ? withLeft = false, WL_APPEND_OUTPUT      : APPEND_OUTPUT     ;
"<"                 return withLeft ? withLeft = false, WL_REDIRECT_INPUT     : REDIRECT_INPUT    ;
"<>"                return withLeft ? withLeft = false, WL_REDIRECT_IO        : REDIRECT_IO       ;
">&"                return withLeft ? withLeft = false, WL_FD_REDIRECT_OUTPUT : FD_REDIRECT_OUTPUT;
"<&"                return withLeft ? withLeft = false, WL_FD_REDIRECT_INPUT  : FD_REDIRECT_INPUT ;

\\\n/{FOLLOWING_WORD_SEGMENT}      returnSimpleWordSegment ("", WORD_SEGMENT);
\\\n/{FOLLOWING_REDIRECT_OPERATOR} withLeft = true; returnSimpleWordSegment ("", WORD_SEGMENT);
\\\n                               returnSimpleWordSegment ("", LAST_WORD_SEGMENT);
\\./{FOLLOWING_WORD_SEGMENT}       returnSimpleWordSegment (yytext, WORD_SEGMENT);
\\./{FOLLOWING_REDIRECT_OPERATOR}  withLeft = true; returnSimpleWordSegment ("", LAST_WORD_SEGMENT);
\\.                                returnSimpleWordSegment (yytext, LAST_WORD_SEGMENT);

\'                                             yy_push_state (SINGLE_QUOTE);
<SINGLE_QUOTE>{SQ_SIMPLE_WORD}                 returnSimpleWordSegment (yytext, WORD_SEGMENT);
<SINGLE_QUOTE>\'/{FOLLOWING_WORD_SEGMENT}      yy_pop_state ();
<SINGLE_QUOTE>\'/{FOLLOWING_REDIRECT_OPERATOR} withLeft = true; yy_pop_state (); returnSimpleWordSegment ("", LAST_WORD_SEGMENT);;
<SINGLE_QUOTE>\'                               yy_pop_state (); returnSimpleWordSegment ("", LAST_WORD_SEGMENT);

\"                                             yy_push_state (DOUBLE_QUOTE);
<DOUBLE_QUOTE>{DQ_SIMPLE_WORD}                 returnSimpleWordSegment (yytext, WORD_SEGMENT);
<DOUBLE_QUOTE>\"/{FOLLOWING_WORD_SEGMENT}      yy_pop_state ();
<DOUBLE_QUOTE>\"/{FOLLOWING_REDIRECT_OPERATOR} withLeft = true; yy_pop_state (); returnSimpleWordSegment ("", LAST_WORD_SEGMENT);
<DOUBLE_QUOTE>\"                               yy_pop_state (); returnSimpleWordSegment ("", LAST_WORD_SEGMENT);
