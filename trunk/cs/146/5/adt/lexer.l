%{
#include <string.h>
#include <stdbool.h>
#include "y.tab.h"
%}

%x LITERAL_SOURCE_CODE_STATE LITERAL_HEADER_CODE_STATE
%option stack

WORD [_A-Za-z][_A-Za-z0-9]*

%%
data                return DATA;
{WORD}              yylval.string = strdup (yytext); return WORD;
[ \t\n]             ;
<<EOF>>             return END_OF_FILE;

\%\[                                    yy_push_state (LITERAL_SOURCE_CODE_STATE);
<LITERAL_SOURCE_CODE_STATE>\%\]         yy_pop_state ();
<LITERAL_SOURCE_CODE_STATE>(.|\n)*/\%\] yylval.string = strdup (yytext); return LITERAL_SOURCE_CODE;

\%\{                                    yy_push_state (LITERAL_HEADER_CODE_STATE);
<LITERAL_HEADER_CODE_STATE>\%\}         yy_pop_state ();
<LITERAL_HEADER_CODE_STATE>(.|\n)*/\%\} yylval.string = strdup (yytext); return LITERAL_HEADER_CODE;

.                   return yytext [0];
