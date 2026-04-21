%{
#include "sctx.tab.h"
#include <string.h>
#include <stdlib.h>
%}

%option noyywrap
%option yylineno

%%

"scchart"       { return SCCHART; }
"input"         { return INPUT; }
"output"        { return OUTPUT; }
"bool"          { return BOOL; }
"int"           { return INT; }
"initial"       { return TOK_INITIAL; }
"final"         { return FINAL; }
"state"         { return STATE; }
"region"        { return REGION; }
"for"           { return FOR; }
"to"            { return TO; }
"if"            { return IF; }
"go to"         { return GOTO; }
"do"            { return DO; }
"join"          { return JOIN; }
"entry"         { return ENTRY; }
"during"        { return DURING; }
"immediate"     { return IMMEDIATE; }
"deferred"      { return DEFERRED; }
"history"       { return HISTORY; }
"shallow"       { return SHALLOW; }
"auto"          { return AUTO; }
"delayed"       { return DELAYED; }
"true"          { return TRUE_VAL; }
"false"         { return FALSE_VAL; }

[a-zA-Z_][a-zA-Z0-9_]* { yylval.str = strdup(yytext); return ID; }
[0-9]+                  { yylval.num = atoi(yytext); return NUMBER; }

"=="    { return EQEQ; }
"!="    { return NEQ; }
">="    { return GEQ; }
"<="    { return LEQ; }
"++"    { return INC; }
"--"    { return DEC; }
"&&"    { return AND; }
"||"    { return OR; }

"="     { return EQ; }
">"     { return GT; }
"<"     { return LT; }
"!"     { return NOT; }

"{"     { return LBRACE; }
"}"     { return RBRACE; }
":"     { return COLON; }
","     { return COMMA; }
";"     { return SEMI; }

[ \t\r\n]+          { }
"//".* { }
"["[^\]]*"]"        { }

.       { return yytext[0]; }

%%