%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern int yylex();
extern int yylineno;
extern char* yytext;
void yyerror(const char *s);

// Basic state tracking for Rust Generation
char* chart_name = NULL;
char states[100][256];
int state_count = 0;
char inputs[100][256];
int input_count = 0;

void add_state(const char* name) {
    strcpy(states[state_count++], name);
}

void add_input(const char* name) {
    strcpy(inputs[input_count++], name);
}

%}

%union {
    char* str;
    int num;
}

%token <str> ID
%token <num> NUMBER
%token SCCHART INPUT OUTPUT BOOL INT TOK_INITIAL FINAL STATE REGION FOR TO IF GOTO DO JOIN ENTRY DURING IMMEDIATE DEFERRED HISTORY SHALLOW AUTO DELAYED TRUE_VAL FALSE_VAL
%token EQEQ EQ INC LBRACE RBRACE COLON COMMA

%%

program:
    SCCHART ID LBRACE elements RBRACE {
        chart_name = $2;
        
        // --- Rust Code Generation (Skeleton) ---
        printf("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\n");
        printf("enum TopState {\n");
        for(int i=0; i<state_count; i++) {
            printf("    %s,\n", states[i]);
        }
        printf("}\n\n");
        
        printf("struct Inputs {\n");
        for(int i=0; i<input_count; i++) {
            printf("    %s: bool, // Type inference simplified\n", inputs[i]);
        }
        printf("}\n\n");
        
        printf("struct Machine {\n");
        printf("    top: TopState,\n");
        printf("    inputs: Inputs,\n");
        printf("}\n\n");
        
        printf("impl Machine {\n");
        printf("    fn new() -> Self {\n");
        printf("        Self {\n");
        if (state_count > 0) printf("            top: TopState::%s,\n", states[0]);
        printf("            inputs: Inputs {\n");
        for(int i=0; i<input_count; i++) {
            printf("                %s: false,\n", inputs[i]);
        }
        printf("            },\n");
        printf("        }\n");
        printf("    }\n");
        printf("}\n");
    }
    ;

elements:
    element elements
    | /* empty */
    ;

element:
    decl
    | state_def
    | region_def
    | transition
    | action
    ;

decl:
    INPUT type id_list
    | OUTPUT type id_list
    ;

type:
    BOOL | INT
    ;

id_list:
    ID { add_input($1); }
    | ID COMMA id_list { add_input($1); }
    ;

state_def:
    state_mod STATE ID LBRACE elements RBRACE { add_state($3); }
    | state_mod STATE ID { add_state($3); }
    ;

state_mod:
    TOK_INITIAL FINAL
    | TOK_INITIAL
    | FINAL
    | /* empty */
    ;

region_def:
    REGION ID LBRACE elements RBRACE
    | REGION ID FOR ID COLON NUMBER TO NUMBER LBRACE elements RBRACE
    ;

transition:
    IF transition_cond GOTO ID transition_mods
    | NUMBER ID GOTO ID transition_mods 
    | GOTO ID transition_mods
    | AUTO GOTO ID transition_mods
    | DELAYED GOTO ID transition_mods
    | IMMEDIATE DO action_stmt GOTO ID transition_mods
    | JOIN TO ID
    | DO action_stmt JOIN TO ID
    ;

transition_cond:
    NUMBER ID
    | ID EQEQ NUMBER
    | ID
    ;

transition_mods:
    SHALLOW HISTORY
    | HISTORY
    | DEFERRED
    | /* empty */
    ;

action:
    ENTRY DO action_stmt
    | DURING DO action_stmt
    ;

action_stmt:
    ID EQ expr
    | ID INC
    ;

expr:
    NUMBER
    | ID
    | TRUE_VAL
    | FALSE_VAL
    ;

%%

void yyerror(const char *s) {
    fprintf(stderr, "Error at line %d: %s near '%s'\n", yylineno, s, yytext);
}

int main(int argc, char **argv) {
    if (argc > 1) {
        FILE *file = fopen(argv[1], "r");
        if (!file) {
            perror("Could not open file");
            return 1;
        }
        extern FILE *yyin;
        yyin = file;
    }
    yyparse();
    return 0;
}