%{
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>

extern int   yylex(void);
extern int   yylineno;
extern char *yytext;
void yyerror(const char *s);

static char *cap(const char *s) {
    char *r = strdup(s);
    if (r[0] >= 'a' && r[0] <= 'z') r[0] -= 32;
    return r;
}

static char *cap_str(const char *s) {
    static char bufs[16][256];
    static int bidx = 0;
    char *r = bufs[bidx];
    bidx = (bidx + 1) % 16;
    if (!s) { r[0] = '\0'; return r; }
    strncpy(r, s, 255);
    r[255] = '\0';
    if (r[0] >= 'a' && r[0] <= 'z') r[0] -= 32;
    return r;
}

static char *lcase(const char *s) {
    char *r = strdup(s);
    for (int i = 0; r[i]; i++)
        if (r[i] >= 'A' && r[i] <= 'Z') r[i] += 32;
    return r;
}

#define MAX_VARS    256
#define MAX_STATES  256
#define MAX_REGIONS  64
#define MAX_TRANS   512
#define CTX_DEPTH    64

typedef struct {
    char name[256];
    char type[32];   
    int  is_output;  
} VarDecl;

VarDecl vars[MAX_VARS];
int     var_count = 0;

static void add_var(const char *name, const char *type, int is_output) {
    VarDecl *v = &vars[var_count++];
    strncpy(v->name, name, 255);
    strncpy(v->type, type, 31);
    v->is_output = is_output;
}


static int is_input_var(const char *name) {
    for (int i = 0; i < var_count; i++) {
        if (strcmp(vars[i].name, name) == 0 && !vars[i].is_output) return 1;
    }
    return 0; 
}

typedef struct {
    char name[256];
    char parent[256];   
    int  is_initial;
    int  is_final;
    int  has_entry;
    char entry_stmt[512];
    int  has_during;
    char during_stmt[512];
} StateInfo;

StateInfo state_table[MAX_STATES];
int       state_count = 0;

typedef struct {
    char name[256];
    char parent_state[256];
} RegionInfo;

RegionInfo region_table[MAX_REGIONS];
int        region_count = 0;

typedef struct {
    char from_state[256];
    char from_parent[256]; 
    char to_state[256];
    int  has_if;
    int  cond_count;
    char cond_var[256];
    int  is_auto;
    int  is_delayed;
    int  is_immediate;
    int  is_default;
    int  is_join;
    char join_to[256];
    int  has_do;
    char do_stmt[512];
    int  history;
    int  is_deferred;
} TransInfo;

TransInfo trans_table[MAX_TRANS];
int       trans_count = 0;


char ctx_stack[CTX_DEPTH][256];
char last_peer_state[CTX_DEPTH][256];
int  ctx_top = 0;
char chart_name[256] = "";

static void push_ctx(const char *name) {
    if (ctx_top < CTX_DEPTH) {
        strncpy(ctx_stack[ctx_top], name, 255);
        last_peer_state[ctx_top][0] = '\0';
        ctx_top++;
    }
}
static void pop_ctx(void) {
    if (ctx_top > 0) ctx_top--;
}
static const char *cur_ctx(void) {
    return ctx_top > 0 ? ctx_stack[ctx_top - 1] : chart_name;
}
static const char *parent_ctx(void) {
    return ctx_top > 1 ? ctx_stack[ctx_top - 2] : chart_name;
}
static void set_last_peer(const char *name) {
    if (ctx_top > 0) {
        strncpy(last_peer_state[ctx_top - 1], name, 255);
    } else {
        strncpy(last_peer_state[0], name, 255);
    }
}

static StateInfo *find_state(const char *name, const char *parent) {
    for (int i = 0; i < state_count; i++)
        if (strcmp(state_table[i].name, name) == 0 && strcmp(state_table[i].parent, parent) == 0)
            return &state_table[i];
    return NULL;
}

static StateInfo *get_current_state(void) {
    if (ctx_top > 0 && last_peer_state[ctx_top - 1][0] != '\0') {
        return find_state(last_peer_state[ctx_top - 1], cur_ctx());
    }
    if (ctx_top > 0) {
        return find_state(cur_ctx(), parent_ctx());
    }
    return NULL;
}

#define SET_TRANS_SRC(t) \
    do { \
        StateInfo *src = get_current_state(); \
        if (src) { \
            strncpy((t)->from_state, src->name, 255); \
            strncpy((t)->from_parent, src->parent, 255); \
        } else { \
            strncpy((t)->from_state, cur_ctx(), 255); \
            strncpy((t)->from_parent, parent_ctx(), 255); \
        } \
    } while(0)


static void parse_transition_cond(TransInfo *t, char *cond) {
    char *colon = strchr(cond, ':');
    if (colon) {
        *colon = '\0';
        t->cond_count = atoi(cond);
        strncpy(t->cond_var, colon+1, 255);
    } else {
        strncpy(t->cond_var, cond, 255);
    }
}

static void add_transition(int has_if, char *cond, int is_immediate, int is_delayed, int is_auto, int is_default, int is_join, char *do_stmts, char *target_state, int mod) {
    TransInfo *t = &trans_table[trans_count++];
    memset(t, 0, sizeof *t);
    SET_TRANS_SRC(t);
    
    if (target_state) strncpy(t->to_state, target_state, 255);
    
    t->has_if = has_if;
    if (has_if && cond) parse_transition_cond(t, cond);
    
    t->is_immediate = is_immediate;
    t->is_delayed = is_delayed;
    t->is_auto = is_auto;
    t->is_default = is_default;
    
    if (is_join) {
        t->is_join = 1;
        char *c = cap(target_state);
        strncpy(t->join_to, c, 255);
        free(c);
    }
    
    if (do_stmts) {
        t->has_do = 1;
        strncpy(t->do_stmt, do_stmts, 511);
    }

    if (mod == 1) t->history = 1;
    else if (mod == 2) t->history = 2;
    else if (mod == 3) t->is_deferred = 1;
}

static void add_state_entry(const char *name, const char *parent, int is_init, int is_final) {
    StateInfo *s = &state_table[state_count++];
    strncpy(s->name,   name,   255);
    strncpy(s->parent, parent, 255);
    s->is_initial   = is_init;
    s->is_final     = is_final;
    s->has_entry    = 0;
    s->entry_stmt[0]= '\0';
    s->has_during   = 0;
    s->during_stmt[0]='\0';
}

static void enum_name_for(const char *scope, char *out) {
    if (strcmp(scope, chart_name) == 0) strcpy(out, "TopState");
    else sprintf(out, "%sState", cap_str(scope));
}

static void field_name_for(const char *scope, char *out) {
    char *l = lcase(scope);
    sprintf(out, "%s_state", l);
    free(l);
}

static const char *initial_child(const char *scope) {
    for (int i = 0; i < state_count; i++)
        if (strcmp(state_table[i].parent, scope) == 0 && state_table[i].is_initial)
            return state_table[i].name;
    for (int i = 0; i < state_count; i++)
        if (strcmp(state_table[i].parent, scope) == 0)
            return state_table[i].name;
    return "";
}

static const char *final_child(const char *scope) {
    for (int i = 0; i < state_count; i++)
        if (strcmp(state_table[i].parent, scope) == 0 && state_table[i].is_final)
            return state_table[i].name;
    return "";
}

static int child_count(const char *scope) {
    int n = 0;
    for (int i = 0; i < state_count; i++)
        if (strcmp(state_table[i].parent, scope) == 0) n++;
    return n;
}

static int feat_has_shallow  = 0;
static int feat_has_deep     = 0;
static int feat_has_deferred = 0;
static int feat_has_counter  = 0;
static int feat_has_delayed  = 0;
static int feat_has_regions  = 0;

static void detect_features(void) {
    for (int i = 0; i < trans_count; i++) {
        if (trans_table[i].history == 1) feat_has_shallow  = 1;
        if (trans_table[i].history == 2) feat_has_deep     = 1;
        if (trans_table[i].is_deferred)  feat_has_deferred = 1;
        if (trans_table[i].cond_count>0) feat_has_counter  = 1;
        if (trans_table[i].is_delayed)   feat_has_delayed  = 1;
    }
    feat_has_regions = (region_count > 0);
}

static int count_cond_vars(char seen[][256]) {
    int nseen = 0;
    for (int i = 0; i < trans_count; i++) {
        if (trans_table[i].cond_count <= 0) continue;
        int dup = 0;
        for (int k = 0; k < nseen; k++)
            if (strcmp(seen[k], trans_table[i].cond_var) == 0) { dup=1; break; }
        if (!dup) strcpy(seen[nseen++], trans_table[i].cond_var);
    }
    return nseen;
}

static void print_cond(TransInfo *tr) {
    if (tr->cond_count > 0) {
        char *l = lcase(tr->cond_var);
        if (is_input_var(tr->cond_var))
            printf("self.inputs.%s && self.%s_counter >= %d", tr->cond_var, l, tr->cond_count);
        else
            printf("self.%s && self.%s_counter >= %d", tr->cond_var, l, tr->cond_count);
        free(l);
    } else {
        printf("%s", tr->cond_var);
    }
}

static void generate_rust(void) {
    detect_features();
    const char *top_init = initial_child(chart_name);
    const char *top_fin  = final_child(chart_name);

    if (child_count(chart_name) > 0) {
        printf("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\nenum TopState {\n");
        for (int i = 0; i < state_count; i++)
            if (strcmp(state_table[i].parent, chart_name) == 0)
                printf("    %s,\n", cap_str(state_table[i].name));
        printf("}\n\n");
    }

    for (int i = 0; i < state_count; i++) {
        if (child_count(state_table[i].name) == 0) continue;
        char ename[300]; enum_name_for(state_table[i].name, ename);
        printf("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\nenum %s {\n", ename);
        for (int j = 0; j < state_count; j++)
            if (strcmp(state_table[j].parent, state_table[i].name) == 0)
                printf("    %s,\n", cap_str(state_table[j].name));
        printf("}\n\n");
    }

    for (int r = 0; r < region_count; r++) {
        const char *rname = region_table[r].name;
        if (child_count(rname) == 0) continue;
        char ename[300]; enum_name_for(rname, ename);
        printf("#[derive(Debug, Clone, Copy, PartialEq, Eq)]\nenum %s {\n", ename);
        for (int j = 0; j < state_count; j++)
            if (strcmp(state_table[j].parent, rname) == 0)
                printf("    %s,\n", cap_str(state_table[j].name));
        printf("}\n\n");
    }

    int has_inputs = 0;
    for (int i = 0; i < var_count; i++) if (!vars[i].is_output) { has_inputs=1; break; }

    if (has_inputs) {
        printf("struct Inputs {\n");
        for (int i = 0; i < var_count; i++) {
            if (vars[i].is_output) continue;
            const char *rtype = strcmp(vars[i].type,"bool")==0 ? "bool" : "i32";
            printf("    %s: %s,\n", vars[i].name, rtype);
        }
        printf("}\n\n");
    }

    printf("struct Machine {\n");
    printf("    top: TopState,\n");

    for (int i = 0; i < state_count; i++) {
        if (child_count(state_table[i].name) == 0) continue;
        char ename[300], fname[300];
        enum_name_for(state_table[i].name, ename);
        field_name_for(state_table[i].name, fname);
        printf("    %s: %s,\n", fname, ename);
    }

    for (int r = 0; r < region_count; r++) {
        const char *rname = region_table[r].name;
        if (child_count(rname) == 0) continue;
        char ename[300], fname[300];
        enum_name_for(rname, ename);
        field_name_for(rname, fname);
        printf("    %s: %s,\n", fname, ename);
    }

    if (feat_has_counter) {
        char seen[MAX_TRANS][256];
        int nseen = count_cond_vars(seen);
        for (int k = 0; k < nseen; k++) {
            char *l = lcase(seen[k]);
            printf("    %s_counter: i32,\n", l);
            free(l);
        }
    }

    if (feat_has_shallow)  printf("    shallow_history: TopState,\n");
    if (feat_has_deep)     printf("    deep_history: TopState,\n");
    if (feat_has_deferred) printf("    deferred_transition: bool,\n");
    if (feat_has_delayed && !feat_has_deferred) {
        for (int i = 0; i < trans_count; i++) {
            if (!trans_table[i].is_delayed) continue;
            char *l = lcase(trans_table[i].to_state);
            printf("    delayed_to_%s: bool,\n", l);
            free(l);
        }
    }

    for (int i = 0; i < var_count; i++) {
        if (!vars[i].is_output) continue;
        const char *rtype = strcmp(vars[i].type,"bool")==0 ? "bool" : "i32";
        printf("    %s: %s,\n", vars[i].name, rtype);
    }

    if (has_inputs) printf("    inputs: Inputs,\n");
    printf("}\n\n");
    printf("impl Machine {\n");
    printf("    fn new() -> Self {\n        Self {\n");
    printf("            top: TopState::%s,\n", top_init[0] ? cap_str(top_init) : "Done");
    for (int i = 0; i < state_count; i++) {
        if (child_count(state_table[i].name) == 0) continue;
        char ename[300], fname[300];
        enum_name_for(state_table[i].name, ename);
        field_name_for(state_table[i].name, fname);
        const char *ic = initial_child(state_table[i].name);
        printf("            %s: %s::%s,\n", fname, ename, ic[0] ? cap_str(ic) : "Done");
    }
    for (int r = 0; r < region_count; r++) {
        const char *rname = region_table[r].name;
        if (child_count(rname) == 0) continue;
        char ename[300], fname[300];
        enum_name_for(rname, ename);
        field_name_for(rname, fname);
        const char *ic = initial_child(rname);
        printf("            %s: %s::%s,\n", fname, ename, ic[0] ? cap_str(ic) : "Done");
    }

    if (feat_has_counter) {
        char seen[MAX_TRANS][256];
        int nseen = count_cond_vars(seen);
        for (int k = 0; k < nseen; k++) {
            char *l = lcase(seen[k]);
            printf("            %s_counter: 0,\n", l);
            free(l);
        }
    }
    if (feat_has_shallow)  printf("            shallow_history: TopState::%s,\n", top_init[0] ? cap_str(top_init) : "Done");
    if (feat_has_deep)     printf("            deep_history: TopState::%s,\n", top_init[0] ? cap_str(top_init) : "Done");
    if (feat_has_deferred) printf("            deferred_transition: false,\n");
    if (feat_has_delayed && !feat_has_deferred) {
        for (int i = 0; i < trans_count; i++) {
            if (!trans_table[i].is_delayed) continue;
            char *l = lcase(trans_table[i].to_state);
            printf("            delayed_to_%s: false,\n", l);
            free(l);
        }
    }

    for (int i = 0; i < var_count; i++) {
        if (!vars[i].is_output) continue;
        const char *def = strcmp(vars[i].type,"bool")==0 ? "false" : "0";
        printf("            %s: %s,\n", vars[i].name, def);
    }

    if (has_inputs) {
        printf("            inputs: Inputs {\n");
        for (int i = 0; i < var_count; i++) {
            if (vars[i].is_output) continue;
            const char *def = strcmp(vars[i].type,"bool")==0 ? "false" : "0";
            printf("                %s: %s,\n", vars[i].name, def);
        }
        printf("            },\n");
    }
    printf("        }\n    }\n\n");
    if (has_inputs) {
        printf("    fn set_inputs(&mut self");
        for (int i = 0; i < var_count; i++) {
            if (vars[i].is_output) continue;
            const char *rt = strcmp(vars[i].type,"bool")==0 ? "bool" : "i32";
            printf(", %s: %s", vars[i].name, rt);
        }
        printf(") {\n");
        for (int i = 0; i < var_count; i++) {
            if (vars[i].is_output) continue;
            printf("        self.inputs.%s = %s;\n", vars[i].name, vars[i].name);
        }
        printf("    }\n\n");
    }

    printf("    fn tick(&mut self) {\n");
    if (feat_has_counter) {
        char seen[MAX_TRANS][256];
        int nseen = count_cond_vars(seen);
        for (int k = 0; k < nseen; k++) {
            char *l = lcase(seen[k]);
            if (is_input_var(seen[k]))
                printf("        if self.inputs.%s {\n", seen[k]);
            else
                printf("        if self.%s {\n", seen[k]);
            printf("            self.%s_counter += 1;\n", l);
            printf("        } else {\n");
            printf("            self.%s_counter = 0;\n", l);
            printf("        }\n\n");
            free(l);
        }
    }

    for (int i = 0; i < state_count; i++) {
        StateInfo *ws = &state_table[i];
        if (strcmp(ws->parent, chart_name) != 0) continue;
        if (ws->is_initial) continue;
        int has_special = 0;
        for (int t = 0; t < trans_count; t++) {
            TransInfo *tr = &trans_table[t];
            if (strcmp(tr->from_state, ws->name) != 0 || strcmp(tr->from_parent, ws->parent) != 0) continue;
            if (tr->history || tr->is_deferred || tr->is_default) { has_special=1; break; }
        }
        if (!has_special) continue;
        printf("        if self.top == TopState::%s {\n", cap_str(ws->name));
        for (int t = 0; t < trans_count; t++) {
            TransInfo *tr = &trans_table[t];
            if (strcmp(tr->from_state, ws->name) != 0 || strcmp(tr->from_parent, ws->parent) != 0 || tr->history != 1) continue;
            printf("            if "); print_cond(tr); printf(" {\n");
            printf("                println!(\"Shallow history restore\");\n");
            printf("                self.top = self.shallow_history;\n");
            printf("                return;\n");
            printf("            }\n\n");
        }
        for (int t = 0; t < trans_count; t++) {
            TransInfo *tr = &trans_table[t];
            if (strcmp(tr->from_state, ws->name) != 0 || strcmp(tr->from_parent, ws->parent) != 0 || tr->history != 2) continue;
            printf("            if "); print_cond(tr); printf(" {\n");
            printf("                println!(\"Deep history restore\");\n");
            printf("                self.top = self.deep_history;\n");
            printf("                return;\n");
            printf("            }\n\n");
        }
        for (int t = 0; t < trans_count; t++) {
            TransInfo *tr = &trans_table[t];
            if (strcmp(tr->from_state, ws->name) != 0 || strcmp(tr->from_parent, ws->parent) != 0 || !tr->is_deferred) continue;
            printf("            if "); print_cond(tr); printf(" {\n");
            printf("                println!(\"Deferred transition scheduled\");\n");
            printf("                self.deferred_transition = true;\n");
            printf("                return;\n");
            printf("            }\n\n");
        }
        for (int t = 0; t < trans_count; t++) {
            TransInfo *tr = &trans_table[t];
            if (strcmp(tr->from_state, ws->name) != 0 || strcmp(tr->from_parent, ws->parent) != 0 || !tr->is_default) continue;
            printf("            println!(\"Default transition to %s\");\n", tr->to_state);
            printf("            self.top = TopState::%s;\n", cap_str(tr->to_state));
            for (int j = 0; j < state_count; j++) {
                if (child_count(state_table[j].name) == 0) continue;
                char ename[300], fname[300];
                enum_name_for(state_table[j].name, ename);
                field_name_for(state_table[j].name, fname);
                printf("            self.%s = %s::%s;\n", fname, ename, cap_str(initial_child(state_table[j].name)));
            }
            for (int r = 0; r < region_count; r++) {
                const char *rname = region_table[r].name;
                if (child_count(rname) == 0) continue;
                char ename[300], fname[300];
                enum_name_for(rname, ename);
                field_name_for(rname, fname);
                printf("            self.%s = %s::%s;\n", fname, ename, cap_str(initial_child(rname)));
            }
            printf("            return;\n");
        }
        printf("        }\n\n");
    }

    printf("        loop {\n");
    printf("            let mut changed = false;\n\n");
    printf("            match self.top {\n");
    for (int i = 0; i < state_count; i++) {
        StateInfo *tls = &state_table[i];
        if (strcmp(tls->parent, chart_name) != 0) continue;

        printf("                TopState::%s => {\n", cap_str(tls->name));
        int has_regions_here = 0;
        for (int r = 0; r < region_count; r++)
            if (strcmp(region_table[r].parent_state, tls->name) == 0) { has_regions_here=1; break; }

        if (has_regions_here) {
            for (int r = 0; r < region_count; r++) {
                RegionInfo *ri = &region_table[r];
                if (strcmp(ri->parent_state, tls->name) != 0) continue;

                char ename[300], fname[300];
                enum_name_for(ri->name, ename);
                field_name_for(ri->name, fname);
                printf("                    match self.%s {\n", fname);
                for (int j = 0; j < state_count; j++) {
                    StateInfo *cs = &state_table[j];
                    if (strcmp(cs->parent, ri->name) != 0) continue;
                    printf("                        %s::%s => {\n", ename, cap_str(cs->name));
                    for (int t = 0; t < trans_count; t++) {
                        TransInfo *tr = &trans_table[t];
                        if (strcmp(tr->from_state, cs->name) != 0 || strcmp(tr->from_parent, cs->parent) != 0) continue;
                        if (tr->has_if && tr->cond_var[0]) {
                            printf("                            if "); print_cond(tr); printf(" {\n");
                            if (tr->has_do && tr->do_stmt[0])
                                printf("                                %s\n", tr->do_stmt);
                            printf("                                self.%s = %s::%s;\n", fname, ename, cap_str(tr->to_state));
                            printf("                                changed = true;\n");
                            printf("                            }\n");
                        } else if (tr->is_auto) {
                            if (tr->has_do && tr->do_stmt[0])
                                printf("                            %s\n", tr->do_stmt);
                            printf("                            self.%s = %s::%s;\n", fname, ename, cap_str(tr->to_state));
                            printf("                            changed = true;\n");
                        }
                    }
                    printf("                        }\n");
                }
                printf("                    }\n\n");
            }

            printf("                    if ");
            int first = 1;
            for (int r = 0; r < region_count; r++) {
                RegionInfo *ri = &region_table[r];
                if (strcmp(ri->parent_state, tls->name) != 0) continue;
                char ename[300], fname[300];
                enum_name_for(ri->name, ename);
                field_name_for(ri->name, fname);
                const char *fin = final_child(ri->name);
                if (!first) printf("\n                        && ");
                printf("self.%s == %s::%s", fname, ename, cap_str(fin[0] ? fin : "Done"));
                first = 0;
            }
            const char *join_tgt = NULL;
            for (int t = 0; t < trans_count; t++)
                if (trans_table[t].is_join && trans_table[t].join_to[0]) { join_tgt = trans_table[t].join_to; break; }
            if (!join_tgt) join_tgt = top_fin && top_fin[0] ? top_fin : "Done";
            char *jt_cap = cap(join_tgt);
            printf(" {\n");
            printf("                        self.top = TopState::%s;\n", jt_cap);
            printf("                        changed = true;\n");
            printf("                    }\n");
            free(jt_cap);

        } else {
            if (tls->has_during && tls->during_stmt[0]) printf("                    %s\n", tls->during_stmt);
            if (child_count(tls->name) > 0) {
                char ename[300], fname[300];
                enum_name_for(tls->name, ename);
                field_name_for(tls->name, fname);

                printf("                    match self.%s {\n", fname);
                for (int j = 0; j < state_count; j++) {
                    StateInfo *ns = &state_table[j];
                    if (strcmp(ns->parent, tls->name) != 0) continue;
                    printf("                        %s::%s => {\n", ename, cap_str(ns->name));
                    if (ns->has_during && ns->during_stmt[0]) printf("                            %s\n", ns->during_stmt);
                    if (child_count(ns->name) > 0) {
                        char ename2[300], fname2[300];
                        enum_name_for(ns->name, ename2);
                        field_name_for(ns->name, fname2);

                        printf("                            match self.%s {\n", fname2);
                        for (int k = 0; k < state_count; k++) {
                            StateInfo *nns = &state_table[k];
                            if (strcmp(nns->parent, ns->name) != 0) continue;
                            printf("                                %s::%s => {\n", ename2, cap_str(nns->name));
                            if (nns->has_during && nns->during_stmt[0]) printf("                                    %s\n", nns->during_stmt);
                            for (int t = 0; t < trans_count; t++) {
                                TransInfo *tr = &trans_table[t];
                                if (strcmp(tr->from_state, nns->name) != 0 || strcmp(tr->from_parent, nns->parent) != 0) continue;
                                if (tr->is_immediate) {
                                    if (tr->has_do && tr->do_stmt[0]) printf("                                    %s\n", tr->do_stmt);
                                    printf("                                    self.%s = %s::%s;\n", fname2, ename2, cap_str(tr->to_state));
                                    printf("                                    changed = true;\n");
                                }
                            }
                            printf("                                }\n");
                        }
                        printf("                            }\n");
                    }

                    for (int t = 0; t < trans_count; t++) {
                        TransInfo *tr = &trans_table[t];
                        if (strcmp(tr->from_state, ns->name) != 0 || strcmp(tr->from_parent, ns->parent) != 0) continue;
                        if (tr->is_immediate) {
                            if (tr->has_do && tr->do_stmt[0]) printf("                            %s\n", tr->do_stmt);
                            printf("                            self.%s = %s::%s;\n", fname, ename, cap_str(tr->to_state));
                            printf("                            changed = true;\n");
                        }
                    }
                    printf("                        }\n");
                }
                printf("                    }\n");
            }

            for (int t = 0; t < trans_count; t++) {
                TransInfo *tr = &trans_table[t];
                if (strcmp(tr->from_state, tls->name) != 0 || strcmp(tr->from_parent, tls->parent) != 0) continue;
                
                if (tr->has_if && tr->cond_var[0]) {
                    printf("                    if "); print_cond(tr); printf(" {\n");
                    if (tr->has_do && tr->do_stmt[0])
                        printf("                        %s\n", tr->do_stmt);
                    printf("                        self.top = TopState::%s;\n", cap_str(tr->to_state));
                    printf("                        changed = true;\n");
                    printf("                    }\n");
                } else if (tr->is_auto) {
                    if (tr->has_do && tr->do_stmt[0]) printf("                    %s\n", tr->do_stmt);
                    printf("                    self.top = TopState::%s;\n", cap_str(tr->to_state));
                    printf("                    changed = true;\n");
                } else if (tr->is_delayed) {
                    char *l = lcase(tr->to_state);
                    printf("                    self.delayed_to_%s = true;\n", l);
                    free(l);
                }
            }
        }

        printf("                }\n\n");
    }

    printf("            }\n\n");
    printf("            if !changed { break; }\n");
    printf("        }\n"); 

    if (feat_has_delayed && !feat_has_deferred) {
        for (int i = 0; i < trans_count; i++) {
            TransInfo *t = &trans_table[i];
            if (!t->is_delayed) continue;
            char *l = lcase(t->to_state);
            printf("\n        if self.delayed_to_%s {\n", l);
            printf("            self.top = TopState::%s;\n", cap_str(t->to_state));
            printf("            self.delayed_to_%s = false;\n", l);
            printf("        }\n");
            free(l);
        }
    }

    if (feat_has_deferred) {
        printf("\n        if self.deferred_transition {\n");
        printf("            println!(\"Executing deferred transition\");\n");
        printf("            self.deferred_transition = false;\n");
        printf("            self.top = TopState::%s;\n", cap_str(top_init));
        for (int i = 0; i < state_count; i++) {
            if (child_count(state_table[i].name) == 0) continue;
            char ename[300], fname[300];
            enum_name_for(state_table[i].name, ename);
            field_name_for(state_table[i].name, fname);
            printf("            self.%s = %s::%s;\n", fname, ename, cap_str(initial_child(state_table[i].name)));
        }
        printf("        }\n");
    }

    printf("    }\n\n"); 

    if (top_fin && top_fin[0]) {
        printf("    fn is_final(&self) -> bool {\n");
        printf("        self.top == TopState::%s\n", cap_str(top_fin));
        printf("    }\n");
    }
    printf("}\n\n");

    printf("fn main() {\n");
    printf("    let mut m = Machine::new();\n\n");
    if (has_inputs) {
        printf("    for tick in 0..5 {\n");
        printf("        println!(\"Tick {}: {:?}\", tick, m.top);\n");
        printf("        m.tick();\n");
        printf("    }\n");
    } else {
        printf("    for tick in 0..5 {\n");
        printf("        println!(\"Tick {}: {:?}\", tick, m.top);\n");
        if (top_fin && top_fin[0])
            printf("        if m.is_final() { break; }\n");
        printf("        m.tick();\n");
        printf("    }\n");
    }
    printf("}\n");
}
%}

%union {
    char *str;
    int   num;
}

%token <str> ID
%token <num> NUMBER

%token SCCHART INPUT OUTPUT BOOL INT TOK_INITIAL FINAL STATE REGION
%token FOR TO IF GOTO DO JOIN ENTRY DURING IMMEDIATE DEFERRED HISTORY
%token SHALLOW AUTO DELAYED TRUE_VAL FALSE_VAL

%token EQEQ NEQ GEQ LEQ GT LT AND OR NOT EQ INC DEC

%token LBRACE RBRACE COLON COMMA SEMI

%left OR
%left AND
%left EQEQ NEQ
%left GT LT GEQ LEQ
%left '+' '-'
%left '*' '/'
%right NOT

%type <str> transition_cond cond_expr action_stmt action_stmts expr
%type <num> state_mod transition_mod

%%

program
    : SCCHART ID LBRACE
        { strncpy(chart_name,$2,255);
        push_ctx(chart_name); }
      elements RBRACE
        {
            generate_rust();
        }
    ;

elements
    : element elements
    |
    ;

element
    : decl
    | state_def
    | region_def
    | transition
    | action
    ;

decl
    : INPUT  BOOL input_ids_bool
    | INPUT  INT  input_ids_int
    | OUTPUT BOOL output_ids_bool
    | OUTPUT INT  output_ids_int
    ;

input_ids_bool
    : ID                         { add_var($1,"bool",0); }
    | ID COMMA input_ids_bool    { add_var($1,"bool",0); }
    ;
input_ids_int
    : ID                         { add_var($1,"int",0); }
    | ID COMMA input_ids_int     { add_var($1,"int",0); }
    ;
output_ids_bool
    : ID                         { add_var($1,"bool",1); }
    | ID COMMA output_ids_bool   { add_var($1,"bool",1); }
    ;
output_ids_int
    : ID                         { add_var($1,"int",1); }
    | ID COMMA output_ids_int    { add_var($1,"int",1); }
    ;

state_mod
    : TOK_INITIAL FINAL { $$ = 0x3; }
    | TOK_INITIAL       { $$ = 0x1; }
    | FINAL             { $$ = 0x2; }
    |                   { $$ = 0x0; }
    ;

state_def
    : state_mod STATE ID LBRACE
        {
            add_state_entry($3, cur_ctx(), $1 & 1, ($1>>1) & 1);
            set_last_peer($3);
            push_ctx($3);
        }
      elements RBRACE
        {
            pop_ctx();
        }

    | state_mod STATE ID
        {
            add_state_entry($3, cur_ctx(), $1 & 1, ($1>>1) & 1);
            set_last_peer($3);
        }
    ;

region_def
    : REGION ID LBRACE
        {
            RegionInfo *ri = &region_table[region_count++];
            strncpy(ri->name, $2, 255);
            strncpy(ri->parent_state, cur_ctx(), 255);
            push_ctx($2);
        }
      elements RBRACE
        {
            pop_ctx();
        }

    | REGION ID FOR ID COLON NUMBER TO NUMBER LBRACE
        {
            RegionInfo *ri = &region_table[region_count++];
            strncpy(ri->name, $2, 255);
            strncpy(ri->parent_state, cur_ctx(), 255);
            push_ctx($2);
        }
      elements RBRACE
        {
            pop_ctx();
        }
    ;

transition
    : IF transition_cond GOTO ID transition_mod
        { add_transition(1, $2, 0, 0, 0, 0, 0, NULL, $4, $5); free($2); free($4); }
    | IF transition_cond DO action_stmts GOTO ID transition_mod
        { add_transition(1, $2, 0, 0, 0, 0, 0, $4, $6, $7); free($2); free($4); free($6); }
    | IMMEDIATE IF transition_cond GOTO ID transition_mod
        { add_transition(1, $3, 1, 0, 0, 0, 0, NULL, $5, $6); free($3); free($5); }
    | IMMEDIATE IF transition_cond DO action_stmts GOTO ID transition_mod
        { add_transition(1, $3, 1, 0, 0, 0, 0, $5, $7, $8); free($3); free($5); free($7); }
    | NUMBER ID GOTO ID transition_mod
        { 
            char buf[256]; snprintf(buf, 256, "%d:%s", $1, $2);
            add_transition(1, buf, 0, 0, 0, 0, 0, NULL, $4, $5); 
            free($2); free($4); 
        }
    | NUMBER ID DO action_stmts GOTO ID transition_mod
        { 
            char buf[256]; snprintf(buf, 256, "%d:%s", $1, $2);
            add_transition(1, buf, 0, 0, 0, 0, 0, $4, $6, $7); 
            free($2); free($4); free($6); 
        }
    | GOTO ID transition_mod
        { add_transition(0, NULL, 0, 0, 0, 1, 0, NULL, $2, $3); free($2); }
    | AUTO GOTO ID transition_mod
        { add_transition(0, NULL, 0, 0, 1, 0, 0, NULL, $3, $4); free($3); }
    | DELAYED GOTO ID transition_mod
        { add_transition(0, NULL, 0, 1, 0, 0, 0, NULL, $3, $4); free($3); }
    | IMMEDIATE DO action_stmts GOTO ID transition_mod
        { add_transition(0, NULL, 1, 0, 0, 0, 0, $3, $5, $6); free($3); free($5); }
    | JOIN TO ID
        { add_transition(0, NULL, 0, 0, 0, 0, 1, NULL, $3, 0); free($3); }
    | DO action_stmts JOIN TO ID
        { add_transition(0, NULL, 0, 0, 0, 0, 1, $2, $5, 0); free($2); free($5); }
    ;

transition_mod
    : SHALLOW HISTORY { $$ = 1; }
    | HISTORY         { $$ = 2; }
    | DEFERRED        { $$ = 3; }
    |                 { $$ = 0; }
    ;

transition_cond
    : NUMBER ID     { char buf[512]; snprintf(buf,512,"%d:%s",$1,$2); $$=strdup(buf); free($2); }
    | cond_expr     { $$ = $1; }
    ;

cond_expr
    : cond_expr AND cond_expr { char buf[512]; snprintf(buf,512,"%s && %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | cond_expr OR cond_expr  { char buf[512]; snprintf(buf,512,"%s || %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | NOT cond_expr           { char buf[256]; snprintf(buf,256,"!%s",$2); $$=strdup(buf); free($2); }
    | '(' cond_expr ')'       { char buf[512]; snprintf(buf,512,"(%s)",$2); $$=strdup(buf); free($2); }
    | expr EQEQ expr          { char buf[512]; snprintf(buf,512,"%s == %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | expr NEQ expr           { char buf[512]; snprintf(buf,512,"%s != %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | expr GT expr            { char buf[512]; snprintf(buf,512,"%s > %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | expr LT expr            { char buf[512]; snprintf(buf,512,"%s < %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | expr GEQ expr           { char buf[512]; snprintf(buf,512,"%s >= %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | expr LEQ expr           { char buf[512]; snprintf(buf,512,"%s <= %s",$1,$3); $$=strdup(buf); free($1); free($3); }
    | ID                      { 
        char buf[256]; 
        if (is_input_var($1)) snprintf(buf,256,"self.inputs.%s",$1); 
        else snprintf(buf,256,"self.%s",$1);
        $$=strdup(buf); free($1); 
      }
    | TRUE_VAL  { $$ = strdup("true"); }
    | FALSE_VAL { $$ = strdup("false"); }
    ;

action
    : ENTRY  DO action_stmts
        {
            StateInfo *s = get_current_state();
            if (s) { s->has_entry = 1; strncpy(s->entry_stmt, $3, 511); }
            free($3);
        }
    | DURING DO action_stmts
        {
            StateInfo *s = get_current_state();
            if (s) { s->has_during = 1; strncpy(s->during_stmt, $3, 511); }
            free($3);
        }
    ;

action_stmts
    : action_stmt SEMI action_stmts
        {
            char buf[1024];
            snprintf(buf, 1024, "%s %s", $1, $3);
            $$ = strdup(buf);
            free($1); free($3);
        }
    | action_stmt
        { $$ = $1; }
    ;

action_stmt
    : ID EQ expr  { 
        char buf[512]; 
        if (is_input_var($1)) snprintf(buf,512,"self.inputs.%s = %s;",$1,$3); 
        else snprintf(buf,512,"self.%s = %s;",$1,$3); 
        $$=strdup(buf); free($1); free($3); 
      }
    | ID INC      { 
        char buf[512]; 
        if (is_input_var($1)) snprintf(buf,512,"self.inputs.%s += 1;",$1); 
        else snprintf(buf,512,"self.%s += 1;",$1); 
        $$=strdup(buf); free($1); 
      }
    | ID DEC      { 
        char buf[512]; 
        if (is_input_var($1)) snprintf(buf,512,"self.inputs.%s -= 1;",$1); 
        else snprintf(buf,512,"self.%s -= 1;",$1); 
        $$=strdup(buf); free($1); 
      }
    ;

expr
    : NUMBER    { char buf[64]; snprintf(buf,64,"%d",$1); $$ = strdup(buf); }
    | ID        { 
        char buf[256]; 
        if (is_input_var($1)) snprintf(buf,256,"self.inputs.%s",$1); 
        else snprintf(buf,256,"self.%s",$1);
        $$=strdup(buf); free($1); 
      }
    | expr '+' expr { char buf[512]; snprintf(buf,512,"%s + %s",$1,$3); $$ = strdup(buf); free($1); free($3); }
    | expr '-' expr { char buf[512]; snprintf(buf,512,"%s - %s",$1,$3); $$ = strdup(buf); free($1); free($3); }
    | expr '*' expr { char buf[512]; snprintf(buf,512,"%s * %s",$1,$3); $$ = strdup(buf); free($1); free($3); }
    | expr '/' expr { char buf[512]; snprintf(buf,512,"%s / %s",$1,$3); $$ = strdup(buf); free($1); free($3); }
    | '(' expr ')'  { char buf[512]; snprintf(buf,512,"(%s)",$2); $$=strdup(buf); free($2); }
    | TRUE_VAL  { $$ = strdup("true"); }
    | FALSE_VAL { $$ = strdup("false"); }
    ;

%%

void yyerror(const char *s) {
    fprintf(stderr, "Error at line %d: %s near '%s'\n", yylineno, s, yytext);
}

int main(int argc, char **argv) {
    if (argc > 1) {
        FILE *file = fopen(argv[1], "r");
        if (!file) { perror("Could not open file"); return 1; }
        extern FILE *yyin;
        yyin = file;
    }
    return yyparse();
}