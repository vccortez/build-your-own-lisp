#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <math.h>
#include <editline.h>
#include "mpc.h"

#define LASSERT(args, cond, fmt, ...) \
  if (!(cond)) { lval* err = lval_err(fmt, ##__VA_ARGS__); lval_del(args); return err; }

#define ASSERT_TYPE(func, args, index, expected) \
  LASSERT(args, args->cell[index]->type == expected, "function '%s': argument [%i] should be '%s', got '%s'", func, index, ltype_name(expected), ltype_name(args->cell[index]->type));

#define ASSERT_COUNT(func, args, expected) \
  LASSERT(args, args->count == expected, "function '%s': expected '%i' arguments, got '%i'", func, expected, args->count);

#define ASSERT_FULL(func, args, index) \
  LASSERT(args, args->cell[index]->count != 0, "function '%s': argument [%i] should not be empty", func, index);

// forward declarations
struct LispyValue;
struct LispyEnvironment;
typedef struct LispyValue lval;
typedef struct LispyEnvironment lenv;

// lispy value
enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_FUN, LVAL_SEXPR, LVAL_QEXPR };
enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

typedef lval*(*lbuiltin)(lenv*, lval*);

struct LispyValue {
  int type;
  double num;
  // error and symbol are strings
  char* err;
  char* sym;
  lbuiltin fun;
  // count and pointer to list of "lval"
  int count;
  lval** cell;
};

struct LispyEnvironment {
  int count;
  char** syms;
  lval** vals;
};

int on_exit();
void signal_handler();

lenv* lenv_new(void);
void lenv_del(lenv*);
lval* lenv_get(lenv*, lval*);
void lenv_put(lenv*, lval*, lval*);

lval* lval_add(lval*, lval*);
void lval_del(lval*);
lval* lval_copy(lval*);

lval* lval_read(mpc_ast_t*);
lval* lval_read_num(mpc_ast_t*);

lval* lval_eval(lenv*, lval*);
lval* lval_eval_sexpr(lenv*, lval*);
lval* lval_pop(lval*, int);
lval* lval_take(lval*, int);
lval* lval_join(lval*, lval*);

void lenv_add_builtin(lenv*, char*, lbuiltin);
void lenv_register_builtins(lenv*);

lval* builtin_def(lenv*, lval*);
lval* builtin_op(lenv*, lval*, char*);
lval* builtin_add(lenv*, lval*);
lval* builtin_sub(lenv*, lval*);
lval* builtin_mul(lenv*, lval*);
lval* builtin_div(lenv*, lval*);
lval* builtin_mod(lenv*, lval*);
lval* builtin_exp(lenv*, lval*);
lval* builtin_min(lenv*, lval*);
lval* builtin_max(lenv*, lval*);
lval* builtin_head(lenv*, lval*);
lval* builtin_tail(lenv*, lval*);
lval* builtin_list(lenv*, lval*);
lval* builtin_eval(lenv*, lval*);
lval* builtin_join(lenv*, lval*);

lval* lval_num(double);
lval* lval_err(char*, ...);
lval* lval_sym(char*);
lval* lval_sexpr(void);
lval* lval_qexpr(void);
lval* lval_fun(lbuiltin);

void lval_expr_print(lval*, char, char);
void lval_print(lval*);
void lval_println(lval*);
char* ltype_name(int);

int main() {
  signal(SIGINT, signal_handler);

  // create parsers
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr  = mpc_new("sexpr");
  mpc_parser_t* Qexpr  = mpc_new("qexpr");
  mpc_parser_t* Expr   = mpc_new("expr");
  mpc_parser_t* Lispy  = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
      "                                                                    \
      number : /-?[0-9]+[.]?[0-9]*/ ;                                      \
      symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&%^]+/ ;                        \
      sexpr  : '(' <expr>* ')' ;                                           \
      qexpr  : '{' <expr>* '}' ;                                           \
      expr   : <number> | <symbol> | <sexpr> | <qexpr> ;                   \
      lispy  : /^/ <expr>* /$/ ;                                           \
      ",
      Number, Symbol, Sexpr, Qexpr, Expr, Lispy);
  // version and exit information
  puts("> lispy version 0.0.1");
  puts("> press ctrl+c to exit");

  lenv* e = lenv_new();
  lenv_register_builtins(e);

  while (1) {
    // output prompt and get input
    char* input = readline("lispy > ");

    if (strcmp("exit", input) == 0) {
      free(input);
      break;
    }
    // add input to history
    add_history(input);

    // attempt to parse user input
    mpc_result_t r;
    if (mpc_parse("<stdin> ", input, Lispy, &r)) {
      lval* answer = lval_eval(e, lval_read(r.output));
      lval_println(answer);
      lval_del(answer);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }

    // free input data
    free(input);
  }

  lenv_del(e);
  mpc_cleanup(6, Number, Symbol, Sexpr, Qexpr, Expr, Lispy);

  return on_exit();
}

lval* lval_eval_sexpr(lenv* e, lval* v) {
  // evaluate children
  for (int i = 0; i < v->count; ++i) {
    v->cell[i] = lval_eval(e, v->cell[i]);
  }

  // error checking
  for (int i = 0; i < v->count; ++i) {
    if (v->cell[i]->type == LVAL_ERR) {
      return lval_take(v, i);
    }
  }

  // empty expression
  if (v->count == 0) {
    return v;
  }

  // single expression
  if (v->count == 1) {
    return lval_take(v, 0);
  }

  // ensure first element is function
  lval* f = lval_pop(v, 0);
  if (f->type != LVAL_FUN) {
    lval_del(v);
    lval_del(f);
    return lval_err("first element is not a function");
  }

  // call function to get result
  lval* result = f->fun(e, v);
  lval_del(f);
  return result;
}

lval* lval_eval(lenv* e, lval* v) {
  if (v->type == LVAL_SYM) {
    lval* x = lenv_get(e, v);
    lval_del(v);
    return x;
  }
  // evaluate if s-expressions
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(e, v);
  }
  // else return itself
  return v;
}

lval* lval_pop(lval* v, int i) {
  // find item at 'i'
  lval* x = v->cell[i];

  // shift memory after the item 'i' over the top
  memmove(&v->cell[i], &v->cell[i+1], sizeof(lval*) * (v->count-i-1));

  // decrease the item count
  v->count--;

  // reallocate the memory
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  return x;
}

lval* lval_take(lval* v, int i) {
  lval* x = lval_pop(v, i);
  lval_del(v);
  return x;
}

void lenv_add_builtin(lenv* e, char* name, lbuiltin func) {
  lval* k = lval_sym(name);
  lval* v = lval_fun(func);
  lenv_put(e, k, v);
  lval_del(k);
  lval_del(v);
}

void lenv_register_builtins(lenv* e) {
  // variable functions
  lenv_add_builtin(e, "def", builtin_def);
  // list functions
  lenv_add_builtin(e, "list", builtin_list);
  lenv_add_builtin(e, "head", builtin_head);
  lenv_add_builtin(e, "tail", builtin_tail);
  lenv_add_builtin(e, "eval", builtin_eval);
  lenv_add_builtin(e, "join", builtin_join);

  // math operators
  lenv_add_builtin(e, "+", builtin_add);
  lenv_add_builtin(e, "-", builtin_sub);
  lenv_add_builtin(e, "*", builtin_mul);
  lenv_add_builtin(e, "/", builtin_div);
  lenv_add_builtin(e, "%", builtin_mod);
  lenv_add_builtin(e, "^", builtin_exp);
  lenv_add_builtin(e, "min", builtin_min);
  lenv_add_builtin(e, "max", builtin_max);
}

lval* builtin_def(lenv* e, lval* a) {
  ASSERT_TYPE("def", a, 0, LVAL_QEXPR);

  // first argument is symbol list
  lval* syms = a->cell[0];

  // ensure all elements of first list are symbols
  for (int i = 0; i < syms->count; ++i) {
    ASSERT_TYPE("def>arg", syms, i, LVAL_SYM);
  }

  // check correct number of symbols and values
  ASSERT_COUNT("def>arg", syms, a->count - 1);

  // assign copies of values to symbols
  for (int i = 0; i < syms->count; ++i) {
    lenv_put(e, syms->cell[i], a->cell[i+1]);
  }

  lval_del(a);
  return lval_sexpr();
}

lval* builtin_op(lenv* e, lval* a, char* op) {
  // ensure all are numbers
  for (int i = 0; i < a->count; ++i) {
    ASSERT_TYPE(op, a, i, LVAL_NUM);
  }

  // pop first element
  lval* x = lval_pop(a, 0);

  // if no more args and subtracting then negate
  if ((strcmp(op, "-") == 0) && a->count == 0) {
    x->num *= -1;
  }

  // while there are other elements
  while(a->count > 0) {
    // pop next element
    lval* y = lval_pop(a, 0);

    if (strcmp(op, "+") == 0) { x->num += y->num; }
    if (strcmp(op, "-") == 0) { x->num -= y->num; }
    if (strcmp(op, "*") == 0) { x->num *= y->num; }
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        lval_del(x);
        lval_del(y);
        x = lval_err("function '%s': attempted to divide by zero", op);
        break;
      }
      x->num /= y->num;
    }
    if (strcmp(op, "%") == 0) {
      if (y->num == 0) {
        lval_del(x);
        lval_del(y);
        x = lval_err("function '%s': attempted to divide by zero", op);
        break;
      }
      x->num = fmod(x->num, y->num);
    }
    if (strcmp(op, "^") == 0) { x->num = pow(x->num, y->num); }
    lval_del(y);
  }

  lval_del(a);
  return x;
}

lval* builtin_add(lenv* e, lval* a) {
  return builtin_op(e, a, "+");
}

lval* builtin_sub(lenv* e, lval* a) {
  return builtin_op(e, a, "-");
}

lval* builtin_mul(lenv* e, lval* a) {
  return builtin_op(e, a, "*");
}

lval* builtin_div(lenv* e, lval* a) {
  return builtin_op(e, a, "/");
}

lval* builtin_mod(lenv* e, lval* a) {
  return builtin_op(e, a, "%");
}

lval* builtin_exp(lenv* e, lval* a) {
  return builtin_op(e, a, "^");
}

lval* builtin_min(lenv* e, lval* a) {
  // ensure all are numbers
  for (int i = 0; i < a->count; ++i) {
    ASSERT_TYPE("min", a, i, LVAL_NUM);
  }

  // pop first element
  lval* x = lval_pop(a, 0);

  while (a->count > 0) {
    // pop next element
    lval* y = lval_pop(a, 0);
    x->num = fmin(x->num, y->num);
    lval_del(y);
  }

  lval_del(a);
  return x;
}

lval* builtin_max(lenv* e, lval* a) {
  // ensure all are numbers
  for (int i = 0; i < a->count; ++i) {
    ASSERT_TYPE("max", a, i, LVAL_NUM);
  }

  // pop first element
  lval* x = lval_pop(a, 0);

  while (a->count > 0) {
    // pop next element
    lval* y = lval_pop(a, 0);
    x->num = fmax(x->num, y->num);
    lval_del(y);
  }

  lval_del(a);
  return x;
}

lval* builtin_head(lenv* e, lval* a) {
  // check error conditions
  ASSERT_COUNT("head", a, 1);
  ASSERT_TYPE("head", a, 0, LVAL_QEXPR);
  ASSERT_FULL("head", a, 0);

  // otherwise take first argument
  lval* v = lval_take(a, 0);

  // delete other elements
  while (v->count > 1) { lval_del(lval_pop(v, 1)); }
  return v;
}

lval* builtin_tail(lenv* e, lval* a) {
  // check error conditions
  ASSERT_COUNT("tail", a, 1);
  ASSERT_TYPE("tail", a, 0, LVAL_QEXPR);
  ASSERT_FULL("tail", a, 0);

  // otherwise take first argument
  lval* v = lval_take(a, 0);

  // delete first element and return
  lval_del(lval_pop(v, 0));
  return v;
}

lval* builtin_list(lenv* e, lval* a) {
  a->type = LVAL_QEXPR;
  return a;
}

lval* builtin_eval(lenv* e, lval* a) {
  ASSERT_COUNT("eval", a, 1);
  ASSERT_TYPE("eval", a, 0, LVAL_QEXPR);

  lval* x = lval_take(a, 0);
  x->type = LVAL_SEXPR;
  return lval_eval(e, x);
}

lval* builtin_join(lenv* e, lval* a) {
  for (int i = 0; i < a->count; ++i) {
    ASSERT_TYPE("join", a, i, LVAL_QEXPR);
  }

  lval* x = lval_pop(a, 0);

  while (a->count) {
    x = lval_join(x, lval_pop(a, 0));
  }

  lval_del(a);
  return x;
}

lval* lval_join(lval* x, lval* y) {
  // for each cell in 'y' add it to 'x'
  while (y->count) {
    x = lval_add(x, lval_pop(y, 0));
  }

  // delete the empty 'y' and return 'x'
  lval_del(y);
  return x;
}

lval* lval_num(double x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;
  return v;
}

lval* lval_err(char* fmt, ...) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;

  // create va_list and initialize it
  va_list va;
  va_start(va, fmt);

  // allocate 512 bytes
  v->err = malloc(512);

  // printf the error string
  vsnprintf(v->err, 511, fmt, va);

  // reallocate to bytes used
  v->err = realloc(v->err, strlen(v->err) + 1);

  // clean va_list
  va_end(va);

  return v;
}

lval* lval_sym(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SYM;
  v->sym = malloc(strlen(s) + 1);
  strcpy(v->sym, s);
  return v;
}

lval* lval_sexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_SEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

lval* lval_qexpr(void) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_QEXPR;
  v->count = 0;
  v->cell = NULL;
  return v;
}

lval* lval_fun(lbuiltin func) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->fun = func;
  return v;
}

lval* lval_read_num(mpc_ast_t* t) {
  errno = 0;
  double x = strtod(t->contents, NULL);
  return errno != ERANGE ?
    lval_num(x) : lval_err("invalid number");
}

lval* lval_read(mpc_ast_t* t) {
  // convert if symbol or number
  if (strstr(t->tag, "number")) { return lval_read_num(t); }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }

  // if root (>) or sexpr then init list
  lval* x = NULL;
  if (strcmp(t->tag, ">") == 0) { x = lval_sexpr(); }
  if (strstr(t->tag, "sexpr")) { x = lval_sexpr(); }
  if (strstr(t->tag, "qexpr")) { x = lval_qexpr(); }

  // fill list with valid expressions in it
  for (int i = 0; i < t->children_num; i++) {
    if (strcmp(t->children[i]->contents, "(") == 0) { continue; }
    if (strcmp(t->children[i]->contents, ")") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "}") == 0) { continue; }
    if (strcmp(t->children[i]->contents, "{") == 0) { continue; }
    if (strcmp(t->children[i]->tag, "regex") == 0) { continue; }
    x = lval_add(x, lval_read(t->children[i]));
  }

  return x;
}

lval* lval_add(lval* v, lval* x) {
  v->count++;
  v->cell = realloc(v->cell, sizeof(lval*) * v->count);
  v->cell[v->count-1] = x;
  return v;
}

void lval_del(lval* v) {
  switch (v->type) {
    case LVAL_NUM:
      break;

    case LVAL_ERR:
      free(v->err);
      break;

    case LVAL_SYM:
      free(v->sym);
      break;

    case LVAL_FUN:
      break;

    case LVAL_QEXPR:
    case LVAL_SEXPR:
      for (int i = 0; i < v->count; ++i) {
        lval_del(v->cell[i]);
      }

      free(v->cell);
      break;
  }

  free(v);
}

lval* lval_copy(lval* v) {
  lval* x = malloc(sizeof(lval));

  x->type = v->type;

  switch(v->type) {
    // copy functions and numbers directly
    case LVAL_NUM:
      x->num = v->num;
      break;
    case LVAL_FUN:
      x->fun = v->fun;
      break;
      // copy strings using malloc and strcpy
    case LVAL_ERR:
      x->err = malloc(strlen(v->err) + 1);
      strcpy(x->err, v->err);
      break;
    case LVAL_SYM:
      x->sym = malloc(strlen(v->sym) + 1);
      strcpy(x->sym, v->sym);
      break;
      // copy lists by copying each sub-expression
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      x->count = v->count;
      x->cell = malloc(sizeof(lval*) * x->count);
      for (int i = 0; i < x->count; i++) {
        x->cell[i] = lval_copy(v->cell[i]);
      }
      break;
  }

  return x;
}

lenv* lenv_new(void) {
  lenv* e = malloc(sizeof(lenv));
  e->count = 0;
  e->syms = NULL;
  e->vals = NULL;
  return e;
}

void lenv_del(lenv* e) {
  for (int i = 0; i < e->count; ++i) {
    free(e->syms[i]);
    lval_del(e->vals[i]);
  }
  free(e->syms);
  free(e->vals);
  free(e);
}

lval* lenv_get(lenv* e, lval* k) {
  // iterate over all items in environment
  for (int i = 0; i < e->count; i++) {
    // check if the stored string matches the symbol string
    // if it does, return a copy of the value
    if (strcmp(e->syms[i], k->sym) == 0) {
      return lval_copy(e->vals[i]);
    }
  }
  // if no symbol found return error
  return lval_err("unbound symbol: %s", k->sym);
}

void lenv_put(lenv* e, lval* k, lval* v) {
  // iterate over all items in environment
  // this is to see if variable already exists
  for (int i = 0; i < e->count; i++) {
    // if variable is found delete item at that position
    // and replace with variable supplied by user
    if (strcmp(e->syms[i], k->sym) == 0) {
      lval_del(e->vals[i]);
      e->vals[i] = lval_copy(v);
      return;
    }
  }
  // if no existing entry found allocate space for new entry
  e->count++;
  e->vals = realloc(e->vals, sizeof(lval*) * e->count);
  e->syms = realloc(e->syms, sizeof(char*) * e->count);

  // copy contents of lval and symbol string into new location
  e->vals[e->count-1] = lval_copy(v);
  e->syms[e->count-1] = malloc(strlen(k->sym)+1);
  strcpy(e->syms[e->count-1], k->sym);
}

void lval_expr_print(lval* v, char open, char close) {
  putchar(open);
  for (int i = 0; i < v->count; ++i) {
    // print value
    lval_print(v->cell[i]);
    // dont print trailing space if last element
    if (i != (v->count-1)) {
      putchar(' ');
    }
  }
  putchar(close);
}

void lval_print(lval* v) {
  switch (v->type) {
    case LVAL_NUM:
      printf("%g", v->num);
      break;

    case LVAL_ERR:
      printf("error: %s", v->err);
      break;

    case LVAL_SYM:
      printf("%s", v->sym);
      break;

    case LVAL_FUN:
      printf("<function>");
      break;

    case LVAL_SEXPR:
      lval_expr_print(v, '(', ')');
      break;

    case LVAL_QEXPR:
      lval_expr_print(v, '{', '}');
      break;
  }
}

void lval_println(lval* v) {
  putchar('>');
  putchar(' ');
  lval_print(v);
  putchar('\n');
}

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "function";
    case LVAL_NUM: return "number";
    case LVAL_ERR: return "error";
    case LVAL_SYM: return "symbol";
    case LVAL_QEXPR: return "q-expression";
    case LVAL_SEXPR: return "s-expression";
    default: return "unknown";
  }
}

void signal_handler() {
  exit(on_exit());
}

int on_exit() {
  puts("> bye bye!");
  return 0;
}
