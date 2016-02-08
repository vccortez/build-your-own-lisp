#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>

#include "mpc.h"
#include "lispy.h"

enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_STR,
  LVAL_FUN, LVAL_SEXPR, LVAL_QEXPR } ;
enum { LNUM_DEC, LNUM_INT };

static mpc_parser_t* Integer;
static mpc_parser_t* Decimal;
static mpc_parser_t* String;
static mpc_parser_t* Comment;
static mpc_parser_t* Number;
static mpc_parser_t* Symbol;
static mpc_parser_t* Sexpr;
static mpc_parser_t* Qexpr;
static mpc_parser_t* Expr;
static mpc_parser_t* Lispy;

static lenv* lenv_new(void);
static void  lenv_del(lenv*);
static lval* lenv_get(lenv*, lval*);
static lenv* lenv_copy(lenv*);

static void  lenv_put(lenv*, lval*, lval*);
static void  lenv_def(lenv*, lval*, lval*);

static lval* lval_add(lval*, lval*);
static void  lval_del(lval*);
static lval* lval_copy(lval*);

static lval* lval_read(mpc_ast_t*);
static lval* lval_read_num(mpc_ast_t*, int);
static lval* lval_read_str(mpc_ast_t*);

static lval* lval_eval(lenv*, lval*);
static lval* lval_eval_sexpr(lenv*, lval*);
static lval* lval_pop(lval*, int);
static lval* lval_take(lval*, int);
static lval* lval_join(lval*, lval*);
static lval* lval_call(lenv*, lval*, lval*);
static int   lval_eq(lval*, lval*);

static void lenv_add_builtin(lenv*, char*, lbuiltin, char*);
static void lenv_register_builtins(lenv*);

static lval* builtin_var(lenv*, lval*, char*);
static lval* builtin_def(lenv*, lval*);
static lval* builtin_put(lenv*, lval*);

static lval* builtin_lambda(lenv*, lval*);
static lval* builtin_unpack(lenv*, lval*);

static lval* builtin_op(lenv*, lval*, char*);
static lval* builtin_add(lenv*, lval*);
static lval* builtin_sub(lenv*, lval*);
static lval* builtin_mul(lenv*, lval*);
static lval* builtin_div(lenv*, lval*);
static lval* builtin_mod(lenv*, lval*);
static lval* builtin_exp(lenv*, lval*);

static lval* builtin_head(lenv*, lval*);
static lval* builtin_tail(lenv*, lval*);
static lval* builtin_list(lenv*, lval*);
static lval* builtin_eval(lenv*, lval*);
static lval* builtin_join(lenv*, lval*);

static lval* builtin_gt(lenv*, lval*);
static lval* builtin_lt(lenv*, lval*);
static lval* builtin_ge(lenv*, lval*);
static lval* builtin_le(lenv*, lval*);
static lval* builtin_ord(lenv*, lval*, char*);

static lval* builtin_cmp(lenv*, lval*, char*);
static lval* builtin_eq(lenv*, lval*);
static lval* builtin_ne(lenv*, lval*);
static lval* builtin_if(lenv*, lval*);

static lval* builtin_load(lenv*, lval*);
static lval* builtin_print(lenv*, lval*);
static lval* builtin_error(lenv*, lval*);

static lval* lval_num(double, int);
static lval* lval_err(char*, ...);
static lval* lval_sym(char*);
static lval* lval_str(char*);
static lval* lval_sexpr(void);
static lval* lval_qexpr(void);
static lval* lval_fun(lbuiltin, char*);
static lval* lval_lambda(lval*, lval*);

static char* ltype_name(int);

static void lval_print(lval*);
static void lval_println(lval*);
static void lval_print_str(lval*);
static void lval_print_expr(lval*, char, char);

#define IF_ISNT(args, cond, fmt, ...) \
  if (!(cond)) { lval* err = lval_err(fmt, ##__VA_ARGS__); lval_del(args); return err; }

#define IF_IS(args, cond, fmt, ...) \
  if ((cond)) { lval* err = lval_err(fmt, ##__VA_ARGS__); lval_del(args); return err; }

#define ASSERT_TYPE(func, args, index, expected) \
  IF_ISNT(args, args->cell[index]->type == expected, "function '%s': argument [%i] should be '%s', got '%s'", func, index, ltype_name(expected), ltype_name(args->cell[index]->type));

#define ASSERT_COUNT(func, args, expected) \
  IF_ISNT(args, args->count == expected, "function '%s': expected '%i' argument(s), got '%i'", func, expected, args->count);

#define TEST_COUNT(func, args, sub, expected, aarg, barg) \
  IF_IS(args, sub->count == expected, "function '%s': expected '%i' argument(s), got '%i'", func, aarg, barg);

#define ASSERT_MATCH(func, args, value, expected, aname, bname) \
  IF_ISNT(args, value == expected, "function '%s': expected '%s' (%i) to match '%s' (%i)", func, aname, value, bname, expected);

#define ASSERT_FULL(func, args, index) \
  IF_ISNT(args, args->cell[index]->count != 0, "function '%s': argument [%i] should not be empty", func, index);

lenv* lispy_init(void) {
  // init parsers
  Integer = mpc_new("integer");
  Decimal = mpc_new("decimal");
  String  = mpc_new("string");
  Comment = mpc_new("comment");
  Number  = mpc_new("number");
  Symbol  = mpc_new("symbol");
  Sexpr   = mpc_new("sexpr");
  Qexpr   = mpc_new("qexpr");
  Expr    = mpc_new("expr");
  Lispy   = mpc_new("lispy");

  // create grammar
  mpca_lang(MPCA_LANG_DEFAULT,
      "                                                        \
      decimal : /-?[0-9]+[.][0-9]+/ ;                          \
      integer : /-?[0-9]+/ ;                                   \
      number : <decimal> | <integer> ;                         \
      symbol : /[a-zA-Z0-9_+\\-*\\/\\\\=<>!&%^]+/ ;            \
      string :  /\"(\\\\.|[^\"])*\"/ ;                         \
      comment :  /;[^\\r\\n]*/ ;                               \
      sexpr  : '(' <expr>* ')' ;                               \
      qexpr  : '{' <expr>* '}' ;                               \
      expr   : <number> | <symbol> | <string>                  \
      |        <sexpr> | <qexpr> | <comment> ;                 \
      lispy  : /^/ <expr>* /$/ ;                               \
      ",
      Decimal, Integer, Number, Symbol, String,
      Comment, Sexpr, Qexpr, Expr, Lispy);

  // create environment and register builtins
  lenv* env = lenv_new();
  lenv_register_builtins(env);

  // add standard library and load it
  lval* lib = lval_add(lval_sexpr(), lval_str("./stdlib.lsp"));
  lval* result = builtin_load(env, lib);

  // if the result is an error be sure to print
  if (result->type == LVAL_ERR) {
    lval_println(result);
  }

  lval_del(result);

  return env;
}

void lispy_parse(lenv* env, char* input) {
  mpc_result_t result;

  // parse user input
  if (mpc_parse("<stdin> ", input, Lispy, &result)) {
    lval* answer = lval_eval(env, lval_read(result.output));

    lval_println(answer);
    lval_del(answer);

    mpc_ast_delete(result.output);
  } else {
    mpc_err_print(result.error);
    mpc_err_delete(result.error);
  }
}

void lispy_exec(lenv* env, char* input) {
  lval* file = lval_add(lval_sexpr(), lval_str(input));

  lval* result = builtin_load(env, file);

  if (result->type == LVAL_ERR) {
    lval_println(result);
  }

  lval_del(result);
}

void lispy_clean(lenv* env) {
  lenv_del(env);

  mpc_cleanup(10, Integer, Decimal, Number, Symbol, String,
      Sexpr, Qexpr, Expr, Comment, Lispy);
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

  // expression has no operator, return empty
  if (v->cell[0]->type != LVAL_FUN) {
    lval_del(v);
    return lval_sexpr();
  }

  // otherwise call function and return result
  lval* f = lval_pop(v, 0);
  lval* result = lval_call(e, f, v);
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

void lenv_add_builtin(lenv* e, char* id, lbuiltin func, char* name) {
  lval* k = lval_sym(id);
  lval* v = lval_fun(func, name);
  lenv_put(e, k, v);
  lval_del(k);
  lval_del(v);
}

void lenv_register_builtins(lenv* e) {
  // variable functions
  lenv_add_builtin(e, "\\", builtin_lambda, "lambda");
  lenv_add_builtin(e, "def", builtin_def, "global_define");
  lenv_add_builtin(e, "=", builtin_put, "local_define");

  // string functions
  lenv_add_builtin(e, "load", builtin_load, "load");
  lenv_add_builtin(e, "error", builtin_error, "error");
  lenv_add_builtin(e, "print", builtin_print, "print");

  // comparison functions
  lenv_add_builtin(e, "if", builtin_if, "if");
  lenv_add_builtin(e, "==", builtin_eq, "equals");
  lenv_add_builtin(e, "!=", builtin_ne, "not_equals");
  lenv_add_builtin(e, ">", builtin_gt, "greater_than");
  lenv_add_builtin(e, "<", builtin_lt, "lower_than");
  lenv_add_builtin(e, ">=", builtin_ge, "greater_equals");
  lenv_add_builtin(e, "<=", builtin_le, "lower_equals");

  // list functions
  lenv_add_builtin(e, "list", builtin_list, "list");
  lenv_add_builtin(e, "unpack", builtin_unpack, "unpack");
  lenv_add_builtin(e, "head", builtin_head, "head");
  lenv_add_builtin(e, "tail", builtin_tail, "tail");
  lenv_add_builtin(e, "eval", builtin_eval, "eval");
  lenv_add_builtin(e, "join", builtin_join, "join");

  // math operators
  lenv_add_builtin(e, "+", builtin_add, "add");
  lenv_add_builtin(e, "-", builtin_sub, "subtract");
  lenv_add_builtin(e, "*", builtin_mul, "multiply");
  lenv_add_builtin(e, "/", builtin_div, "divide");
  lenv_add_builtin(e, "%", builtin_mod, "modulus");
  lenv_add_builtin(e, "^", builtin_exp, "exponential");
}

lval* builtin_var(lenv* e, lval* a, char* func) {
  ASSERT_TYPE("def", a, 0, LVAL_QEXPR);

  // first argument is symbol list
  lval* syms = a->cell[0];

  // ensure all elements of first list are symbols
  for (int i = 0; i < syms->count; ++i) {
    ASSERT_TYPE("var{args}", syms, i, LVAL_SYM);
  }

  // check correct number of symbols and values
  ASSERT_MATCH("var{args}", syms, syms->count, a->count - 1, "symbols", "values");

  // assign copies of values to symbols
  for (int i = 0; i < syms->count; ++i) {
    if (strcmp(func, "def") == 0) {
      lenv_def(e, syms->cell[i], a->cell[i+1]);
    }

    if (strcmp(func, "=") == 0) {
      lenv_put(e, syms->cell[i], a->cell[i+1]);
    }
  }

  lval_del(a);
  return lval_sexpr();
}

lval* builtin_def(lenv* e, lval* a) {
  return builtin_var(e, a, "def");
}

lval* builtin_put(lenv* e, lval* a) {
  return builtin_var(e, a, "=");
}

lval* builtin_if(lenv* e, lval* a) {
  ASSERT_COUNT("if", a, 3);
  ASSERT_TYPE("if", a, 0, LVAL_NUM);
  ASSERT_TYPE("if", a, 1, LVAL_QEXPR);
  ASSERT_TYPE("if", a, 2, LVAL_QEXPR);

  // mark q-expressions as evaluable
  a->cell[1]->type = LVAL_SEXPR;
  a->cell[2]->type = LVAL_SEXPR;

  lval* x;
  if (a->cell[0]->num) {
    // if true then eval first expression
    x = lval_eval(e, lval_pop(a, 1));
  } else {
    x = lval_eval(e, lval_pop(a, 2));
  }

  lval_del(a);
  return x;
}

lval* builtin_load(lenv* e, lval* a) {
  ASSERT_COUNT("load", a, 1);
  ASSERT_TYPE("load", a, 0, LVAL_STR);

  // parse file given by string name
  mpc_result_t r;
  if (mpc_parse_contents(a->cell[0]->str, Lispy, &r)) {
    // read contents
    lval* expr = lval_read(r.output);
    mpc_ast_delete(r.output);

    // evaluate each expression
    while (expr->count) {
      lval* x = lval_eval(e, lval_pop(expr, 0));
      // if evaluation leads to error, print it
      if (x->type == LVAL_ERR) { lval_println(x); }
      lval_del(x);
    }
    // delete expressions and arguments
    lval_del(expr);
    lval_del(a);

    // return empty list
    return lval_sexpr();
  } else {
    // get parse error as string
    char* err_msg = mpc_err_string(r.error);
    mpc_err_delete(r.error);
    // create new error message using it
    lval* err = lval_err("could not load library %s", err_msg);

    free(err_msg);
    lval_del(a);
    return err;
  }
}

lval* builtin_print(lenv* e, lval* a) {
  // print each argument followed by a space
  for (int i = 0; i < a->count; ++i) {
    lval_print(a->cell[i]);
    putchar(' ');
  }
  // print a newline and delete arguments
  putchar('\n');
  lval_del(a);

  return lval_sexpr();
}

lval* builtin_error(lenv* e, lval* a) {
  ASSERT_COUNT("error", a, 1);
  ASSERT_TYPE("error", a, 0, LVAL_STR);
  // construct error from first arg
  lval* err = lval_err(a->cell[0]->str);
  // clean up and return
  lval_del(a);

  return err;
}

lval* builtin_unpack(lenv* e, lval* a) {
  ASSERT_COUNT("unpack", a, 1);
  ASSERT_TYPE("unpack", a, 0, LVAL_QEXPR);
  ASSERT_FULL("unpack", a, 0);

  lval* v = lval_take(a, 0);
  v->type = LVAL_SEXPR;
  if (v->count == 1) {
    return lval_eval(e, v);
  }

  return v;
}

lval* builtin_lambda(lenv* e, lval* a) {
  ASSERT_COUNT("\\", a, 2);
  ASSERT_TYPE("\\", a, 0, LVAL_QEXPR);
  ASSERT_TYPE("\\", a, 1, LVAL_QEXPR);

  // first q-expression may only have symbols
  for (int i = 0; i < a->cell[0]->count; ++i) {
    ASSERT_TYPE("\\{args}", a->cell[0], i, LVAL_SYM);
  }

  lval* formals = lval_pop(a, 0);
  lval* body = lval_pop(a, 0);
  lval_del(a);

  return lval_lambda(formals, body);
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
    int int_op = 0;
    // pop next element
    lval* y = lval_pop(a, 0);

    if (x->num_type == LNUM_INT && y->num_type == LNUM_INT) {
      int_op = 1;
    }

    if (strcmp(op, "+") == 0) {
      x->num += int_op ? floor(y->num): y->num;
    }
    if (strcmp(op, "-") == 0) {
      x->num -= int_op ? floor(y->num): y->num;
    }
    if (strcmp(op, "*") == 0) {
      x->num *= int_op ? floor(y->num): y->num;
    }
    if (strcmp(op, "/") == 0) {
      if (y->num == 0) {
        lval_del(x);
        x = lval_err("function %s attempted to divide by 0", op);
      } else {
        if (int_op) {
          int xt = (int)floor(x->num);
          int yt = (int)floor(y->num);
          x->num = (xt / yt);
        } else {
          x->num /= y->num;
        }
      }
    }
    if (strcmp(op, "%") == 0) {
      if (y->num == 0) {
        lval_del(x);
        x = lval_err("function %s attempted to divide by 0", op);
      } else {
        if (int_op) {
          int xt = (int)floor(x->num);
          int yt = (int)floor(y->num);
          x->num = (xt % yt);
        } else {
          x->num = fmod(x->num, y->num);
        }
      }
    }
    if (strcmp(op, "^") == 0) {
      x->num = pow(x->num, y->num);
    }

    lval_del(y);

    if (x->type == LVAL_ERR) {
      break;
    } else {
      x->num_type = int_op ? LNUM_INT: LNUM_DEC;
    }
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

lval* builtin_gt(lenv* e, lval* a) {
  return builtin_ord(e, a, ">");
}

lval* builtin_ge(lenv* e, lval* a) {
  return builtin_ord(e, a, ">=");
}

lval* builtin_lt(lenv* e, lval* a) {
  return builtin_ord(e, a, "<");
}

lval* builtin_le(lenv* e, lval* a) {
  return builtin_ord(e, a, "<=");
}

lval* builtin_ord(lenv* e, lval* a, char* op) {
  ASSERT_COUNT(op, a, 2);
  ASSERT_TYPE(op, a, 0, LVAL_NUM);
  ASSERT_TYPE(op, a, 1, LVAL_NUM);

  int r;
  if (strcmp(op, ">") == 0) {
    r = (a->cell[0]->num > a->cell[1]->num);
  }
  if (strcmp(op, "<") == 0) {
    r = (a->cell[0]->num < a->cell[1]->num);
  }
  if (strcmp(op, ">=") == 0) {
    r = (a->cell[0]->num >= a->cell[1]->num);
  }
  if (strcmp(op, "<=") == 0) {
    r = (a->cell[0]->num <= a->cell[1]->num);
  }

  lval_del(a);
  return lval_num(r, LNUM_INT);
}

lval* builtin_cmp(lenv* e, lval* a, char* op) {
  ASSERT_COUNT(op, a, 2);

  int r;
  if (strcmp(op, "==") == 0) {
    r = lval_eq(a->cell[0], a->cell[1]);
  }
  if (strcmp(op, "!=") == 0) {
    r = !lval_eq(a->cell[0], a->cell[1]);
  }

  lval_del(a);
  return lval_num(r, LNUM_INT);
}

lval* builtin_eq(lenv* e, lval* a) {
  return builtin_cmp(e, a, "==");
}

lval* builtin_ne(lenv* e, lval* a) {
  return builtin_cmp(e, a, "!=");
}

lval* lval_num(double x, int ntype) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num_type = ntype; // LNUM_DEC or LNUM_INT
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

lval* lval_str(char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_STR;
  v->str = malloc(strlen(s) + 1);
  strcpy(v->str, s);
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

lval* lval_fun(lbuiltin func, char* s) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_FUN;
  v->builtin = func;
  v->name = malloc(strlen(s) + 1);
  strcpy(v->name, s);
  return v;
}

lval* lval_lambda(lval* formals, lval* body) {
  lval* v = malloc(sizeof(lval));

  v->type = LVAL_FUN;
  v->builtin = NULL;
  v->name = NULL;
  v->env = lenv_new();
  v->formals = formals;
  v->body = body;

  return v;
}

lval* lval_call(lenv* e, lval* f, lval* a) {
  // unpack special condition
  if (a->count == 1 &&
      a->cell[0]->type == LVAL_SEXPR && a->cell[0]->count > 1) {
    for (int i = 0; i < a->cell[0]->count; ++i) {
      lval_add(a, lval_copy(a->cell[0]->cell[i]));
    }

    lval_del(lval_pop(a, 0));
  }

  // if builtin then call it
  if (f->builtin) {
    return f->builtin(e, a);
  }

  // record argument counts
  int given = a->count;
  int total = f->formals->count;

  // while args still remain to be processed
  while (a->count) {
    // if we've ran out of formal args to bind
    TEST_COUNT("function", a, f->formals, 0, given, total);

    // pop the first symbol from the formals
    lval* sym = lval_pop(f->formals, 0);

    // special case to deal with '&'
    if (strcmp(sym->sym, "&") == 0) {
      // ensure '&' is followed by another symbol
      if (f->formals->count != 1) {
        lval_del(a);
        return lval_err("function format invalid, no args after '&'");
      }

      // next formal should be bound to remaining arguments
      lval* nsym = lval_pop(f->formals, 0);
      lenv_put(f->env, nsym, builtin_list(e, a));
      lval_del(sym);
      lval_del(nsym);
      break;
    }

    // pop the next argument from the list
    lval* val = lval_pop(a, 0);

    // bind a copy into the function's environment
    lenv_put(f->env, sym, val);

    // delete a symbol and value
    lval_del(sym);
    lval_del(val);
  }

  // arg list is now bound, so can be cleaned
  lval_del(a);

  // if '&' remains in formal list, bind to empty list
  if (f->formals->count > 0 && strcmp(f->formals->cell[0]->sym, "&") == 0) {
    // check to ensure that & is not passed wrongly
    if (f->formals->count != 2) {
      return lval_err("function format invalid: no symbol after '&'");
    }

    // pop and delete & symbol
    lval_del(lval_pop(f->formals, 0));

    // pop next symbol and create empty list
    lval* sym = lval_pop(f->formals, 0);
    lval* val = lval_qexpr();

    // bind to env and delete
    lenv_put(f->env, sym, val);
    lval_del(sym);
    lval_del(val);
  }

  // if all formals have been bound, evaluate
  if (f->formals->count == 0) {
    // set environment parent to evaluation environment
    f->env->par = e;

    // evaluate and return
    return builtin_eval(f->env, lval_add(lval_sexpr(), lval_copy(f->body)));
  } else {
    // otherwise return partially evaluated function
    return lval_copy(f);
  }
}

int lval_eq(lval* x, lval* y) {
  // different are always unequal
  if (x->type != y->type) { return 0; }

  // compare based on type
  switch(x->type) {
    case LVAL_NUM:
      return (x->num == y->num);
    case LVAL_ERR:
      return (strcmp(x->err, y->err) == 0);
    case LVAL_SYM:
      return (strcmp(x->sym, y->sym) == 0);
    case LVAL_STR:
      return (strcmp(x->str, y->str) == 0);
    case LVAL_FUN:
      if (x->builtin || y->builtin) {
        return x->builtin == y->builtin;
      } else {
        return lval_eq(x->formals, y->formals) && lval_eq(x->body, y->body);
      }
    case LVAL_QEXPR:
    case LVAL_SEXPR:
      if (x->count != y->count) { return 0; }
      for (int i = 0; i < x->count; ++i) {
        // if any element not equal then return false
        if (!lval_eq(x->cell[i], y->cell[i])) { return 0; }
      }
      return 1;
  }
  return 0;
}

lval* lval_read_num(mpc_ast_t* t, int num_type) {
  errno = 0;
  double x = strtod(t->contents, NULL);
  return errno != ERANGE ?
    lval_num(x, num_type) : lval_err("invalid number");
}

lval* lval_read_str(mpc_ast_t* t) {
  // cut off final quote
  t->contents[strlen(t->contents) - 1] = '\0';
  // copy the string missing the first quote
  char* unescaped = malloc(strlen(t->contents+1)+1);
  strcpy(unescaped, t->contents+1);
  // pass through the unescape function
  unescaped = mpcf_unescape(unescaped);
  // construct new lval using string
  lval* str = lval_str(unescaped);
  // free string and return
  free(unescaped);
  return str;
}

lval* lval_read(mpc_ast_t* t) {
  // convert if symbol or number
  if (strstr(t->tag, "number")) {
    if (strstr(t->tag, "decimal")) {
      return lval_read_num(t, LNUM_DEC);
    } else {
      return lval_read_num(t, LNUM_INT);
    }
  }
  if (strstr(t->tag, "symbol")) { return lval_sym(t->contents); }
  if (strstr(t->tag, "string")) { return lval_read_str(t); }

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
    if (strstr(t->children[i]->tag, "comment")) { continue; }
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
    case LVAL_STR:
      free(v->str);
      break;

    case LVAL_FUN:
      if (v->builtin) {
        free(v->name);
      } else {
        lenv_del(v->env);
        lval_del(v->formals);
        lval_del(v->body);
      }
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
      x->num_type = v->num_type;
      x->num = v->num;
      break;
    case LVAL_FUN:
      if (v->builtin) {
        x->builtin = v->builtin;
        x->name = malloc(strlen(v->name) + 1);
        strcpy(x->name, v->name);
      } else {
        x->builtin = NULL;
        x->name = NULL;
        x->env = lenv_copy(v->env);
        x->formals = lval_copy(v->formals);
        x->body = lval_copy(v->body);
      }
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
    case LVAL_STR:
      x->str = malloc(strlen(v->str) + 1);
      strcpy(x->str, v->str);
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
  e->par = NULL;
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
  if (e->par) {
    return lenv_get(e->par, k);
  } else {
    return lval_err("unbound symbol: %s", k->sym);
  }
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

lenv* lenv_copy(lenv* e) {
  lenv* n = malloc(sizeof(lenv));
  n->par = e->par;
  n->count = e->count;
  n->syms = malloc(sizeof(char*) * n->count);
  n->vals = malloc(sizeof(lval*) * n->count);
  for (int i = 0; i < e->count; ++i) {
    n->syms[i] = malloc(strlen(e->syms[i]) + 1);
    strcpy(n->syms[i], e->syms[i]);
    n->vals[i] = lval_copy(e->vals[i]);
  }
  return n;
}

void lenv_def(lenv* e, lval* k, lval* v) {
  while (e->par) { e = e->par; }
  lenv_put(e, k, v);
}

void lval_print_expr(lval* v, char open, char close) {
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
      if (v->num_type == LNUM_INT) {
        printf("%g", v->num);
      }
      else if (v->num_type == LNUM_DEC) {
        printf("%.2f", v->num);
      }
      break;

    case LVAL_ERR:
      fprintf(stderr, "error: %s", v->err);
      break;

    case LVAL_SYM:
      printf("%s", v->sym);
      break;

    case LVAL_STR:
      lval_print_str(v);
      break;

    case LVAL_FUN:
      if (v->builtin) {
        printf("(builtin): %s", v->name);
      } else {
        printf("(\\ ");
        lval_print(v->formals);
        putchar(' ');
        lval_print(v->body);
        putchar(')');
      }
      break;

    case LVAL_SEXPR:
      lval_print_expr(v, '(', ')');
      break;

    case LVAL_QEXPR:
      lval_print_expr(v, '{', '}');
      break;
  }
}

void lval_print_str(lval* v) {
  // make string copy
  char* escaped = malloc(strlen(v->str) + 1);
  strcpy(escaped, v->str);
  // pass through the escape function
  escaped = mpcf_escape(escaped);
  // print between quotes
  printf("\"%s\"", escaped);
  free(escaped);
}

void lval_println(lval* v) {
  if (v->type == LVAL_ERR) {
    fputc('>', stderr);
    fputc(' ', stderr);
    lval_print(v);
    fputc('\n', stderr);
  } else {
    fputc('>', stdout);
    fputc(' ', stdout);
    lval_print(v);
    fputc('\n', stdout);
  }
}

char* ltype_name(int t) {
  switch(t) {
    case LVAL_FUN: return "function";
    case LVAL_NUM: return "number";
    case LVAL_ERR: return "error";
    case LVAL_SYM: return "symbol";
    case LVAL_STR: return "string";
    case LVAL_QEXPR: return "q-expression";
    case LVAL_SEXPR: return "s-expression";
    default: return "unknown";
  }
}
