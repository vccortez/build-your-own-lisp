#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <math.h>
#include <editline.h>
#include "mpc.h"

enum { LVAL_ERR, LVAL_NUM, LVAL_SYM, LVAL_SEXPR };
enum { LERR_DIV_ZERO, LERR_BAD_OP, LERR_BAD_NUM };

struct LispyType {
  int type;
  double num;
  // error and symbol are strings
  char* err;
  char* sym;
  // count and pointer to list of "lval"
  int count;
  struct LispyType** cell;
};

typedef struct LispyType lval;

int on_exit();
void signal_handler();

lval* lval_read_num(mpc_ast_t*);
lval* lval_read(mpc_ast_t*);
lval* lval_add(lval*, lval*);

lval eval(mpc_ast_t*);
lval eval_op(lval, char*, lval);
lval eval_unary_op(lval, char*);

lval* lval_num(double);
lval* lval_err(char*);
lval* lval_sym(char*);
lval* lval_sexpr(void);
void lval_del(lval*);

void lval_expr_print(lval*, char, char);
void lval_print(lval*);
void lval_println(lval*);

int main() {
  signal(SIGINT, signal_handler);

  // create parsers
  mpc_parser_t* Number = mpc_new("number");
  mpc_parser_t* Symbol = mpc_new("symbol");
  mpc_parser_t* Sexpr  = mpc_new("sexpr");
  mpc_parser_t* Expr   = mpc_new("expr");
  mpc_parser_t* Lispy  = mpc_new("lispy");

  mpca_lang(MPCA_LANG_DEFAULT,
      "\
      number : /-?[0-9]+[.]?[0-9]*/ ;\
      symbol : '+' | '-' | '*' | '/' | '%' | '^' | \"min\" | \"max\" ;\
      sexpr  : '(' <expr>* ')' ;\
      expr   : <number> | <symbol> | <sexpr> ;\
      lispy  : /^/ <symbol> <expr>+ /$/ ;\
      ",
      Number, Symbol, Sexpr, Expr, Lispy);
  // version and exit information
  puts("> lispy version 0.0.1");
  puts("> press ctrl+c to exit");

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
      // lval answer = eval(r.output);
      lval* x = lval_read(r.output);
      lval_println(x);
      lval_del(x);
      mpc_ast_delete(r.output);
    } else {
      mpc_err_print(r.error);
      mpc_err_delete(r.error);
    }

    // free input data
    free(input);
  }

  mpc_cleanup(5, Number, Symbol, Sexpr, Expr, Lispy);
  return on_exit();
}

/*
lval eval(mpc_ast_t* t) {
  // if number return it
  if (strstr(t->tag, "number")) {
    // check error in conversion
    errno = 0;
    //long x = strtol(t->contents, NULL, 10);
    double x = strtod(t->contents, NULL);
    return errno != ERANGE ? lval_num(x) : lval_err(LERR_BAD_NUM);
  }

  // symbol is always the second child
  char* op = t->children[1]->contents;

  // store the third child in 'x'
  lval x = eval(t->children[2]);

  // iterate remaining children and combining
  // or if no remaining children attempt unary operation
  int i = 3;
  if (strstr(t->children[i]->tag, "expr")) {
    while (strstr(t->children[i]->tag, "expr")) {
      x = eval_op(x, op, eval(t->children[i]));
      i++;
    }
  } else {
    x = eval_unary_op(x, op);
  }

  return x;
}

lval eval_op(lval x, char* op, lval y) {
  // if either is an error, return it
  if (x.type == LVAL_ERR) { return x; }
  if (y.type == LVAL_ERR) { return y; }

  // else do the math
  int err = -1;
  double num;
  if (strcmp(op, "+") == 0) {
    num = x.num + y.num;
  }
  else if (strcmp(op, "-") == 0) {
    num = x.num - y.num;
  }
  else if (strcmp(op, "*") == 0) {
    num = x.num * y.num;
  }
  else if (strcmp(op, "/") == 0) {
    if (y.num == 0) {
      err = LERR_DIV_ZERO;
    } else {
      num = x.num / y.num;
    }
  }
  else if (strcmp(op, "%") == 0) {
    if (y.num == 0) {
      err = LERR_DIV_ZERO;
    } else {
      num = fmod(x.num, y.num);
    }
  }
  else if (strcmp(op, "^") == 0) {
    num = pow(x.num, y.num);
  }
  else if (strcmp(op, "min") == 0) {
    num = (x.num > y.num) ? y.num : x.num;
  }
  else if (strcmp(op, "max") == 0) {
    num = (x.num > y.num) ? x.num : y.num;
  }

  if (err != -1) {
    return lval_err(err);
  } else {
    return lval_num(num);
  }
}

lval eval_unary_op(lval x, char* op) {
  if (strcmp(op, "-") == 0) {
    return lval_num(x.num * -1);
  }
  return x;
}
*/

lval* lval_num(double x) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_NUM;
  v->num = x;
  return v;
}

lval* lval_err(char* m) {
  lval* v = malloc(sizeof(lval));
  v->type = LVAL_ERR;
  v->err = malloc(strlen(m) + 1);
  strcpy(v->err, m);
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

    case LVAL_SEXPR:
      for (int i = 0; i < v->count; ++i) {
        lval_del(v->cell[i]);
      }

      free(v->cell);
      break;
  }

  free(v);
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

    case LVAL_SEXPR:
      lval_expr_print(v, '(', ')');
      break;
  }
}

void lval_println(lval* v) {
  putchar('>');
  putchar(' ');
  lval_print(v);
  putchar('\n');
}

void signal_handler() {
  exit(on_exit());
}

int on_exit() {
  puts("> bye bye!");
  return 0;
}
