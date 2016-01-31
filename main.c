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

lval* lval_eval_sexpr(lval*);
lval* lval_eval(lval*);
lval* lval_pop(lval*, int);
lval* lval_take(lval*, int);

lval* builtin_op(lval*, char*);

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
      lispy  : /^/ <expr>* /$/ ;\
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
      lval* answer = lval_eval(lval_read(r.output));
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

  mpc_cleanup(5, Number, Symbol, Sexpr, Expr, Lispy);
  return on_exit();
}

lval* lval_eval_sexpr(lval* v) {
  // evaluate children
  for (int i = 0; i < v-> count; ++i) {
    v->cell[i] = lval_eval(v->cell[i]);
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

  // ensure first element is symbol
  lval* f = lval_pop(v, 0);
  if (f->type != LVAL_SYM) {
    lval_del(f);
    lval_del(v);
    return lval_err("s-expression missing symbol!");
  }

  // call builtin with operator
  lval* result = builtin_op(v, f->sym);
  lval_del(f);
  return result;
}

lval* lval_eval(lval* v) {
  // evaluate if s-expressions
  if (v->type == LVAL_SEXPR) {
    return lval_eval_sexpr(v);
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

lval* builtin_op(lval* a, char* op) {
  // ensure all are numbers
  for (int i = 0; i < a->count; ++i) {
    if (a->cell[i]->type != LVAL_NUM) {
      lval_del(a);
      return lval_err("can't operate on non-number");
    }
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
        x = lval_err("division by zero!");
        break;
      }
      x->num /= y->num;
    }
    if (strcmp(op, "%") == 0) {
      if (y->num == 0) {
        lval_del(x);
        lval_del(y);
        x = lval_err("division by zero!");
        break;
      }
      x->num = fmod(x->num, y->num);
    }
    if (strcmp(op, "^") == 0) { x->num = pow(x->num, y->num); }
    if (strcmp(op, "min") == 0) { x->num = fmin(x->num, y->num); }
    if (strcmp(op, "max") == 0) { x->num = fmax(x->num, y->num); }
    lval_del(y);
  }

  lval_del(a);
  return x;
}

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
