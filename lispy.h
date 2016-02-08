#ifndef lispy_h
#define lispy_h

struct lispy_value;
typedef struct lispy_value lval;

struct lispy_environment;
typedef struct lispy_environment lenv;

typedef lval*(*lbuiltin)(lenv*, lval*);

struct lispy_value {
  int type;

  int num_type;
  double num;

  char *err;
  char *sym;
  char *str;

  lbuiltin builtin;

  lenv *env;
  lval *formals;
  lval *body;

  int count;
  lval **cell;
};

struct lispy_environment {
  lenv *par;
  int count;
  char **syms;
  lval **vals;
};

lenv* lispy_init(void);
char* lispy_parse(lenv*, char*);
char* lispy_exec(lenv*, char*);
void  lispy_clean(lenv*);

#endif
