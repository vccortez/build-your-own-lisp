#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include <editline.h>

#include "lispy.h"

lenv* main_env;

int  on_exit(void);
void signal_handler();

int main(int argc, char **argv) {
  signal(SIGINT, signal_handler);

  main_env = lispy_init();

  if (argc == 1) {
    puts("> lispy version 0.0.1");
    puts("> press ctrl+c to exit");

    while (1) {
      char* input = readline("lispy> ");

      if (strcmp("exit", input) == 0) {
        free(input);
        break;
      }
      // add input to history
      add_history(input);

      // attempt to parse user input
      lispy_parse(main_env, input);

      free(input);
    }
  }

  if (argc >= 2) {
    for (int i = 1; i < argc; ++i) {
      lispy_exec(main_env, argv[i]);
    }
  }

  return on_exit();
}

void signal_handler() {
  exit(on_exit());
}

int on_exit() {
  lispy_clean(main_env);

  puts("> bye bye!");

  return 0;
}
