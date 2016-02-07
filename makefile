CFLAGS=-std=c99 -Wall
LIBS=-lm -leditline

all: lispy

lispy: mpc.o main.c
	$(CC) $(CFLAGS) $^ -o $@ ${LIBS}

mpc.o: mpc.c
	$(CC) $(CFLAGS) -c $< -o $@

clean:
	@rm -f ./*.o lispy
