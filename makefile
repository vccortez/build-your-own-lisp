CFLAGS = -std=c99 -Wall
LIBS = -lm -leditline
OBJ = main.o lispy.o mpc.o
DEPS = mpc.h lispy.h
EXE = lispy

%.o: %.c $(DEPS)
	$(CC) $(CFLAGS) -c -o $@ $<

lispy: $(OBJ)
	$(CC) $(CFLAGS) $^ -o $(EXE) ${LIBS}

clean:
	@rm $(EXE) $(OBJ)
