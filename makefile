CFLAGS = -std=c99 -Wall
LIBS = -lm -leditline
OBJ = main.o lispy.o mpc.o
EXE = lispy

all: $(EXE)

lispy: $(OBJ)
	$(CC) $(CFLAGS) $^ -o $@ ${LIBS}

main.o: lispy.h
lispy.o: lispy.h
mpc.o: mpc.h

clean:
	@rm $(EXE) $(OBJ)
