program: program.o
	cc program.o -o program
program.o: program.c
	cc -Wall -c program.c
