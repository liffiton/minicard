.PHONY: all test

all:
	g++ -std=c++17 -O1 -g -fsanitize=address,undefined -fno-omit-frame-pointer -I .. opb_equality.cpp ../minicard/Solver.cc ../utils/Options.cc ../utils/System.cc -lz -o bin/opb_equality_test

test:
	bin/opb_equality_test

