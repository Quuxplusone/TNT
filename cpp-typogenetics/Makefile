CXXFLAGS=-std=c++14 -W -Wall -Wextra -Wno-sign-compare -pedantic

dna-test: dna-test.o dna.o
	$(CXX) $(CXXFLAGS) $^ -o $@

clean:
	rm -f typogenetics *.o

test: dna-test
	./dna-test

%.o: %.cc
	$(CXX) $(CXXFLAGS) $< -c -o $@

.PHONY: clean test
