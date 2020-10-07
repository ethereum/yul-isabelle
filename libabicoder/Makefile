theories := $(wildcard ../*.thy)

all: test

export/abicoder.ML: $(theories) ../ROOT
	isabelle build -o quick_and_dirty -D ..
	isabelle export -O export -d .. -x "*:**" -p 2 SolidityAbi

abicoder.a: export/abicoder.ML abicoder.mlb mlton_export.sml
	mlton -format archive -default-ann 'allowFFI true' -default-ann "redundantMatch ignore" -export-header export/abicoder.h abicoder.mlb

export/abicoder.h: abicoder.a

test.o: test.cpp abicoder.hpp
	g++ -c -I . -o test.o test.cpp

abicoder.o: abicoder.cpp abicoder.hpp export/abicoder.h
	g++ -c abicoder.cpp -o abicoder.o

test: test.o abicoder.a abicoder.o
	g++ -o test test.o abicoder.o abicoder.a -lgmp

clean:
	rm -rf export abicoder.a test.o test abicoder.o
