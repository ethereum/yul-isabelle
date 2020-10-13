theories := $(wildcard ../*.thy)

all: abicoder.a

export/abicoder.ML: $(theories) ../ROOT
	isabelle build -D ..
	isabelle export -O export -d .. -x "*:**" -p 2 SolidityAbi

abicoder.o: export/abicoder.ML abicoder.mlb mlton_export.sml
	mlton -format archive -default-ann 'allowFFI true' -default-ann "redundantMatch ignore" -export-header export/abicoder.h abicoder.mlb
	ar x abicoder.a
	mv abicoder.a.o abicoder.o
	rm abicoder.a

export/abicoder.h: abicoder.o

test.o: test.cpp abicoder.hpp
	g++ -std=c++17 -c -I . -o test.o test.cpp

abicoderpp.o: abicoder.cpp abicoder.hpp export/abicoder.h
	g++ -std=c++17 -c abicoder.cpp -o abicoderpp.o

libabicoder.a: abicoder.o abicoderpp.o
	ar -crs libabicoder.a abicoder.o abicoderpp.o

test: test.o libabicoder.a
	g++ -o test -L . test.o -labicoder -lgmp

clean:
	rm -rf export libabicoder.a test.o test abicoder.o abicoderpp.o
