#include "abicoder.hpp"
#include <iostream>

int main(int argc, const char** argv)
{
	abicoder::ABICoder coder;
	
	if (argc == 3)
		std:: cout << coder.decode(argv[1], argv[2]) << std::endl;
	else
		std::cerr << "Usage: " << argv[0] << " <type> <data>" << std::endl;
	
/*	abicoder_open(argc, argv);
	Objptr obj = alloc(52);
	abicoder_close();*/
}
