#include "abicoder.hpp"
#include <iostream>

int main(int argc, const char** argv)
{
	abicoder::ABICoder coder;
	
	if (argc == 4 && std::string(argv[1]) == "dec")
		std::cout << coder.decode(argv[2], argv[3]) << std::endl;
	else if (argc == 4 && std::string(argv[1]) == "enc")
		std::cout << coder.encode(argv[2], argv[3]) << std::endl;
	else
		std::cerr << "Usage: " << argv[0] << " enc/dec <type> <data>" << std::endl;
}
