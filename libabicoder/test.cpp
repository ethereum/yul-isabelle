#include "abicoder.hpp"
#include <iostream>

int main(int argc, const char** argv)
{
	abicoder::ABICoder coder(1024*512);

	if (argc == 4 && std::string(argv[1]) == "dec")
	{
		auto [status, result] = coder.decode(argv[2], argv[3]);
		if (status)
		{
			std::cout << result << std::endl;
			return EXIT_SUCCESS;
		}
		else
		{
			std::cerr << result << std::endl;
			return EXIT_FAILURE;
		}
	}
	else if (argc == 4 && std::string(argv[1]) == "enc")
	{
		auto [status, result] = coder.encode(argv[2], argv[3]);
		if (status)
		{
			std::cout << result << std::endl;
			return EXIT_SUCCESS;
		}
		else
		{
			std::cerr << result << std::endl;
			return EXIT_FAILURE;
		}
	}
	else
	{
		std::cerr << "Usage: " << argv[0] << " enc/dec <type> <data>" << std::endl;
		return EXIT_FAILURE;
	}
}
