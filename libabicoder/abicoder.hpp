#pragma once

#include <string>
#include <vector>
#include <utility>

namespace abicoder {

class ABICoder
{
public:
	/** @a heapSize Heap size to be used by the ML generated code in KB. Defaults to 0 which chooses the default amount. */
	ABICoder(size_t heapSize = 0);
	ABICoder(ABICoder const&) = delete;
	~ABICoder();
	ABICoder& operator=(ABICoder const&) = delete;
	std::pair<bool, std::string> decode(std::string const& _type, std::vector<unsigned char> const& _data);
	std::pair<bool, std::string> decode(std::string const& _type, std::string const& _data);

	std::pair<bool, std::string> encode(std::string const& _type, std::string const& _data);
};

}
