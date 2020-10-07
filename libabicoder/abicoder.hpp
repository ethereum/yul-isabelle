#pragma once

#include <string>
#include <vector>

namespace abicoder {

class ABICoder
{
public:
	ABICoder();
	ABICoder(ABICoder const&) = delete;
	~ABICoder();
	ABICoder& operator=(ABICoder const&) = delete;
	std::string decode(std::string const& _type, std::vector<unsigned char> const& _data);
	std::string decode(std::string const& _type, std::string const& _data);
};

}
