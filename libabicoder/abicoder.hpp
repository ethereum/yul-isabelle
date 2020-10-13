#pragma once

#include <string>
#include <vector>
#include <utility>

namespace abicoder {

class ABICoder
{
public:
	ABICoder();
	ABICoder(ABICoder const&) = delete;
	~ABICoder();
	ABICoder& operator=(ABICoder const&) = delete;
	std::pair<bool, std::string> decode(std::string const& _type, std::vector<unsigned char> const& _data);
	std::pair<bool, std::string> decode(std::string const& _type, std::string const& _data);

	std::pair<bool, std::string> encode(std::string const& _type, std::string const& _data);
};

}
