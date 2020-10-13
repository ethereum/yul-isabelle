#include "abicoder.hpp"
extern "C" {
#include "export/abicoder.h"
}

using namespace abicoder;

ABICoder::ABICoder()
{
	static const char *argv0 = "";
	abicoder_open(0, &argv0);
}

ABICoder::~ABICoder()
{
	abicoder_close();
}

char toHexNibble(unsigned char x)
{
	if (x < 10) return '0' + x;
	else return 'A' + x - 10;
}

std::pair<bool, std::string> splitErrorCondition(const char* result, size_t size)
{
  if (size >= 4 && result[0] == 'O' && result[1] == 'K' && result[2] == ':' && result[3] == ' ')
	return {true, std::string(result + 4, size - 4)};
  else
	return {false, std::string(result, size)};
}

std::pair<bool, std::string> ABICoder::encode(std::string const& _type, std::string const& _data)
{
	Objptr type = abicoder_alloc(_type.size());
	std::copy(_type.begin(), _type.end(), reinterpret_cast<char*>(type));
	std::string dataWithoutWhitespace;
	for (auto c: _data) {
		if (!isspace(c))
			dataWithoutWhitespace += c;
	}
	Objptr data = abicoder_alloc(dataWithoutWhitespace.size());
	std::copy(dataWithoutWhitespace.begin(), dataWithoutWhitespace.end(), reinterpret_cast<char*>(data));
	Objptr result = abicoder_encode(type, data);
	return splitErrorCondition(reinterpret_cast<const char*>(result), abicoder_size(result));
}

std::pair<bool, std::string> ABICoder::decode(std::string const& _type, std::string const& _data)
{
	Objptr type = abicoder_alloc(_type.size());
	std::copy(_type.begin(), _type.end(), reinterpret_cast<char*>(type));
	std::string dataWithoutWhitespace;
	for (auto c: _data) {
		if (!isspace(c))
			dataWithoutWhitespace += c;
	}
	Objptr data = abicoder_alloc(dataWithoutWhitespace.size());
	std::copy(dataWithoutWhitespace.begin(), dataWithoutWhitespace.end(), reinterpret_cast<char*>(data));
	Objptr result = abicoder_decode(type, data);
	return splitErrorCondition(reinterpret_cast<const char*>(result), abicoder_size(result));
}

std::pair<bool, std::string> ABICoder::decode(std::string const& _type, std::vector<unsigned char> const& _data)
{
	Objptr type = abicoder_alloc(_type.size());
	std::copy(_type.begin(), _type.end(), reinterpret_cast<char*>(type));
	Objptr data = abicoder_alloc(_data.size() * 2);
	{
		char *ptr = reinterpret_cast<char*>(data);
		for (unsigned char c: _data)
		{
			*ptr++ = toHexNibble(c >> 4);
			*ptr++ = toHexNibble(c & 0xF);
		}
	}
	Objptr result = abicoder_decode(type, data);
	return splitErrorCondition(reinterpret_cast<const char*>(result), abicoder_size(result));
}
