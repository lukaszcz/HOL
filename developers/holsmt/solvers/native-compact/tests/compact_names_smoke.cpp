#include <cstdlib>
#include <ios>
#include <iostream>
#include <ostream>
#include <stdexcept>
#include <streambuf>
#include <string>

#include "printer/compact_names.h"

using cvc5::internal::printer::CompactNames;
using cvc5::internal::printer::CompactPrintStream;

namespace {

void require(bool condition, const char* message)
{
  if (!condition) throw std::runtime_error(message);
}

class FailingBuffer : public std::streambuf
{
 protected:
  int_type overflow(int_type) override { return traits_type::eof(); }
};

class FailingCompactBuffer : public CompactPrintStream
{
 public:
  explicit FailingCompactBuffer(CompactNames& names)
      : CompactPrintStream(names)
  {
  }

 protected:
  int_type overflow(int_type) override { return traits_type::eof(); }
};

}  // namespace

int main()
{
  try
  {
    require(CompactPrintStream::compact(" (f  x)\n(g y) ")
                == "(f x)(g y)",
            "lexical compaction changed");
    const std::string rational = "(/ (- 1) 2)";
    require(!CompactNames::strictlyProfitable(rational, "@aaaa", 6),
            "six-use negative rational grew the stream");
    require(CompactNames::strictlyProfitable(rational, "@aaaa", 7),
            "seven-use negative rational should save one byte");

    CompactNames names;
    auto& rejected = names.entries[{'l', 1}];
    rejected.count = 2;
    rejected.literal = "12345";
    names.entries[{'p', 2}].count = 1;
    names.allocate();
    require(rejected.name.empty(), "unprofitable literal was allocated");
    require(names.entries.at(CompactNames::Key{'p', 2}).name == "@a",
            "rejected literal consumed the next alias");

    CompactNames collision;
    collision.reserved.insert("@a");
    collision.entries[{'p', 1}].count = 1;
    collision.allocate();
    require(collision.entries.at(CompactNames::Key{'p', 1}).name == "@b",
            "reserved alias was reused");

    CompactNames countNames;
    FailingCompactBuffer countFailure(countNames);
    std::ostream countOut(&countFailure);
    countOut.exceptions(std::ios::badbit | std::ios::failbit);
    bool countThrew = false;
    try
    {
      countOut << "proof";
    }
    catch (const std::ios_base::failure&)
    {
      countThrew = true;
    }
    require(countThrew && countNames.entries.empty(),
            "counting stream failure was swallowed");

    FailingBuffer destinationFailure;
    std::ostream destination(&destinationFailure);
    CompactNames outputNames;
    outputNames.collecting = false;
    CompactPrintStream outputFailure(outputNames, &destination);
    std::ostream output(&outputFailure);
    output.exceptions(std::ios::badbit | std::ios::failbit);
    bool outputThrew = false;
    try
    {
      output << "proof";
    }
    catch (const std::ios_base::failure&)
    {
      outputThrew = true;
    }
    require(outputThrew, "emission stream failure was swallowed");
  }
  catch (const std::exception& error)
  {
    std::cerr << error.what() << '\n';
    return EXIT_FAILURE;
  }
  std::cout << "compact_names_smoke: OK\n";
  return EXIT_SUCCESS;
}
