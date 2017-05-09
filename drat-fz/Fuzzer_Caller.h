#include <string>


class Fuzzer_Caller{
  
public:
  void call_Fuzzer();
  void setFuzzer(std::string fuzzer, const char** arg);
  
private:
    const char **arg_fuzzer; 
    std::string fuzzer;
  
};