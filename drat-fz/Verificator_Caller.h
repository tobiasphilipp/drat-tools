 #include <string>
#include <vector>

class Verificator_Caller{

public:
  void call_Verificator(const char **arg_verificator);
  bool set_Verificator(std::string verf);
  
  //return whether the proof is varified(true) or not(false), and stores the result
  bool check_verification(bool drat_trim);
  
  bool get_result(int i){
  
    return results[i];
  }
  
  //returns way and position of every modified clause
  std::vector<std::string> destroy_information(std::string way, std::vector<std::string> clause);
  
private:
    
    //stores entire information of modified clauses
    std::vector<std::string> info; 
    std::string verificator; 
    
    //stores results of tested verificator
    std::vector<bool> results;
      
};
