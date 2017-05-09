#include <vector>
#include <string>

class Cnf_Reader{

public: 
  Cnf_Reader(std::string path);
  int get_cnf_dir();
  int get_c_formula(){ return this->c_formula;}
  
  bool has_next();
  const char* next();

  const char* getPath(){return this->path.c_str();};

private:
  int curr_index;
  std::string path;
  int c_formula;
  std::vector<std::string> formulas;
};