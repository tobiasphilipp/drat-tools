#include <iostream>
#include <vector>
#include <string>

class Destroyer{

public:
      
  void read_proof();
  bool remove_clause_randomly(bool deletioninfo); 
  bool adding_lit_randomly(int lits, bool deletioninfo, bool tautologies);
  bool removing_lit_randomly(int lits, bool deletioninfo);
  void save_proof(bool deletioninfo);
  std::string destroy_proof(int lits, const char **arg_verificator, std::string ref_verificator, int deletion_info_option, bool tautologies, int method);
  
  //returns modified clauses of last destroying step
  std::vector<std::string> get_destroyed_clause();
  
  //return appropiate index of destroyed clause
  std::vector<int> get_destroyed_line();
  
  void reset_proof();
  
  int get_proof_size(){
  return clauses.size();    
  }
  
private:
  
  //repository index of destroyed clauses
  std::vector<int> destroyed_clause_rep;
  //last destroyed clause
  int destroyed_clause;
  
  signed int added_literal;
  signed int removed_literal;
  
  //original proof
  std::vector<std::vector<signed int> > clauses;
  
  //destroyed proof
  std::vector<std::vector<signed int> > destroyed_clauses;   
  
};