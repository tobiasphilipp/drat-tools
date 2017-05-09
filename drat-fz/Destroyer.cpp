#include "Destroyer.h"
#include <fstream>
#include <stdlib.h> 
#include <time.h>
#include <string> 
#include <sstream>
#include "Verificator_Caller.h"
#include <sys/wait.h>
#include <unistd.h>
#include <errno.h>

using namespace std;

void Destroyer::read_proof(){

  ifstream proof("proof", ifstream::binary);
  
  if(!proof.is_open()){
    cerr<<"cant open proof"<<endl;
    return;
    }
    
    clauses.clear();
    
   proof.seekg(0,proof.end);
   int length = proof.tellg();
   proof.seekg(0, proof.beg);
   
   char * buffer = new char [length];
   proof.read(buffer,length);
   
   bool lit_is_neg;
   string read_lit;
   signed int lit; 
   vector<signed int> clause;
   
   for(int i =0; i<length;++i){
      if((buffer[i] == '\n')){
	if(clause.size() == 0){
	 if(read_lit.size() > 0){
	   lit = atoi(read_lit.c_str());
	   clause.push_back(lit);
	 }
	}
	read_lit.clear();
	clauses.push_back(clause);
	clause.clear();
	continue;
      }
      else if(buffer[i] == ' '){
         if(read_lit.size() > 0){
	   lit = atoi(read_lit.c_str());
	   clause.push_back(lit);
	   read_lit.clear();
	 }
	 continue;
      }
      else if(buffer[i] == 'd'){ //in DRUP/DRAT only at the begin of a line
           clause.push_back(0);
	 continue;
      }
     read_lit += buffer[i];
    }

   clauses.pop_back(); //last clause is empty
   destroyed_clauses = clauses;
   
   delete[] buffer;
   proof.close();
  
}

bool Destroyer::remove_clause_randomly(bool deletioninfo)
{
 
  if(destroyed_clauses.size() == 0){ 
  
   // cerr<<"cant find clauses to destroy"<<endl;
    return false;
  }
  
  destroyed_clauses.clear(); 

  bool contains = true;
  bool flag;
  int  tries = 0;
  
  destroyed_clause = rand() % clauses.size(); 
  
  while(((clauses[destroyed_clause][0] == 0) && (!deletioninfo)) || contains ){ 
    tries++;
    destroyed_clause = rand() % clauses.size(); 
    flag = false;
    for(int i=0; i<destroyed_clause_rep.size();++i){ 
      if(destroyed_clause_rep[i] == destroyed_clause){flag = true; break;}
     }
    if(!flag) contains = false;
    
    if(tries > 20) return false;
  }
  
  destroyed_clause_rep.push_back(destroyed_clause);
  
  bool to_push;
  
  for(int i =0; i<clauses.size(); ++i){
    to_push = true;
    for(int k=0; k<destroyed_clause_rep.size();++k){ if(i==destroyed_clause_rep[k]) to_push = false;}
   if(to_push) destroyed_clauses.push_back(clauses[i]);  
  }
   
  return true;
}
bool Destroyer::adding_lit_randomly(int lits, bool deletioninfo, bool tautologies){ //TODO: here is an endless loop only constructing tautologies and no tautologies allowed
 
  //destroyed_clauses.clear();
  
  added_literal = (rand() % lits ) +1;
  
  if(rand()%2 == 1){ added_literal = 0 - added_literal;}

  if(destroyed_clauses.size() > 0){
  
    bool holds_complement_or_clause;
    int try_find_clause = 0;
    do{
      try_find_clause++;
      holds_complement_or_clause = false;
      destroyed_clause = rand() % clauses.size(); 
      while((clauses[destroyed_clause][0] == 0) && (!deletioninfo)){ destroyed_clause = rand() % clauses.size(); } 
  for(int i=0; i<destroyed_clauses[destroyed_clause].size(); ++i){
      if(((added_literal + destroyed_clauses[destroyed_clause][i] ==0)&&!tautologies) || (added_literal - destroyed_clauses[destroyed_clause][i] ==0)){holds_complement_or_clause=true; break;}
     }
     if(try_find_clause > 20){
       try_find_clause=0; 
       added_literal = (rand() % lits ) +1; 
       if(rand()%2 == 1){ 
	 added_literal = 0 - added_literal; 
	 continue;}
       }
	 
    }while(holds_complement_or_clause);
  
    destroyed_clause_rep.push_back(destroyed_clause);
    
    destroyed_clauses[destroyed_clause].push_back(added_literal);
  
  /*
  for(int i =0; i<clauses.size(); ++i){
  if(i == destroyed_clause){
    bool holds_complement = false;
    do{
    for(int k=0; k<clauses[i].size();++k){
      if(added_literal + clauses[i][k] ==0){ holds_complement=true; added_literal = rand() % lits; break;}
      if(k==clauses[i].size()-1) holds_complement=false;      
    }
    
    }while(holds_complement);
    clauses[i].push_back(added_literal);
  }
  destroyed_clauses.push_back(clauses[i]);
  clauses[i].pop_back();  
   }*/
  }
  else{
    vector<signed int> vec;
    vec.push_back(added_literal);
    destroyed_clauses.push_back(vec);
    destroyed_clause_rep.push_back(1);
  }
   
  return true;
}

bool Destroyer::removing_lit_randomly(int lits, bool deletioninfo){
 
  vector<signed int> clause_to_push;
  
  //destroyed_clauses.clear();
  
  removed_literal = (rand() % lits ) +1;
  
  if(rand()%2 == 1){ removed_literal = 0 - removed_literal;}

  if(destroyed_clauses.size() > 0){
  
    bool holds_lit = false;
    int try_find_big_clause;
    int tested_clauses =0;
    
  while(!holds_lit){
    try_find_big_clause = 0;
  destroyed_clause = rand() % destroyed_clauses.size(); 
  tested_clauses++;
  while(((destroyed_clauses[destroyed_clause][0] == 0) && (!deletioninfo)) || ((destroyed_clauses[destroyed_clause][0] == 0)&&(destroyed_clauses[destroyed_clause].size() <= 2)) 
                                                                           || ((destroyed_clauses[destroyed_clause][0] != 0)&&(destroyed_clauses[destroyed_clause].size() <= 1))){ 
    destroyed_clause = rand() % destroyed_clauses.size(); 
    try_find_big_clause++;
    if(try_find_big_clause > 100) return false;
  }
  for(int i =0; i < destroyed_clauses[destroyed_clause].size(); ++i){
    if(destroyed_clauses[destroyed_clause][i] == removed_literal){ holds_lit=true; break;}
    }
    if(tested_clauses > 20){
      tested_clauses =0;
      removed_literal = (rand() % lits ) +1;
       if(rand()%2 == 1){ removed_literal = 0 - removed_literal;} 
    }
  }
  destroyed_clause_rep.push_back(destroyed_clause);
    for(int k=0; k<destroyed_clauses[destroyed_clause].size();++k){
        if(destroyed_clauses[destroyed_clause][k] == removed_literal) continue;
	clause_to_push.push_back(destroyed_clauses[destroyed_clause][k]);
    }
   
   destroyed_clauses[destroyed_clause] = clause_to_push;
    
   return true;
  }
    
  return false;
}

void Destroyer::save_proof(bool deletioninfo){

  remove("proof"); //TODO: dont remove the file, just clear it, maybe better performance
  ofstream proof("proof", std::ios::out|std::ios::binary);
  
  bool del_tmp = true; 
  
  for(int i =0; i<destroyed_clauses.size();++i){

    for(int j=0; j<destroyed_clauses[i].size();++j){
      if(destroyed_clauses[i][j] == 0 && destroyed_clauses[i].size() > 1){
	if(deletioninfo) proof<<'d';
	else{ del_tmp=false; break;}
	}
      else proof << destroyed_clauses[i][j];
      del_tmp = true;    
      proof <<' ';  
      }
      if(del_tmp){
      proof <<0;
      proof <<'\n';
    }
   }
   proof <<0;
   proof <<'\n';
   
   proof.close();
  
}

void Destroyer::reset_proof()
{
  destroyed_clause_rep.clear();
  destroyed_clauses = clauses;
}

string Destroyer::destroy_proof(int lits, const char **arg_verificator, string ref_verificator, int deletion_info_option, bool tautologies, int method) //TODO: add counter
{
 
  bool deletioninfo;
  
  if(deletion_info_option == 0) deletioninfo=false;
  else if(deletion_info_option == 1) deletioninfo=true;
  else if(deletion_info_option==3){
                 int rand_del = rand() % 2;
               if(rand_del == 0) deletioninfo = true;
               else deletioninfo=false;
               }
  
  int count =0;
Verificator_Caller veri;
	
string ret;
int way;
 
if(method == 1){ way = 0; ret ="removing clause";}
else if(method == 2){ way = 2; ret ="removing literal";}
else if(method == 4){ way = 1; ret ="adding literal";}
else if(method == 3){ way = rand() % 2; way == 0 ? ret ="removing clause" : ret="removing literal";}
else if(method == 5){ way = rand() % 2; way == 0 ? ret ="removing clause" : ret="adding literal";}
else if(method == 6){ way = (rand() % 2) +1; way == 1 ? ret ="adding literal" : ret="removing literal";}
else if(method == 7){ way = rand() % 3; way == 0 ? ret ="removing clause" : way==1 ? ret="adding literal" : ret="removing literal";}
   
  read_proof();
  cerr<<"try "<<ret<<endl;
         do{
	     if(way ==0){
	     if(!remove_clause_randomly(deletioninfo)){
	       reset_proof();
	       way = 1;
	       
	       ret="adding literal"; 
	       cerr<<"try "<<ret<<endl;
	       adding_lit_randomly(lits, deletioninfo, tautologies);	
	      
	      }
	     }
	     else if(way==1){ adding_lit_randomly(lits, deletioninfo, tautologies);}
	     else{
	       if(!removing_lit_randomly(lits, deletioninfo)){
	       reset_proof();
	       way = 1;
	       
	       ret="adding literal"; 
	       cerr<<"try "<<ret<<endl;
	       adding_lit_randomly(lits, deletioninfo, tautologies);
	      }
	       
	    }
	     
	     save_proof(deletioninfo);
	     
	  int pid = fork();
	
	if(pid <0) cerr<<"error creating child"<<endl;
	if(pid == 0){
	  veri.set_Verificator(ref_verificator);
          veri.call_Verificator(arg_verificator);
	 }	
	
	  while (true) {
        int status;
        pid_t done = wait(&status);
             if (done == -1) {
         if (errno == ECHILD) break; // no more child processes
              } else {
		
		if((WEXITSTATUS(status) == 1))break;
		
        if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
            cerr << "pid " << done << " failed" <<endl;
            exit(1);
           }
        }
       }
	count++;
	}while(veri.check_verification(true));
	
	cerr<<"Steps to destroy proof: "<<count<<endl;
	return ret;
}


vector<string> Destroyer::get_destroyed_clause(){
  vector<string> ret;
  string tmp;
  
  if(clauses.size() == 0){
    cerr<<"ERROR, clauses should never be 0"<<endl;
    exit(1);
  }
  for(int j=0; j<destroyed_clause_rep.size();++j){
    for(int i=0; i<this->clauses[destroyed_clause_rep[j]].size(); ++i){
    ostringstream convert; 
    convert << clauses[destroyed_clause_rep[j]][i];
    tmp += convert.str();
    tmp += " ";
   }
   ret.push_back(tmp);
   tmp.clear();
  }
  return ret;
}

vector<int> Destroyer::get_destroyed_line(){
 return this->destroyed_clause_rep;  
}






