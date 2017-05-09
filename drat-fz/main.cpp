#include <signal.h>

#include "main.h"
#include "Destroyer.h"
#include "Fuzzer_Caller.h"
#include "Verificator_Caller.h"
#include "Cnf_Reader.h"
#include <sys/wait.h>
#include <unistd.h>
#include <time.h>
#include <fstream>
#include <time.h>
#include <string>
#include <cstdlib>
#include <errno.h>
#include <stdio.h>

//=================================================================================================

using namespace std;

//=================================================================================================


void evaluation(){
  
	int avg_clauses=0;
	int max_cl = 0;
	int min_cl = 10000;
	for(int i=0;i<n_clauses.size();++i){
	  if(n_clauses[i]>max_cl)max_cl=n_clauses[i];
	  if(n_clauses[i]<min_cl)min_cl=n_clauses[i];
	  avg_clauses+=n_clauses[i];
	}
	avg_clauses /= n_clauses.size();
	
	int avg_variables=0;
	int max_var = 0;
	int min_var = 10000;
	for(int i=0;i<n_vars.size();++i){
	  if(n_vars[i]>max_var) max_var=n_vars[i];
	  if(n_vars[i]<min_var)min_var=n_vars[i];
	  avg_variables+=n_vars[i];
	}
	avg_variables /= n_vars.size();
	
	int avg_proof=0;
	int max_proof = 0;
	int min_proof = 10000;
	for(int i=0;i<n_proof_clauses.size();++i){
	  if(n_proof_clauses[i]>max_proof)max_proof=n_proof_clauses[i];
	  if(n_proof_clauses[i]<min_proof) min_proof=n_proof_clauses[i];
	  avg_proof+=n_proof_clauses[i];
	}
	avg_proof /= n_proof_clauses.size();
	
	
	cerr<<"evaluation \n avg-formula-size: clauses: "<<avg_clauses<<" variables: "<<avg_variables<< "\n" << " avg proof-size: "<<avg_proof<<endl;
	cerr<<" max-formula-size: clauses: "<<max_cl<<" variables: "<<max_var<< "\n" << " min-formula-size: clauses: "<<min_cl<< " variables: "<<min_var<<"\n" << " max-proof-size: "<<max_proof<< "\n" <<" min_proof-size "<<min_proof<<endl;
}


void wait_for_solving(pid_t timer, pid_t solver){
 while (true) {
    
        int status;
        pid_t done = wait(&status);
	
             if (done == -1) {
         if (errno == ECHILD) break; // no more child processes
              } else {
		
		if(done == timer && WEXITSTATUS(status) == 0){
		 			
			cerr<<"terminated"<<endl;
			kill(solver, SIGTERM);
			SAT = true; //if read_Formula doesnt terminate, dont call the verificator
			break;
		      }
		      
		 if(done == solver && WEXITSTATUS(status) == 10){
                   SAT=true;
		   kill(timer, SIGTERM);
		   break;
		 }
		  if(done == solver && WEXITSTATUS(status) == 20){
                   SAT=false;
		   kill(timer, SIGTERM);
		   
		    ifstream proof("proof", ifstream::binary);
  
                     proof.seekg(0,proof.end);
                      int length = proof.tellg();
                     proof.seekg(0, proof.beg);
		   
		     if(length <= 2) SAT=true;
		     
		     proof.close();
		     
		   break;
		 }
		
		 
                 if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                    cerr << "pid " << done << " failed" << endl;
                       exit(1);
                   }
        }
    }
}

void parent_waiting(bool veri){
  while (true) {
    
        int status;
        pid_t done = wait(&status);
	
             if (done == -1) {
         if (errno == ECHILD) break; // no more child processes
              } else {
		
		if((WEXITSTATUS(status)) != 0 && veri)break;
		
		if((WEXITSTATUS(status)) == 0){
		  //its possible that there are two processes here | catching the timer_child and verificator_child | just continue if there's no child anymore (see errno == ECHILD)
		}
		
                else if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) {
                   cerr << "pid " << done << " failed" << WEXITSTATUS(status)<< endl;
                      exit(1);
                  }
        }
       }
}


int get_header(const char* formula_name){


	  ifstream header(formula_name, ifstream::binary);
	     header.seekg(0,header.end);
             int length = header.tellg();
              header.seekg(0, header.beg);
	      
           char * buffer = new char [length];
           header.read(buffer,length);
   
           char* p_cnf;
           p_cnf = strstr(buffer, "p cnf "); 
	   
	   int k = 6;
	   string vars;
	   while(p_cnf[k] != ' '){
	   vars += p_cnf[k];
	     k++;
	   }
	   
	   k++;
	
	   string n_cl;
           while(p_cnf[k] != '\n'){
	   n_cl += p_cnf[k];
	     k++;
	   }
	   n_vars.push_back(atoi(vars.c_str()));
	   n_clauses.push_back(atoi(n_cl.c_str()));
	   
	   delete[] buffer;
	   header.close();
	   
	   return n_vars.back();
	   
	   
	   
	  
}

//getting header of generated cnf
int get_header(){
get_header("formula"); 	  
}


bool test_verificator(Verificator_Caller* verificator, int deletion_info, Cnf_Reader* reader){
  
  pid_t pid;
  int vars; 
  
   if(!specific_cnf){ 
     pid = fork();
    if(pid <0) cerr<<"error creating child"<<endl;
	if(pid == 0){
	  Fuzzer_Caller fuzz;
	  
	  int n_fuzzer = rand() % fuzzer.size();
	  
	  const char** arg_fuzzer=new const char* [fuzzer_arguments[n_fuzzer].size()+2];
	  arg_fuzzer[0] = "formula_fuzzer@fuzzer";
	  for(int i=0; i<fuzzer_arguments[n_fuzzer].size();++i) arg_fuzzer[1+i] = (fuzzer_arguments[n_fuzzer][i].c_str());
	  //execl(solver.c_str(), const_cast<char*>("solver"), "formula", "proof", NULL);
	  arg_fuzzer[fuzzer_arguments[n_fuzzer].size()+1] = NULL;
	  
	  fuzz.setFuzzer(fuzzer[n_fuzzer], arg_fuzzer);
	  
	  fuzz.call_Fuzzer();

          delete arg_fuzzer;	  
	 
	}
   
	      
        parent_waiting(false);
	vars= get_header();
   }    
   else{     
     char full_path[512];   // array to hold the full_path.

     const char* br = reader->next();
    strcpy(full_path,reader->getPath()); 
    strcat(full_path,br); 
 
    arg_solver[1] = (const char*) &full_path;
    arg_verificator[1] = (const char*) &full_path;
    arg_ref_verificator[1] = (const char*) &full_path;
    
      cerr<<"testing specific formula: "<<arg_solver[1]<<endl;
    
    vars = get_header(full_path);
  }     
	
	
	pid = fork();
	if(pid <0) cerr<<"error creating child"<<endl;
	if(pid == 0){

	 remove("proof");
	 
	 execv(solver.c_str(), (char **) arg_solver);
	 }
	 else{
	 pid_t timerpid = fork();
	 if(timerpid <0){
	   cerr<<"error creating child"<<endl;
	   exit(1);
	   }
	   if(timerpid == 0){
	       sleep(10);
	         _exit(0);
	      }
	    wait_for_solving(timerpid, pid); 
	 }
	 
     if (SAT == false){
	cerr<<"unsat-formula # "<<unsat++<<endl;
	
	    pid = fork();
	if(pid <0) cerr<<"error creating child"<<endl;
	if(pid == 0){
	 verificator->call_Verificator(arg_verificator);
	 }
		
	parent_waiting(true);
	
	if(!(verificator->check_verification(true))){ //if the tested verificator verifies proofs in an other way than drat-trim, the argument of check_verification has to be false. make respective changes in check_verification-method
	  cerr<<"ERROR IN VERIFICATOR, PROOF SHOULD BE VERIFIED"<<endl;
	  evaluation();
	exit(1);
	}
             Destroyer destroyer;
	     string destroyed = destroyer.destroy_proof(vars, arg_ref_verificator, ref_verificator, deletion_info, tautologies, method);
	     n_proof_clauses.push_back(destroyer.get_proof_size());
	     
	     //destroyer.get_destroyed_clause();
	   
	      pid = fork();
	if(pid <0) cerr<<"error creating child"<<endl;
	if(pid == 0){
          verificator->call_Verificator(arg_verificator);
	 }
		
	parent_waiting(true);
	if(verificator->check_verification(true)){
	cerr<<"ERROR IN VERIFICATOR, PROOF SHOULD NOT BE VERIFIED. THE FOLLOWING CLAUSE WAS MODIFIED: "<<endl;
	vector<string> info = verificator->destroy_information(destroyed, destroyer.get_destroyed_clause());
        vector<int>lines = destroyer.get_destroyed_line();
	for(int i=0; i<info.size();++i){
	cerr<<info[i]<<endl;
	cerr<<"in line "<<lines[i]<<endl;
	}
	evaluation();
	exit(1);
	}
	     
  }   
     
      return true;
  
}
    
void printhelp(){

  cerr<<"Options:"<<endl;
  cerr<<"-h....print help"<<endl;
  cerr<<"-c....number of unsat-instances to check"<<endl;
  cerr<<"-d....print deletion_info in proofs, 0=disabled, 1=enabled, 3=random [enabled by default]"<<endl;
  cerr<<"-v....path to verificator to check (add arguments: path,arg1,...argn)"<<endl;
  cerr<<"-t....decide whether the proof contains tautologies [disabled by default]"<<endl;
  cerr<<"-m....method to destroy the proof (remove clause=1, remove literal=2, add literal=4) [7 by default]"<<endl;
//   cerr<<"-s....use specific formula (/cnf) [disabled by default]"<<endl;
  exit(0);
  
}
    
void parseOptions(int argc, char** argv){

    char* option;
    int k=3;
    
  for(int i=0; i< argc; i++){
  
     if((string)argv[i] == "-h") printhelp();
     
     else if((string)argv[i] == "-t") tautologies = true;
     
//      else if((string)argv[i] == "-s") specific_cnf = true;     
     
     else if((option = strstr(argv[i],"-c=")) != NULL){
       k = 3;
       string _count;
      while(option[k] != NULL){
	 _count += option[k];
	     k++;
      }
      count =  atoi(_count.c_str());
      if(count == 0){cerr<<"count[invalid digit]"<<endl; exit(1);}
     }
     
      else if((option = strstr(argv[i],"-m=")) != NULL){
       k = 3;
       string _method;
      while(option[k] != NULL){
	 _method += option[k];
	     k++;
      }
      method =  atoi(_method.c_str());
      if(method < 1 || method>7){cerr<<"count[invalid digit]"<<endl; exit(1);}
     }
     
     else if((option = strstr(argv[i],"-d=")) != NULL){
       k = 3;
       string del_info;
      while(option[k] != NULL){
	 del_info += option[k];
	     k++;
      }
      deletion_info = atoi(del_info.c_str());
      if(deletion_info > 2){cerr<<"deletion_info[0,2]"<<endl; exit(1);}
     }
     
     else if((option = strstr(argv[i],"-v=")) != NULL){
       k = 3;
       verificator = "";
       bool arguments = false;
       string argument;
      while(option[k] != NULL){
	 if(option[k] == ','){
       
       if(!arguments) arguments =true;
       else{ verificator_arguments.push_back(argument); argument ="";}
                    
    }
     else if(!arguments) verificator += option[k];
     
     else if(arguments) argument += option[k];
     
     k++;
      }
      if(argument != ""){ verificator_arguments.push_back(argument); argument ="";} 
     } 
  }
}

void parseConfiguration(){
  
string conf= path +"/config";
  ifstream config(conf.c_str(), ifstream::binary);
  
  int k;
  
  if(!config.is_open()){
    cerr<<"cant find configuration"<<endl;
    exit(1);
    }
    
    config.seekg(0,config.end);
   int length = config.tellg();
   config.seekg(0, config.beg);
   
   char * buffer = new char [length];
   config.read(buffer,length);
   
   char* value;
   
   
   value = strstr(buffer,"Solver=");  //parsing solver with arguments
   if(value != NULL){
   k = 7;
   bool arguments = false;
   string argument;
   while(value[k] != ';'){
     if(value[k] == ','){
       
       if(!arguments) arguments =true;
       else{ solver_arguments.push_back(argument); argument ="";}
                    
    }
     else if(!arguments) solver += value[k];
     
     else if(arguments) argument += value[k];
     
     k++;
    }
    if(argument != "") solver_arguments.push_back(argument);
   }
   else{ cerr<<"no solver in configuration"<<endl; exit(1);}
   
 value = strstr(buffer,"Reference-Verificator=");  //parsing reference-verificator with arguments
   if(value != NULL){
   k = 22;
   bool arguments = false;
   string argument;
   while(value[k] != ';'){
     if(value[k] == ','){
       
       if(!arguments) arguments =true;
       else{ ref_verificator_arguments.push_back(argument); argument ="";}
                    
    }
     else if(!arguments) ref_verificator += value[k];
     
     else if(arguments) argument += value[k];
     
     k++;
    }
    if(argument != "") ref_verificator_arguments.push_back(argument);
   }
   else{ cerr<<"no Reference-Verificator in configuration"<<endl; exit(1);}
   
   value = strstr(buffer,"Fuzzer=");  //parsing reference-verificator with arguments
   if(value != NULL){
   k = 7;
   bool arguments = false;
   string argument;
   string fuz;
   vector<string> fuz_arguments;
   while(value[k] != ';'){
     if(value[k] == ','){
       
       if(!arguments) arguments =true; 
       else{ fuz_arguments.push_back(argument); argument ="";}
                    
    }
    
     else if(value[k] == '|'){
       fuzzer.push_back(fuz); 
       fuz=""; 
       if(argument != ""){ fuz_arguments.push_back(argument); argument ="";}
       fuzzer_arguments.push_back(fuz_arguments);
       fuz_arguments.clear();  
       arguments = false;
    }
    
     else if(!arguments) fuz += value[k];
     
     else if(arguments) argument += value[k];
     
    
     
     k++;
    }
    if(fuz != "") fuzzer.push_back(fuz);  
    if(argument != "") fuz_arguments.push_back(argument);
    fuzzer_arguments.push_back(fuz_arguments);
   }
   else{ cerr<<"no Fuzzer in configuration"<<endl; exit(1);}
}


//=================================================================================================
// Main:

int main(int argc, char** argv)
{  
  
  SAT = true;
  tautologies = false;
  specific_cnf = false;
  method =7;
  
  count = 10;
  deletion_info = 1;
	
  parseConfiguration();
  verificator = ref_verificator;
  
  parseOptions(argc, argv);
  
  arg_solver= new const char* [solver_arguments.size()+4];
	 arg_solver[0] = "solver@fuzzer";
	 arg_solver[1] = "formula";
	 arg_solver[2] = "proof";
	 for(int i=0; i<solver_arguments.size();++i) arg_solver[3+i] = (solver_arguments[i].c_str());
	 //execl(solver.c_str(), const_cast<char*>("solver"), "formula", "proof", NULL);
	 arg_solver[solver_arguments.size()+3] = NULL;
        
  arg_ref_verificator= new const char* [ref_verificator_arguments.size()+4];
	 arg_ref_verificator[0] = "ref_verificator@fuzzer";
	 arg_ref_verificator[1] = "formula";
	 arg_ref_verificator[2] = "proof";
	 for(int i=0; i<ref_verificator_arguments.size();++i) arg_ref_verificator[3+i] = (ref_verificator_arguments[i].c_str());
	 //execl(solver.c_str(), const_cast<char*>("solver"), "formula", "proof", NULL);
	 arg_ref_verificator[ref_verificator_arguments.size()+3] = NULL;
	 
   arg_verificator= new const char* [verificator_arguments.size()+4];
	 arg_verificator[0] = "tested_verificator@fuzzer";
	 arg_verificator[1] = "formula";
	 arg_verificator[2] = "proof";
	 for(int i=0; i<verificator_arguments.size();++i) arg_verificator[3+i] = (verificator_arguments[i].c_str());
	 //execl(solver.c_str(), const_cast<char*>("solver"), "formula", "proof", NULL);
	 arg_verificator[verificator_arguments.size()+3] = NULL;
	 
	
 if(access(ref_verificator.c_str(), 00) != 0){cerr<<"cant access ref_verificator"<<endl; exit(1);}	 
 if(access(verificator.c_str(), F_OK) != 0){cerr<<"cant access tested verificator"<<endl; exit(1);}
 if(access(solver.c_str(), F_OK) != 0){cerr<<"cant access solver"<<endl; exit(1);}
 if(!specific_cnf){
 for(int i=0; i<fuzzer.size();++i) if(access(fuzzer[i].c_str(), F_OK) != 0){cerr<<"cant access fuzzer "<<i<<endl; exit(1);}
 }	
	cerr<<"CONFIGURATION:\n"<<"Solver: "<<solver<<" with the following arguments: "<<endl;
	for(int i=0; i<solver_arguments.size();++i) cerr<<solver_arguments[i]<<endl;
	cerr<<"Reference-Verificator: "<<ref_verificator<<" with the following arguments: "<<endl;
	for(int i=0; i<ref_verificator_arguments.size();++i) cerr<<ref_verificator_arguments[i]<<endl;
	cerr<<"Checked Verificator: "<<verificator<<" with the following arguments: "<<endl;
	for(int i=0; i<verificator_arguments.size();++i) cerr<<verificator_arguments[i]<<endl;
	
        Verificator_Caller* verificator_totest = new Verificator_Caller();
	
	srand (time(NULL)); 
	
	verificator_totest->set_Verificator(verificator);  
            
	if(specific_cnf){
	  Cnf_Reader* cnf_reader = new Cnf_Reader(path);      
		cerr<<"reset count, testing " << cnf_reader->get_c_formula() <<" specific formula"<<endl;
		while(cnf_reader->has_next()){ test_verificator(verificator_totest, deletion_info, cnf_reader);}
	
		delete cnf_reader;
	}
	else{
	  while(count>unsat) test_verificator(verificator_totest, deletion_info, NULL);
	}
	
	cerr<< verificator<<" worked on every formula correctly"<<endl;
	
	evaluation();

	delete verificator_totest;
	delete arg_solver;
	delete arg_ref_verificator;
	delete arg_verificator;
        
	return 0;
	 
 }
