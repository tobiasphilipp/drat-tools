#include "Verificator_Caller.h"
#include <unistd.h>
#include <iostream>
#include <fcntl.h>
#include <vector>
#include <stdio.h>
#include <fstream>
#include <string.h>
#include <stdlib.h> 
#include <errno.h>
#include <sys/wait.h>




using namespace std;

void Verificator_Caller::call_Verificator(const char **arg_verificator)
{
  
  remove("verification"); //TODO: dont remove the file, just clear it
             int fd = open("verification", O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
            dup2(fd,1);
	    dup2(fd,2);
            close(fd);
	    execv(verificator.c_str(), (char **) arg_verificator);
}

bool Verificator_Caller::set_Verificator(string verf){
  this->verificator = verf;
  
  return true;
}

bool Verificator_Caller::check_verification(bool drat_trim)
{
ifstream verf("verification", ifstream::binary);
  
  if(!verf.is_open()){
    cerr<<"cant open verification"<<endl;
    exit(1);
    }
    
    verf.seekg(0,verf.end);
   int length = verf.tellg();
   verf.seekg(0, verf.beg);
   
   char * buffer = new char [length];
   verf.read(buffer,length);
   
   char* verified;
   
   drat_trim ? verified = strstr(buffer, "s VERIFIED\n") : verified = strstr(buffer, "was successful!");  
   
   
   if(verified == NULL ){ 
     results.push_back(false);
    }
   else{ results.push_back(true);}
   
   delete[] buffer;
   verf.close();
   
   return results[results.size()-1];
}

vector<string> Verificator_Caller::destroy_information(string way, vector<string> clause)
{
  
for(int i=0; i<clause.size();++i) this->info.push_back( clause[i] + "by " + way);

return this->info;
}



