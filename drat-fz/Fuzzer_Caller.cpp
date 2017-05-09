#include "Fuzzer_Caller.h"
#include <unistd.h>
#include <iostream>
#include <fcntl.h>
#include <vector>
#include <stdio.h>


using namespace std;

void Fuzzer_Caller::call_Fuzzer()
{
                   
	    remove("formula"); //TODO: dont remove the file, just clear it
            int fd = open("formula", O_RDWR | O_CREAT, S_IRUSR | S_IWUSR);
            dup2(fd,1);
            close(fd);
            
	  // char *arguments[4] = {"q"};
	    
	    
	    
            execv(fuzzer.c_str(), (char **) arg_fuzzer);
	   
  
}

void Fuzzer_Caller::setFuzzer(string fuzzer, const char** arg)
{
this->fuzzer = fuzzer;
this->arg_fuzzer =arg;
}


