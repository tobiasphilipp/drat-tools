#include "Cnf_Reader.h"
#include <dirent.h> 
#include <stdio.h> 
#include <iostream>
#include <stdlib.h>
#include <string.h>
#include <sstream>
#include <fstream>

Cnf_Reader::Cnf_Reader(std::string path)
{
  curr_index =0;
  this->path = path +"/cnf/";
  c_formula = get_cnf_dir();
}

int Cnf_Reader::get_cnf_dir()
{
  DIR           *d;
  struct dirent *dir;
  d = opendir(this->path.c_str());
  std::string to_push;
  
  if (d)
  {
  
    while ((dir = readdir(d)) != NULL)
    {
      if(dir->d_name[0] == '.') continue;
      to_push = std::string(dir->d_name);

      formulas.push_back(to_push);
    }
    closedir(d);
  }
  
  return formulas.size();
  
}

bool Cnf_Reader::has_next()
{
return curr_index < c_formula;
}

const char* Cnf_Reader::next()
{
  if(!has_next()){ std::cerr<<"no following object"<<std::endl; exit(1);}
  curr_index++;
  
  return formulas[curr_index-1].c_str();
  
}





