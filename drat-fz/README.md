Author: Elias Werner
Mail: elias.werner@tu-dresden.de

Tool, fuzzing cnf-proof-checker

  Description 
  -----------
  This tool performs the following:
  - Generate an unsatisfiable CNF-formula using an arbitrary fuzzer or use specific formula, in the /cnf-directory
  - Generate an appertaining proof using an arbitrary solver
  - Verifiying the proof by the test-verificator and checking it against an arbitrary reference-verificator

  - every tool can be exchanged (see config)

  Installation
  ------------
  1) Build the tool: 
     -mkdir build
     -cd build
     -cmake ..
     -make
  
  2) Define the locations of the tools in config
 
  3) Run the fuzzer (for execution information use './fuzzer -h')


  Sample Run 
  ----------
   ./fuzzer -v=../tested_verificator -c=100


  Additional configuration
  ------------------------
  - The verificator has to verify the proof printing "s VERIFIED" [equal to drat-trim]
  - The Solver has to decide whether the formula is satisfiable (returnvalue 10) or unsatisfiable (returnvalue 20) [equal to minisat]
