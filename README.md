# -compiler-for-Chez-Scheme
 compiler for Chez Scheme programming language, the Compiler written  in Ocaml, and it converts scheme code to assembly x86.
 *******************************************************************************************************************************
The compiler consists of 4 parts:

Part 1:
  Reader: it takes scheme code (string) as input, and it generate an sexpr as its output.

Part 2:
  Tag-Parser: it takes sexpr as input(the output of part 1), and it generate expr as its output.

Part 3:
  Semantic-Analyser: it takes expr as input(the output of part 2), and it generate expr' as its output.

Part 4:
  Code-gen: it takes expr' as input(the output of part 1), and it generate assembly code as its output.
 
