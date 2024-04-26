#include <stdio.h>

#include "ast.h"

#include "ast_printer.h"

#include "codegen.h"

extern int yyparse (void);  // the entrypoint to the parser

extern FILE *yyout;  // the output of flex

extern T_prog program_ast;  // the output of bison

extern FILE *codegenout;  // the output of code generation

int main(int argc, char **argv) {
  /* while (1) { */
  /*   yylex(); */
  /* } */

  // print input program and parse errors to stderr
  yyout = stderr;

  // kick off the parser, which will store the result in program_ast
  yyparse();

  codegenout = stdout;
  
  // generate the machine code, which writes to stdout, using the annotated ast and symtab
  codegen(program_ast);
}
