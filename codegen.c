#include <stdio.h>

#include "codegen.h"
#include "table.h"

FILE *codegenout;  // the output of code generation

#define PUSH(arg1) fprintf(codegenout,  "\tpush\t%s\n", arg1 )
#define POP(arg1) fprintf(codegenout,  "\tpop\t%s\n", arg1 )
#define MOV(arg1, arg2) fprintf(codegenout, "\tmov\t%s, %s\n", arg1, arg2)
#define MOV_FROM_IMMEDIATE(arg1, arg2) fprintf(codegenout, "\tmov\t$%d, %s\n", arg1, arg2)
#define MOV_FROM_OFFSET(offset, reg) fprintf(codegenout, "\tmov\t-%d(%%rbp), %s\n", offset, reg)
#define MOV_TO_OFFSET(reg, offset) fprintf(codegenout, "\tmov\t%s, -%d(%%rbp)\n", reg, offset)
#define MOV_FROM_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s(%%rip), %s\n", global, reg)
#define MOV_TO_GLOBAL(reg, global) fprintf(codegenout, "\tmov\t%s, %s(%%rip)\n", reg, global)
#define ADD(arg1, arg2) fprintf(codegenout, "\tadd\t%s, %s\n", arg1, arg2)
#define SUB(arg1, arg2) fprintf(codegenout, "\tsub\t%s, %s\n", arg1, arg2)
#define SUBCONST(arg1, arg2) fprintf(codegenout, "\tsub\t$%d, %s\n", arg1, arg2)
#define IMUL(arg1, arg2) fprintf(codegenout, "\timul\t%s, %s\n", arg1, arg2)
#define COMMENT(arg1) fprintf(codegenout, "\t# %s\n", arg1)

#define CMP0(arg) fprintf(codegenout,"\tcmp $0, %s\n", arg)
#define CMP(arg1, arg2) fprintf(codegenout,"\tcmp %s, %s\n", arg1, arg2)
#define JE(labelnum) fprintf(codegenout,"\tje .L%d\n", labelnum)
#define JL(labelnum) fprintf(codegenout,"\tjl .L%d\n", labelnum)
#define JLE(labelnum) fprintf(codegenout,"\tjle .L%d\n", labelnum)
#define JG(labelnum) fprintf(codegenout,"\tjg .L%d\n", labelnum)
#define JGE(labelnum) fprintf(codegenout,"\tjge .L%d\n", labelnum)
#define JMP(labelnum) fprintf(codegenout,"\tjmp .L%d\n", labelnum)
#define LABEL(labelnum) fprintf(codegenout,".L%d:\n", labelnum)
#define JNE(labelnum) fprintf(codegenout,"\tjne .L%d\n", labelnum)

const string const param_registers[] = { "%rdi", "%rsi", "%rdx", "%rcx", "%r8", "%r9"}; // all const

static void codegen_main(T_main main);

static void codegen_decllist(T_decllist decllist);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_funclist(T_funclist funclist); 

static void codegen_func(T_func func);

static void codegen_stmtlist(T_stmtlist stmtlist);

static void codegen_stmt(T_stmt stmt);

static void codegen_assignstmt(T_stmt stmt);

static void codegen_ifstmt(T_stmt stmt);

static void codegen_ifelsestmt(T_stmt stmt);

static void codegen_whilestmt(T_stmt stmt);

static void codegen_compoundstmt(T_stmt stmt);

static void codegen_expr(T_expr expr);

static void codegen_identexpr(T_expr expr);

static void codegen_callexpr(T_expr expr);

static void codegen_intexpr(T_expr expr);

static void codegen_charexpr(T_expr expr);

static void codegen_strexpr(T_expr expr);

static void codegen_arrayexpr(T_expr expr);

static void codegen_unaryexpr(T_expr expr);

static void codegen_binaryexpr(T_expr expr);

static void codegen_castexpr(T_expr expr);

static void emit_prologue(int size);

static void emit_epilogue();

static int bitwidth(T_type type);

typedef struct S_offset_scope *T_offset_scope;

struct S_offset_scope {
  T_table table;
  int stack_size;
  int current_offset;
  T_offset_scope parent;
};

static T_offset_scope create_offset_scope(T_offset_scope parent) {
  T_offset_scope offset_scope = xmalloc(sizeof(*offset_scope));
  offset_scope->table = create_table();
  // start after the dynamic link to the caller's %rbp
  offset_scope->current_offset = 8;
  offset_scope->stack_size = 0;
  offset_scope->parent = parent;
  return offset_scope;
}

static T_offset_scope destroy_offset_scope(T_offset_scope offset_scope) {
  T_offset_scope parent_offset_scope = offset_scope->parent;
  destroy_table(offset_scope->table);
  free(offset_scope);
  return parent_offset_scope;
}

struct S_offset {
  int offset;
};

typedef struct S_offset * T_offset;

static T_table global_symbols;

static T_offset_scope current_offset_scope;

void insert_offset(T_offset_scope scope, string ident, int size) {
  T_offset entry = xmalloc(sizeof(*entry));
  entry->offset = scope->current_offset;
  insert(scope->table, ident, (void*) entry);
  scope->stack_size += size;
  scope->current_offset += size;
}

static int lookup_offset_in_scope(T_offset_scope offset_scope, string ident) {
  T_offset offset = (T_offset) lookup(offset_scope->table, ident);
  if (NULL == offset) {
    fprintf(stderr, "FATAL: symbol not in table.  double-check the code that inserts the symbol into the offset scope.");
  }
  return offset->offset;
}

static T_offset lookup_offset_in_all_offset_scopes(T_offset_scope offset_scope, string ident) {
  // loop over each offset_scope and check for a binding for ident
  while (NULL != offset_scope) {
    // check for a binding in this offset_scope
    T_offset offset = (T_offset) lookup(offset_scope->table, ident);
    if (NULL != offset) {
      return offset;
    }
    // no binding in this offset_scope, so check the parent
    offset_scope = offset_scope->parent;
  }
  // found no binding in any offset_scope
  return NULL;
}

void codegen(T_prog prog) {
  // no need to record symbols in the global offset_scope.  the assembler and linker handle them.
  current_offset_scope = NULL;
  
  // emit assembly header
  fprintf(codegenout, ".file \"stdin\"\n");
  
  // emit a .comm for global vars
  global_symbols = create_table();
  // loop over each global symbol.  emit .comm and add to global symtab
  T_decllist decllist = prog->decllist;
  while (NULL != decllist) {
    if (E_functiontype != decllist->decl->type->kind) {
      fprintf(codegenout, ".comm\t%s,%d\n", decllist->decl->ident, bitwidth(decllist->decl->type));
      insert(global_symbols, decllist->decl->ident, decllist->decl->ident);
    }
    decllist = decllist->tail;
  }

  // optional: emit an .rodata section and label for strings

  // go through each function
  codegen_funclist(prog->funclist);

  // generate the code for main
  codegen_main(prog->main);

  // free the global symbol table
  free(global_symbols);
}

static void codegen_main(T_main main) {
  // create a new scope
  current_offset_scope = create_offset_scope(NULL);

  // emit the pseudo ops for the function definition
  fprintf(codegenout, ".text\n");
  fprintf(codegenout, ".globl %s\n", "main");
  fprintf(codegenout, ".type %s, @function\n", "main");

  // emit a label for the function
  fprintf(codegenout, "%s:\n", "main");

  // add local declarations to the scope
  codegen_decllist(main->decllist);

  COMMENT("stack space for argc and argv");
  insert_offset(current_offset_scope, "argc", 8);  // int argc
  insert_offset(current_offset_scope, "argv", 8);  // char **argv

  COMMENT("emit main's prologue");
  emit_prologue(current_offset_scope->stack_size);

  COMMENT("move argc and argv from parameter registers to the stack");
  int offset;
  offset = lookup_offset_in_scope(current_offset_scope, "argc");
  MOV_TO_OFFSET("%rdi", offset);
  offset = lookup_offset_in_scope(current_offset_scope, "argv");
  MOV_TO_OFFSET("%rsi", offset);
  
  COMMENT("generate code for the body");
  codegen_stmtlist(main->stmtlist);

  COMMENT("generate code for the return expression");
  codegen_expr(main->returnexpr);
  COMMENT("save the return expression into %rax per the abi");
  POP("%rax");

  COMMENT("emit main's epilogue");
  emit_epilogue();

  // exit the scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_funclist(T_funclist funclist) {
  while (NULL != funclist) {
    codegen_func(funclist->func);
    funclist = funclist->tail;
  }
}

static void codegen_func(T_func func) {
  // Create a new scope for the function
  current_offset_scope = create_offset_scope(current_offset_scope);

  // Emit pseudo-ops for the function definition
  fprintf(codegenout, ".text\n.globl %s\n.type %s, @function\n", func->ident, func->ident);

  // Emit a label for the function
  fprintf(codegenout, "%s:\n", func->ident);
  T_paramlist paramlist = func->paramlist;
  int param_index = 0;
  
  // Update stack size and offsets for parameters before emitting the prologue
  while (paramlist != NULL) {
    if (param_index < 6) { // For parameters that are passed in registers
      // Calculate and insert stack offset for parameter
      insert_offset(current_offset_scope, paramlist->ident, 8); // Assuming all parameters are 64-bit (8)
      
      // Move parameter from register to its stack location
      int offset = lookup_offset_in_scope(current_offset_scope, paramlist->ident);
      MOV_TO_OFFSET(param_registers[param_index], offset);
    }
    paramlist = paramlist->tail;
    param_index++;
  }

  // Add local declarations to the scope
  codegen_decllist(func->decllist);

  // Emit the function prologue
  emit_prologue(current_offset_scope->stack_size); 

  // Generate code for the body of the function
  codegen_stmtlist(func->stmtlist);

  //BUG 

  //code for return expression
  codegen_expr(func->returnexpr);

  POP("%rax");

  // Emit the function epilogue
  emit_epilogue();

  // Destroy the function's scope
  current_offset_scope = destroy_offset_scope(current_offset_scope);
}

static void codegen_decllist(T_decllist decllist) {
  //loop over each element in the decllist list
  while (decllist != NULL)
  {
    //insert each element into the offset_scope (assume all values in the stack have an offset of 8 bytes)
    int size = 8;

    //insert variable into current scope with appropriate size
    insert_offset(current_offset_scope, decllist->decl->ident, size);

    //move to the next declaration in the list
    decllist = decllist->tail;
  }

}

/* statements */
static void codegen_stmtlist(T_stmtlist stmtlist) {
  while (NULL != stmtlist) {
    codegen_stmt(stmtlist->stmt);
    stmtlist = stmtlist->tail;
  }
}

static void codegen_stmt(T_stmt stmt) {
  if (NULL == stmt) {
    fprintf(stderr, "FATAL: stmt is NULL in codegen_stmt\n");
    exit(1);
  }
  switch (stmt->kind) {
  case E_assignstmt: codegen_assignstmt(stmt); break;
  case E_ifstmt: codegen_ifstmt(stmt); break;
  case E_ifelsestmt: codegen_ifelsestmt(stmt); break;
  case E_whilestmt: codegen_whilestmt(stmt); break;
  case E_compoundstmt: codegen_compoundstmt(stmt); break;
  default: fprintf(stderr, "FATAL: unexpected stmt kind in codegen_stmt\n"); exit(1); break;
  }
}

static void codegen_assignstmt(T_stmt stmt) { //PROJECT 4
  // Gen. code right-hand side
  codegen_expr(stmt->assignstmt.right);
  POP("%rax"); 

  // Check left-hand side; deref
  if (stmt->assignstmt.left->kind == E_unaryexpr) 
  {
        
        // Gen. code for l-express.; deref
        codegen_expr(stmt->assignstmt.left->unaryexpr.expr);
        
        // Gen. code for r-express.
        codegen_expr(stmt->assignstmt.right); 
        
        // Pop result from stack into rax
        POP("%rax");
        // Pop result address from stack into rbx
        POP("%rbx");

        // Move value from register to address pointed to by l-express.
        MOV("%rax", "(%rbx)");
  } 

  else 
  {
      // Generate code for r-expression
      codegen_expr(stmt->assignstmt.right); 

      // Pop resulting value from stack into rax
      POP("%rax");

      // Lookup offset
      int offset = lookup_offset_in_scope(current_offset_scope, stmt->assignstmt.left->identexpr);

      // Move the value from register to stack add.
      MOV_TO_OFFSET("%rax", offset);
  }
  
}


// Assuming you have a global variable for label counter  
static int label_counter = 0;  

static void codegen_ifstmt(T_stmt stmt) { //Function to generate code for if statement  
    // The label for the end of the if branch, to skip the if body if the condition is false  
    int after_if_label = label_counter++;  
      
    // Generate code for the condition and get the result in %rax  
    codegen_expr(stmt->ifstmt.cond);  
    POP("%rax");  // Pop the value from the stack to %rax, assuming the result of the condition is now in %rax  
  
    // Compare the result to "false" (0) and jump to the label after the if statement if condition is false  
    CMP0("%rax");   
    JE(after_if_label); // If condition is false, jump to the end of the if statement  
  
    // Execute the if branch  
    codegen_stmt(stmt->ifstmt.body); // Generate code for the body of the if statement  
  
    // Label for first instruction after the if statement  
    LABEL(after_if_label);  
}  
  
static void codegen_ifelsestmt(T_stmt stmt) { //Function to generate code for if-else statement  
  // Labels for the else branch and the code following the if-else statement  
  int else_label = label_counter++;  
  int after_ifelse_label = label_counter++;  
  
  // Generate code for the condition and store the result in %rax  
  codegen_expr(stmt->ifelsestmt.cond);  
  POP("%rax"); // Pop the value from the stack to %rax  
    
  // Compare to "false" and jump to the else branch if condition is false  
  CMP0("%rax");  
  JE(else_label); // If condition is false, jump to the else branch  
  
  // Execute the if branch  
  codegen_stmt(stmt->ifelsestmt.ifbranch); // Generate code for the if branch  
    
  // Unconditionally jump past else branch  
  JMP(after_ifelse_label); // After executing if branch, jump to the end of the if-else statement  
  
  // Label for the else branch  
  LABEL(else_label);  
  codegen_stmt(stmt->ifelsestmt.elsebranch); // Generate code for the else branch  
  
  // Label for the first instruction after the if-else statement  
  LABEL(after_ifelse_label);  
}  
  
static void codegen_whilestmt(T_stmt stmt) { //Function to generate code for while statement  
  // Labels for the start and end of the while loop  
  int start_label = label_counter++;  
  int end_label = label_counter++;  
  
  // Label at the start of the loop, where the condition will be re-evaluated each iteration  
  LABEL(start_label);  
  
  // Generate code for the condition expression and store the result in %rax  
  codegen_expr(stmt->whilestmt.cond);  
  POP("%rax"); // Pop the value from the stack to %rax  
  
  // Compare the result to "false" and jump to the end of the loop if false  
  CMP0("%rax");  
  JE(end_label); // If condition is false, jump to the end of the while loop  
  
  // Execute the while loop body  
  codegen_stmt(stmt->whilestmt.body); // Generate code for the body of the while loop  
  
  // Unconditionally jump to the loop head to re-evaluate the condition  
  JMP(start_label); // After executing body, jump back to the start of the loop to evaluate condition again  
  
  // Label for the first instruction after the while statement  
  LABEL(end_label);  
}  


static void codegen_compoundstmt(T_stmt stmt) { 
  //generate the code for the body of the compound statement
  codegen_stmtlist(stmt->compoundstmt.stmtlist); 
}

/* expressions */
static void codegen_expr(T_expr expr) {
  if (NULL == expr) {
    fprintf(stderr, "FATAL: unexpected NULL in codegen_expr\n");
    exit(1);
  }
  switch (expr->kind) {
  case E_identexpr: codegen_identexpr(expr); break;
  case E_callexpr: codegen_callexpr(expr); break;
  case E_intexpr: codegen_intexpr(expr); break;
  case E_charexpr: codegen_charexpr(expr); break;
  case E_strexpr: codegen_strexpr(expr); break;
  case E_arrayexpr: codegen_arrayexpr(expr); break;
  case E_unaryexpr: codegen_unaryexpr(expr); break;
  case E_binaryexpr: codegen_binaryexpr(expr); break;
  case E_castexpr: codegen_castexpr(expr); break;
  default: fprintf(stderr, "FATAL: unexpected expr kind in codegen_expr\n"); exit(1); break;
  }
}

static void codegen_identexpr(T_expr expr) {
  // todo: given in class
  //look up the ident, then move it to an intermidate register
  int offset = lookup_offset_in_scope(current_offset_scope, expr->identexpr);
  MOV_FROM_OFFSET(offset, "%rax");
  PUSH("%rax");
}

static void codegen_callexpr(T_expr expr) {
  codegen_expr(expr->callexpr.args->expr);

  POP("%rdi");

  CALL(expr->callexpr.ident);

  PUSH("%rax"); 
}

static void codegen_intexpr(T_expr expr) {
  //move the immediate value into a register and push it onto the stack
  MOV_FROM_IMMEDIATE(expr->intexpr, "%rax");
  PUSH("%rax"); 
}

static void codegen_charexpr(T_expr expr) {
  COMMENT("push the character");
  MOV_FROM_IMMEDIATE((int) expr->charexpr, "%rax");
  PUSH("%rax");
}

static void codegen_strexpr(T_expr expr) {
  // bonus exercise
  int temp = atoi(expr ->strexpr);
  MOV_FROM_IMMEDIATE(temp, "%rax");
  PUSH("%rax");
}

static void codegen_arrayexpr(T_expr expr) {
  // bonus exercise
}

static void codegen_unaryexpr(T_expr expr) { //PROJECT 4 
  // Check the operator type
  switch(expr->unaryexpr.op) {
    case E_op_ref: // Reference operator '&'
      // Ensure that the expression to reference is an identifier
      if (expr->unaryexpr.expr->kind != E_identexpr) {
        fprintf(stderr, "FATAL: Unary expression operand must be an identifier\n");
        exit(1);
      }

      // Save the base pointer to another register (e.g., rax)
      fprintf(codegenout, "\tmov\t%%rbp, %%rax\n");

      // Lookup the identifier's offset in the current scope
      int offset = lookup_offset_in_scope(current_offset_scope, expr->unaryexpr.expr->identexpr);

      // Compute the address by subtracting the offset from the base pointer copy in rax
      fprintf(codegenout, "\tsub\t$%d, %%rax\n", offset);

      // Save the result by pushing it onto the stack
      fprintf(codegenout, "\tpush\t%%rax\n");
      break;

    case E_op_deref: // Dereference operator '*'
      // Generate code for the expression inside the unary expression
      codegen_expr(expr->unaryexpr.expr);

      // Pop the result from the stack into a register (e.g., rax)
      fprintf(codegenout, "\tpop\t%%rax\n");

      // Load the value from the memory address pointed to by rax into rax
      fprintf(codegenout, "\tmov\t(%%rax), %%rax\n");

      // Push the dereferenced value onto the stack
      fprintf(codegenout, "\tpush\t%%rax\n");
      break;

    case E_op_not: // Logical negation operator '!'
      // Generate code for the expression inside the unary expression
      codegen_expr(expr->unaryexpr.expr);

      // Pop the result from the stack into a register (e.g., rax)
      fprintf(codegenout, "\tpop\t%%rax\n");

      // Compare the result to zero and set the zero flag (ZF) accordingly
      fprintf(codegenout, "\tcmp\t$0, %%rax\n");

      // Set rax to 1 if ZF is set (logical not)
      fprintf(codegenout, "\tsete\t%%al\n");

      // Move the result into rax
      fprintf(codegenout, "\tmovzbq\t%%al, %%rax\n");

      // Push the result onto the stack
      fprintf(codegenout, "\tpush\t%%rax\n");
      break;

    default:
      fprintf(stderr, "FATAL: Unsupported unary operator\n");
      exit(1);
  }
}

static void codegen_binaryexpr(T_expr expr) { //PROJECT 4
    assert(expr && expr->kind == E_binaryexpr);  // Ensure we have a binary expression

    // Generate code for the left operand
    codegen_expr(expr->binaryexpr.left);
    // Generate code for the right operand
    codegen_expr(expr->binaryexpr.right);

    // Pop the right operand into %rbx (it was pushed last)
    POP("%rbx");
    // Pop the left operand into %rax
    POP("%rax");

    // Apply the binary operator
    switch (expr->binaryexpr.op) {
        case E_op_plus:
            ADD("%rbx", "%rax");  // Result of rax + rbx will be in %rax
            break;
        case E_op_minus:
            if (expr->binaryexpr.left->kind == E_pointertype) { // Left operand is a pointer
            // Scale right operand by size of the type pointed to
            fprintf(codegenout, "\timul $%d, %%rbx\n", (int)sizeof(int)); 
            }
            SUB("%rbx", "%rax");
            break;
        case E_op_times:
            IMUL("%rbx", "%rax"); // Result of rax * rbx will be in %rax
            break;
        case E_op_divide:
            // Prepare %rdx:%rax for division
            CDQ();
            // IDIV uses %rax for the dividend and places quotient in %rax, remainder in %rdx
            IDIV("%rbx");
            break;
        
        case E_op_and:
            // Generate code for the left operand
            codegen_expr(expr->binaryexpr.left);
            // Generate code for the right operand
            codegen_expr(expr->binaryexpr.right);

            // Pop the right operand into %rbx (it was pushed last)
            POP("%rbx");
            // Pop the left operand into %rax
            POP("%rax");

            // Perform logical AND operation
            // In assembly, we can use AND instruction to perform logical AND
            fprintf(codegenout, "\tand %%rbx, %%rax\n");

            // Push the result onto the stack
            PUSH("%rax");
            break;
        
        case E_op_or:
            // Generate code for the left operand
            codegen_expr(expr->binaryexpr.left);
            // Generate code for the right operand
            codegen_expr(expr->binaryexpr.right);

            // Pop the right operand into %rbx (it was pushed last)
            POP("%rbx");
            // Pop the left operand into %rax
            POP("%rax");

            // Perform logical OR operation
            // In assembly, we can use OR instruction to perform logical OR
            fprintf(codegenout, "\tor %%rbx, %%rax\n");

            // Push the result onto the stack
            PUSH("%rax");
            break;

        case E_op_eq:
            // Generate code for the left operand
            codegen_expr(expr->binaryexpr.left);
            // Generate code for the right operand
            codegen_expr(expr->binaryexpr.right);

            // Pop the right operand into %rbx (it was pushed last)
            POP("%rbx");
            // Pop the left operand into %rax
            POP("%rax");

            // Compare the left and right operands
            fprintf(codegenout, "\tcmp %%rbx, %%rax\n");
            // Set ZF if the operands are equal
            fprintf(codegenout, "\tsete %%al\n");
            // Move zero-extended AL register to AX
            fprintf(codegenout, "\tmovzbq %%al, %%rax\n");

            // Push the result onto the stack
            PUSH("%rax");
            break;
        
        case E_op_lt:
            // Generate code for the left operand
            codegen_expr(expr->binaryexpr.left);
            // Generate code for the right operand
            codegen_expr(expr->binaryexpr.right);

            // Pop the right operand into %rbx (it was pushed last)
            POP("%rbx");
            // Pop the left operand into %rax
            POP("%rax");

            // Compare the left and right operands
            fprintf(codegenout, "\tcmp %%rbx, %%rax\n");
            // Set SF and OF flags to 1 if the left operand is less than the right operand
            fprintf(codegenout, "\tsetl %%al\n");
            // Move zero-extended AL register to AX
            fprintf(codegenout, "\tmovzbq %%al, %%rax\n");

            // Push the result onto the stack
            PUSH("%rax");
            break;

        // Add cases for other operators as necessary
        default:
            fprintf(stderr, "Unsupported binary operator\n");
            exit(1);
    }

    // Push the result onto the stack
    PUSH("%rax");
}

static void codegen_castexpr(T_expr expr) {
  // bonus: truncate or extend data between bitwidths depending on type  
  // Cast the expression to the desired type
  codegen_expr(expr->castexpr.expr);
}

/**
 * Emit a function prologue, given some size in bytes of the local
 * variables in the stack frame.
 */
static void emit_prologue(int size) {
	//save stack
	PUSH("%rbp");
	MOV("%rsp", "%rbp");
	if (size > 0) {
		SUBCONST(size, "%rsp");
	}
	PUSH("%rbx");
}

static void emit_epilogue() {
	POP("%rbx");
	MOV("%rbp", "%rsp");
	POP("%rbp");
	RET;
}

/**
 * This function returns the size of a type in bytes.
 */
static int bitwidth(T_type type) {
  switch (type->kind) {
  case E_primitivetype:
    switch (type->primitivetype) {
    case E_typename_int:
      // 32-bit integers
      return 4;
    case E_typename_char:
      // characters are 1 byte
      return 1;
    default:
      fprintf(stderr, "FATAL: unexpected kind in compare_types\n");
      exit(1);
    }
    break;
  case E_pointertype:
    // pointers are to 64-bit addresses
    return 8;
  case E_arraytype:
    // arrays are the size times the bitwidth of the type
    return type->arraytype.size * bitwidth(type->arraytype.type);
  case E_functiontype:
    fprintf(stderr, "FATAL: functions as values are not supported\n");
    exit(1);
    break;
  default:
    fprintf(stderr, "FATAL: unexpected kind in bitwidth\n");
    exit(1);
    break;
  }  
}
