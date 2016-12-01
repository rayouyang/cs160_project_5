#include <iostream>
#include <cstdio>
#include <cstring>
#include <list>
#include "ast.hpp"
#include "symtab.hpp"
#include "primitive.hpp"
#include "assert.h"

// WRITEME: The default attribute propagation rule
#define default_rule(X) \
    (X)->m_attribute.m_scope=m_st->get_scope(); \
    (X)->visit_children(this);
#include <typeinfo>

class Typecheck : public Visitor
{
  private:
    FILE* m_errorfile;
    SymTab* m_st;
    bool flag;

    // The set of recognized errors
    enum errortype
    {
        no_main,
        nonvoid_main,
        dup_proc_name,
        dup_var_name,
        proc_undef,
        call_type_mismatch,
        narg_mismatch,
        expr_type_err,
        var_undef,
        ifpred_err,
        whilepred_err,
        incompat_assign,
        who_knows,
        ret_type_mismatch,
        array_index_error,
        no_array_var,
        arg_type_mismatch,
        expr_pointer_arithmetic_err,
        expr_abs_error,
        expr_addressof_error,
        invalid_deref
    };

    // Print the error to file and exit
    void t_error(errortype e, Attribute a)
    {
        fprintf(m_errorfile,"on line number %d, ", a.lineno);

        switch(e)
        {
            case no_main:
                fprintf(m_errorfile, "error: no main\n");
                exit(2);
            case nonvoid_main:
                fprintf(m_errorfile, "error: the Main procedure has arguments\n");
                exit(3);
            case dup_proc_name:
                fprintf(m_errorfile, "error: duplicate procedure names in same scope\n");
                exit(4);
            case dup_var_name:
                fprintf(m_errorfile, "error: duplicate variable names in same scope\n");
                exit(5);
            case proc_undef:
                fprintf(m_errorfile, "error: call to undefined procedure\n");
                exit(6);
            case var_undef:
                fprintf(m_errorfile, "error: undefined variable\n");
                exit(7);
            case narg_mismatch:
                fprintf(m_errorfile, "error: procedure call has different number of args than declartion\n");
                exit(8);
            case arg_type_mismatch:
                fprintf(m_errorfile, "error: argument type mismatch\n");
                exit(9);
            case ret_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in return statement\n");
                exit(10);
            case call_type_mismatch:
                fprintf(m_errorfile, "error: type mismatch in procedure call args\n");
                exit(11);
            case ifpred_err:
                fprintf(m_errorfile, "error: predicate of if statement is not boolean\n");
                exit(12);
            case whilepred_err:
                fprintf(m_errorfile, "error: predicate of while statement is not boolean\n");
                exit(13);
            case array_index_error:
                fprintf(m_errorfile, "error: array index not integer\n");
                exit(14);
            case no_array_var:
                fprintf(m_errorfile, "error: attempt to index non-array variable\n");
                exit(15);
            case incompat_assign:
                fprintf(m_errorfile, "error: type of expr and var do not match in assignment\n");
                exit(16);
            case expr_type_err:
                fprintf(m_errorfile, "error: incompatible types used in expression\n");
                exit(17);
            case expr_abs_error:
                fprintf(m_errorfile, "error: absolute value can only be applied to integers and strings\n");
                exit(17);
            case expr_pointer_arithmetic_err:
                fprintf(m_errorfile, "error: invalid pointer arithmetic\n");
                exit(18);
            case expr_addressof_error:
                fprintf(m_errorfile, "error: AddressOf can only be applied to integers, chars, and indexed strings\n");
                exit(19);
            case invalid_deref:
                fprintf(m_errorfile, "error: Deref can only be applied to integer pointers and char pointers\n");
                exit(20);
            default:
                fprintf(m_errorfile, "error: no good reason\n");
                exit(21);
        }
    }

    // Helpers
    // WRITEME: You might want write some hepler functions.
    const char* lhs_to_id(Lhs* lhs)
    {
        if(lhs == NULL){
            return nullptr;
        }
        Variable *v = dynamic_cast<Variable*>(lhs);
        if(v) {
            //std::cout << v->m_symname->spelling() << std::endl;
            return v->m_symname->spelling();
        }
        DerefVariable *dv = dynamic_cast<DerefVariable*>(lhs);
        if(dv) {
            return dv->m_symname->spelling();
        }
        ArrayElement *ae = dynamic_cast<ArrayElement*>(lhs);
        if(ae) {
           std::cout << ae->m_attribute.m_basetype << std::endl;
           return ae->m_symname->spelling();
        }
        return nullptr;
    }
    const char* lhs_to_id1(Lhs* lhs)
    {
        if(lhs == NULL){
            return nullptr;
        }
        Variable *v = dynamic_cast<Variable*>(lhs);
        if(v) {
            return v->m_symname->spelling();
        }
        DerefVariable *dv = dynamic_cast<DerefVariable*>(lhs);
        if(dv) {
            return dv->m_symname->spelling();
        }
        return nullptr;
    }
    const char* expr_to_id(Expr* expr){
        if(expr == NULL){
            return nullptr;
        }
        Ident *i = dynamic_cast<Ident*>(expr);
        if(i){
            return i->m_symname->spelling();
        }
        return nullptr;
    }
    // Type Checking
    // WRITEME: You need to implement type-checking for this project

    // Check that there is one and only one main
    void check_for_one_main(ProgramImpl* p)
    {

        char *name; Symbol *s;
        name = strdup("Main");
        s = m_st->lookup(name);
        if(!s){
            this->t_error(no_main,  p->m_attribute);
        }
        if((s->m_arg_type).size() != 0){
            this->t_error(nonvoid_main,  p->m_attribute);
        }
    }

    // Create a symbol for the procedure and check there is none already
    // existing
    void add_proc_symbol(ProcImpl* p)
    {
        char *name; Symbol *s;
        name = strdup(p->m_symname->spelling());
        std::list<Decl_ptr>::iterator iter;
        if(!strcmp(name, strdup("Main"))){
            if (flag) {
                this->t_error(no_main,  p->m_attribute);
            }
            flag = true;
        }
        //std::cout << name << std::endl;
        s = new Symbol();
        //std::cout << p->m_type->m_attribute.m_basetype << std::endl;
        //s->m_basetype = p->m_type->m_attribute.m_basetype;
        s->m_basetype = bt_procedure;
        p->m_type->accept(this);
        s->m_return_type = p->m_type->m_attribute.m_basetype;

        for (iter = p->m_decl_list->begin(); iter != p->m_decl_list->end(); iter++){
            (s->m_arg_type).push_back((*iter)->m_attribute.m_basetype);
            //std::cout << (*iter)->m_attribute.m_basetype << std::endl; 
        }
        //std::cout << s->m_return_type << std::endl;
        if(!m_st->insert(name, s))
            this->t_error(dup_proc_name,  p->m_attribute);
       
    }

    // Add symbol table information for all the declarations following
    void add_decl_symbol(DeclImpl* p)
    {
        char *name; Symbol *s;        
        std::list<SymName_ptr>::iterator iter;
        
        for (iter = p->m_symname_list->begin(); iter != p->m_symname_list->end(); iter++){
            //std::cout << (*iter)->spelling() << std::endl;
            //std::cout << p->m_type->m_attribute.m_basetype << std::endl;
            s = new Symbol();
            s->m_basetype = p->m_type->m_attribute.m_basetype;
            p->m_attribute.m_basetype = p->m_type->m_attribute.m_basetype;
            name = strdup((*iter)->spelling());
            if(!m_st->insert(name, s))
            this->t_error(dup_var_name,  p->m_attribute);
        }
    }

    // Check that the return statement of a procedure has the appropriate type
    void check_proc(ProcImpl *p)
    {
        char *name; Symbol *s;
        name = strdup(p->m_symname->spelling());

        s = m_st->lookup(name);

        if(p->m_attribute.m_basetype != s->m_return_type)
            this->t_error(ret_type_mismatch,  p->m_attribute);
    }

    // Check that the declared return type is not an array
    void check_return(Return *p)
    {
        if(p->m_attribute.m_basetype == bt_string){
            this->t_error(ret_type_mismatch,  p->m_attribute);
        }
    }

    // check_call should check the existence of the function being called, 
    // and make sure types of arguments and return values are consistent.
    void check_call(Call *p)
    {
        char *name; Symbol *s, *s2, *s3;
        const char *name2;
        name = strdup(p->m_symname->spelling());
        //std::cout << name << std::endl;
        s = m_st->lookup(name);
        if(!s){
            this->t_error(proc_undef,  p->m_attribute);
        }

        //std::cout << s->m_return_type << std::endl;
        //std::cout << s2->m_basetype << std::endl;
        
        name2 = lhs_to_id(p->m_lhs);

        
        s2 = m_st->lookup(name2);
        
        if(s2->m_basetype != bt_procedure){

        }

        if(!s2){
            this->t_error(var_undef,  p->m_attribute);
        }
        
        //std::cout << s2->m_basetype << std::endl;
        if(s->m_return_type != s2->m_basetype){
                this->t_error(call_type_mismatch,  p->m_attribute);
        }
        //TODO: add argument checks
            
        if(s->m_arg_type.size() != p->m_expr_list->size()){
            this->t_error(narg_mismatch,  p->m_attribute);   
        }
        std::list<Expr_ptr>::iterator pIter;
        std::vector<Basetype>::iterator sIter;
        const char * name3;
        for (pIter = p->m_expr_list->begin(), sIter =s->m_arg_type.begin(); 
             pIter != p->m_expr_list->end();
             pIter++, sIter++)
        {
            name3 = expr_to_id(*pIter);
            if(!name3){
                this->t_error(arg_type_mismatch,  p->m_attribute);
            }
            s3 = m_st->lookup(expr_to_id(*pIter));
            std::cout << s3->m_basetype << std::endl;
            
            if(s3)
            {
                if(s3->m_basetype != (*sIter))
                {
                    this->t_error(arg_type_mismatch,  p->m_attribute);
                }
            }    
        }
    }

    // For checking that this expressions type is boolean used in if/else
    void check_pred_if(Expr* p)
    {
        if(p->m_attribute.m_basetype != bt_boolean)
        {
            this->t_error(ifpred_err,  p->m_attribute);
        }
    }

    // For checking that this expressions type is boolean used in while
    void check_pred_while(Expr* p)
    {
        if(p->m_attribute.m_basetype != bt_boolean)
        {
            this->t_error(whilepred_err,  p->m_attribute);
        }
    }
    
    /*The types of the left-hand side and the right-hand side of an assignment must match. 
    Note that one can only assign characters to individual string (character array) elements. 
    The NULL pointer can be used as either a char pointer or an integer pointer. 
    If this property is violated, exit with error code 16.*/
    void check_assignment(Assignment* p)
    {
        char *name; Symbol *s, *s2;
        const char *name2;
        Basetype RHS = p->m_expr->m_attribute.m_basetype;
        name2 = lhs_to_id1(p->m_lhs);
        if (name2 == nullptr)
        {
            ArrayElement *ae = dynamic_cast<ArrayElement*>(p->m_lhs);
            if(ae) {
                //std::cout << RHS << std::endl;
                //std::cout << ae->m_attribute.m_basetype << std::endl;
                if(RHS != ae->m_attribute.m_basetype){
                    this->t_error(incompat_assign,  p->m_attribute);
                }
                return;               
            }
        } 
        s2 = m_st->lookup(name2);
        if(!s2){
            this->t_error(var_undef,  p->m_attribute);
        }
        
        //std::cout << p->m_lhs->m_attribute.m_basetype << std::endl;
        //std::cout << RHS << std::endl;
        if(RHS != p->m_lhs->m_attribute.m_basetype){
            this->t_error(incompat_assign,  p->m_attribute);
        }

    }

    void check_string_assignment(StringAssignment* p)
    {
        const char *name; Symbol *s;
        
        name = lhs_to_id(p->m_lhs);
        s = m_st->lookup(name);
        if(!s){
            this->t_error(var_undef,  p->m_attribute);
        }
        if(bt_string != s->m_basetype){
            this->t_error(incompat_assign,  p->m_attribute);
        }
    }

    void check_array_access(ArrayAccess* p)
    {
        if(!m_st->lookup(p->m_symname->spelling())){
            this->t_error(var_undef,  p->m_attribute);
        }
        if(p->m_expr->m_attribute.m_basetype != bt_integer){
            this->t_error(array_index_error,  p->m_attribute);
        }
        if(m_st->lookup(p->m_symname->spelling())->m_basetype != bt_string){
        this->t_error(no_array_var,  p->m_attribute);

        }
    }

    void check_array_element(ArrayElement* p)
    {
        if(!m_st->lookup(p->m_symname->spelling())){
            this->t_error(var_undef,  p->m_attribute);
        }
        if(p->m_expr->m_attribute.m_basetype != bt_integer){
            this->t_error(array_index_error,  p->m_attribute);
        }
        if(m_st->lookup(p->m_symname->spelling())->m_basetype != bt_string){
        this->t_error(no_array_var,  p->m_attribute);
        }
    }

    // For checking boolean operations(and, or ...)
    void checkset_boolexpr(Expr* parent, Expr* child1, Expr* child2)
    {   
        if (parent->m_attribute.m_basetype != bt_boolean || 
            child1->m_attribute.m_basetype != bt_boolean ||
            child2->m_attribute.m_basetype != bt_boolean){
            this->t_error(expr_type_err,  parent->m_attribute);
        }
    }

    // For checking arithmetic expressions(plus, times, ...)
    void checkset_arithexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        //std::cout << "arithexpr" << std::endl;
        //std::cout << parent->m_attribute.m_basetype << std::endl;
        //std::cout << child1->m_attribute.m_basetype << std::endl;
        //std::cout << child2->m_attribute.m_basetype << std::endl;
        if (parent->m_attribute.m_basetype  != bt_integer || 
            child1->m_attribute.m_basetype != bt_integer ||
            child2->m_attribute.m_basetype != bt_integer){
            if(child1->m_attribute.m_basetype == bt_charptr ||
               child1->m_attribute.m_basetype == bt_intptr)
            {
                this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);
            }
            this->t_error(expr_type_err,  parent->m_attribute);
        }
    }

    // Called by plus and minus: in these cases we allow pointer arithmetics
    void checkset_arithexpr_or_pointer(Expr* parent, Expr* child1, Expr* child2)
    {
        //std::cout << "arithexpr_or_pointer" << std::endl;
        //std::cout << parent->m_parent_attribute->m_basetype << std::endl;
        //std::cout << child1->m_attribute.m_basetype << std::endl;
        //std::cout << child2->m_attribute.m_basetype << std::endl;
        switch(parent->m_parent_attribute->m_basetype){
            case(bt_charptr):
            {
                if(!(child1->m_attribute.m_basetype == bt_charptr &&
                   child2->m_attribute.m_basetype == bt_integer))
                {
                    this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_integer):
            {
                if(!(child1->m_attribute.m_basetype == bt_integer &&
                   child2->m_attribute.m_basetype == bt_integer))
                {
                    this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);
                }
                break;
            }
            default:
                this->t_error(expr_pointer_arithmetic_err,  parent->m_attribute);
        }
    }

    // For checking relational(less than , greater than, ...)
    void checkset_relationalexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        //std::cout << parent->m_parent_attribute->m_basetype << std::endl;
        //std::cout << child1->m_attribute.m_basetype << std::endl;
        //std::cout << child2->m_attribute.m_basetype << std::endl;
        if (parent->m_parent_attribute->m_basetype != bt_boolean || 
            child1->m_attribute.m_basetype != bt_integer ||
            child2->m_attribute.m_basetype != bt_integer){
            this->t_error(expr_type_err, parent->m_attribute);
        }
    }

    // For checking equality ops(equal, not equal)
    void checkset_equalityexpr(Expr* parent, Expr* child1, Expr* child2)
    {
        if (parent->m_parent_attribute->m_basetype != bt_boolean){
            this->t_error(expr_type_err,  parent->m_attribute);
        }
        //std::cout << child1->m_attribute.m_basetype << std::endl;
        //std::cout << child2->m_attribute.m_basetype << std::endl;
        switch(child1->m_attribute.m_basetype){
            case(bt_charptr):
            {   
                if(child2->m_attribute.m_basetype == bt_charptr)
                {}
                else if(child2->m_attribute.m_basetype == bt_ptr)
                {}
                else
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_boolean):
            {
                //std::cout << child1->m_attribute.m_basetype << std::endl;
                //std::cout << child2->m_attribute.m_basetype << std::endl;
                if(child2->m_attribute.m_basetype != bt_boolean)
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_integer):
            {
                if(child2->m_attribute.m_basetype != bt_integer)
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_intptr):
            {
                if(child2->m_attribute.m_basetype == bt_intptr)
                {}
                else if(child2->m_attribute.m_basetype == bt_ptr)
                {}
                else
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_char):
            {
                if(child2->m_attribute.m_basetype != bt_char)
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            case(bt_ptr):
            {
                if(child2->m_attribute.m_basetype != bt_ptr)
                {
                    this->t_error(expr_type_err,  parent->m_attribute);
                }
                break;
            }
            default:
                this->t_error(expr_type_err,  parent->m_attribute);
        }
    }
    // For checking not
    void checkset_not(Expr* parent, Expr* child)
    {
        if(parent->m_attribute.m_basetype != bt_boolean)
        {
            this->t_error(expr_type_err,  parent->m_attribute);
        }
        if(child->m_attribute.m_basetype != bt_boolean)
        {
            this->t_error(expr_type_err,  parent->m_attribute);
        }
    }

    // For checking unary minus
    void checkset_uminus(Expr* parent, Expr* child)
    {
        if(parent->m_attribute.m_basetype != bt_integer)
        {
            this->t_error(expr_type_err,  parent->m_attribute);
        }
        if(child->m_attribute.m_basetype != bt_integer)
        {
            this->t_error(expr_type_err,  parent->m_attribute);
        }
    }

    void checkset_absolute_value(Expr* parent, Expr* child)
    {
        //std::cout << parent->m_parent_attribute->m_basetype << std::endl;
        //std::cout << child->m_attribute.m_basetype << std::endl;
        if(parent->m_parent_attribute->m_basetype != bt_integer)
        {
            this->t_error(expr_abs_error,  parent->m_attribute);
        }
        if(!(child->m_attribute.m_basetype == bt_integer || 
           child->m_attribute.m_basetype == bt_string) )
        {
            this->t_error(expr_abs_error,  parent->m_attribute);
        }
    }

    void checkset_addressof(Expr* parent, Lhs* child)
    {
          //std::cout << parent->m_parent_attribute->m_basetype << std::endl;
          //std:: cout << child->m_attribute.m_basetype << std::endl;
          
          if(parent->m_parent_attribute->m_basetype == bt_charptr)
          {
            if(child->m_attribute.m_basetype == bt_char)
            {}
            else
            {
                this->t_error(expr_addressof_error, parent->m_attribute);
            }
          }
          else if(parent->m_parent_attribute->m_basetype == bt_intptr)
          {
            if(child->m_attribute.m_basetype == bt_integer)
            {}
            else
            {
                this->t_error(expr_addressof_error, parent->m_attribute);
            }
          }
          else
            this->t_error(expr_addressof_error, parent->m_attribute);
    }

    void checkset_deref_expr(Deref* parent,Expr* child)
    {
        //std::cout << "checkset_deref_expr" << std::endl;
        //std::cout << parent->m_parent_attribute->m_basetype << std::endl;
        //std::cout << child->m_attribute.m_basetype << std::endl;
        if(parent->m_parent_attribute->m_basetype == bt_char)
          {
            if(child->m_attribute.m_basetype == bt_charptr)
            {
                parent->m_attribute.m_basetype = bt_char;
            }
            else
            {
                this->t_error(invalid_deref, parent->m_attribute);
            }
          }
          else if(parent->m_parent_attribute->m_basetype == bt_integer)
          {
            if(child->m_attribute.m_basetype == bt_intptr)
            {
                parent->m_attribute.m_basetype = bt_integer;

            }
            else
            {
                this->t_error(invalid_deref, parent->m_attribute);
            }
          }
          else
            this->t_error(invalid_deref, parent->m_attribute);
    }

    // Check that if the right-hand side is an lhs, such as in case of
    // addressof
    void checkset_deref_lhs(DerefVariable* p)
    {
        Symbol *s2;
        s2 = m_st->lookup(p->m_symname->spelling());
        if(!s2){
            this->t_error(var_undef,  p->m_attribute);
        }
        if(!(s2->m_basetype == bt_charptr ||
           s2->m_basetype == bt_intptr))
        {
            this->t_error(invalid_deref, p->m_attribute);
        }
    }

    void checkset_variable(Variable* p)
    {
        Symbol *s2;
        s2 = m_st->lookup(p->m_symname->spelling());
        if(!s2){
            this->t_error(var_undef,  p->m_attribute);
        }
    }


  public:

    Typecheck(FILE* errorfile, SymTab* st) {
        m_errorfile = errorfile;
        m_st = st;
        flag = false;
    }

    void visitProgramImpl(ProgramImpl* p)
    {
        //m_st->open_scope();

        default_rule(p);

        check_for_one_main(p); //checks for one main
        //m_st->close_scope();
        //m_st->dump(stdout);
    }

    void visitProcImpl(ProcImpl* p)
    {
        add_proc_symbol(p);
        m_st->open_scope();
        default_rule(p);
         //checks for duplicates
        check_proc(p); //checks return value
    }

    void visitCall(Call* p)
    {
        default_rule(p);
        check_call(p);
    }

    void visitNested_blockImpl(Nested_blockImpl* p)
    {
        m_st->open_scope();
        default_rule(p);
        m_st->close_scope();
    }

    void visitProcedure_blockImpl(Procedure_blockImpl* p)
    {

        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        m_st->close_scope();
    }

    void visitDeclImpl(DeclImpl* p)
    {
        default_rule(p);
        add_decl_symbol(p);

    }

    void visitAssignment(Assignment* p)
    {
        default_rule(p);
        check_assignment(p);
    }

    void visitStringAssignment(StringAssignment *p)
    {
        default_rule(p);
        check_string_assignment(p);
    }

    void visitIdent(Ident* p)
    {
        default_rule(p);
        const char* name = expr_to_id(p);
        
        if(!m_st->lookup(name)){
            this->t_error(var_undef,  p->m_attribute);
        }
        p->m_attribute.m_basetype = m_st->lookup(name)->m_basetype;
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        //std::cout << p->m_parent_attribute->m_basetype << std::endl;
    }

    void visitReturn(Return* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        check_return(p); // check basetype to not be string
    }

    void visitIfNoElse(IfNoElse* p)
    {
        default_rule(p);
        check_pred_if(p->m_expr);
    }

    void visitIfWithElse(IfWithElse* p)
    {
        default_rule(p);
        check_pred_if(p->m_expr);

    }

    void visitWhileLoop(WhileLoop* p)
    {
        default_rule(p);
        check_pred_while(p->m_expr);
    }

    void visitCodeBlock(CodeBlock *p) 
    {
        default_rule(p);
    }

    void visitTInteger(TInteger* p)
    {
        p->m_attribute.m_basetype = bt_integer;
        //p->m_parent_attribute->m_basetype = bt_integer;
    }

    void visitTBoolean(TBoolean* p)
    {
        p->m_attribute.m_basetype = bt_boolean;

    }

    void visitTCharacter(TCharacter* p)
    {
        p->m_attribute.m_basetype = bt_char;
    }

    void visitTString(TString* p)
    {
        p->m_attribute.m_basetype = bt_string;

    }

    void visitTCharPtr(TCharPtr* p)
    {
        p->m_attribute.m_basetype = bt_charptr;
    }

    void visitTIntPtr(TIntPtr* p)
    {
        p->m_attribute.m_basetype = bt_intptr;
    }

    void visitAnd(And* p)
    {
        default_rule(p);
        checkset_boolexpr(p, p->m_expr_1, p->m_expr_2);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;

    }

    void visitDiv(Div* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        checkset_arithexpr(p,p->m_expr_1,p->m_expr_2);

    }

    void visitCompare(Compare* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }
        p->m_attribute.m_basetype = bt_boolean;   
        checkset_equalityexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitGt(Gt* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }   
        checkset_relationalexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitGteq(Gteq* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }   
        checkset_relationalexpr(p,p->m_expr_1,p->m_expr_2);    
    }

    void visitLt(Lt* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }   
        checkset_relationalexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitLteq(Lteq* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }   
        checkset_relationalexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitMinus(Minus* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }   
        checkset_arithexpr_or_pointer(p,p->m_expr_1, p->m_expr_2);

    }

    void visitNoteq(Noteq* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_boolean;
        }   
        checkset_equalityexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitOr(Or* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        checkset_boolexpr(p, p->m_expr_1, p->m_expr_2);
    }

    void visitPlus(Plus* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            
            //std::cout << "visitplus" << std::endl;
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }

        //std::cout << p->m_attribute.m_basetype << std::endl;
        checkset_arithexpr_or_pointer(p,p->m_expr_1, p->m_expr_2);
    }

    void visitTimes(Times* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }
        checkset_arithexpr(p,p->m_expr_1,p->m_expr_2);
    }

    void visitNot(Not* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        checkset_not(p,p->m_expr);
    }

    void visitUminus(Uminus* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        checkset_uminus(p, p->m_expr);

    }

    void visitArrayAccess(ArrayAccess* p)
    {
        default_rule(p);
        p->m_attribute.m_basetype = bt_char;
        if(p->m_parent_attribute->m_basetype == bt_undef){
            //std::cout << "visitarrayaccess" << std::endl;           
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }

        check_array_access(p);
    }

    void visitIntLit(IntLit* p)
    {
        default_rule(p);
        //std::cout << p->m_parent_attribute->m_basetype << std::endl;
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = bt_integer;
        }
        p->m_attribute.m_basetype = bt_integer;

    }

    void visitCharLit(CharLit* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = bt_char;
        p->m_attribute.m_basetype = bt_char;

    }

    void visitBoolLit(BoolLit* p)
    {
        default_rule(p);
        p->m_parent_attribute->m_basetype = bt_boolean;
        p->m_attribute.m_basetype = bt_boolean;


    }

    void visitNullLit(NullLit* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype != bt_undef){
            p->m_parent_attribute->m_basetype = bt_ptr;
        }
        p->m_attribute.m_basetype = bt_ptr;
    }

    void visitAbsoluteValue(AbsoluteValue* p)
    {
        default_rule(p);
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }
        checkset_absolute_value(p,p->m_expr);
    }

    void visitAddressOf(AddressOf* p)
    {
        default_rule(p);
        if(p->m_attribute.m_basetype == bt_char){
            p->m_attribute.m_basetype = bt_charptr;
        }
        if(p->m_attribute.m_basetype == bt_integer){
            p->m_attribute.m_basetype = bt_intptr;
        }
        if(p->m_parent_attribute->m_basetype == bt_undef){
            //std::cout << p->m_attribute.m_basetype << std::endl;
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }
        checkset_addressof(p, p->m_lhs);
    }

    void visitVariable(Variable* p)
    {
        default_rule(p);
        checkset_variable(p);
        const char* name = lhs_to_id(p);
        p->m_attribute.m_basetype = m_st->lookup(name)->m_basetype;
        p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        //std::cout << p->m_parent_attribute->m_basetype << std::endl;
    }

    void visitDeref(Deref* p)
    {
        default_rule(p);
        checkset_deref_expr(p, p->m_expr);
    }

    void visitDerefVariable(DerefVariable* p)
    {
        default_rule(p);
        checkset_deref_lhs(p);
        p->m_attribute.m_basetype = m_st->lookup(p->m_symname->spelling())->m_basetype;
        //std::cout << "visitDerefVariable" << std::endl;
        //std::cout << p->m_attribute.m_basetype << std::endl;
        if(p->m_attribute.m_basetype == bt_charptr){
            p->m_attribute.m_basetype = bt_char;
        }
        if(p->m_attribute.m_basetype == bt_integer){
            p->m_attribute.m_basetype = bt_intptr;
        }
    }

    void visitArrayElement(ArrayElement* p)
    {
        default_rule(p);
        p->m_attribute.m_basetype = bt_char;
        if(p->m_parent_attribute->m_basetype == bt_undef){
            p->m_parent_attribute->m_basetype = p->m_attribute.m_basetype;
        }
        check_array_element(p);
    }

    // Special cases
    void visitPrimitive(Primitive* p) {

    }
    void visitSymName(SymName* p) {

    }
    void visitStringPrimitive(StringPrimitive* p) {}
};


void dopass_typecheck(Program_ptr ast, SymTab* st)
{
    Typecheck* typecheck = new Typecheck(stderr, st);
    ast->accept(typecheck); // Walk the tree with the visitor above
    delete typecheck;
}
