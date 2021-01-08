theory YulSyntaxUtils imports Main YulSyntax

begin

(* https://solidity.readthedocs.io/en/v0.5.10/yul.html#specification-of-yul *)

(* one possible way to specify Yul literals *)
(* note that we are assuming numbers have been parsed *)
datatype bool_literal =
  BLit "bool"

datatype number_literal =
  NLit "int"

datatype string_literal =
  SLit "char list"

datatype literal =
  NL number_literal
| SL string_literal
| BL bool_literal
(* | hex_literal *)

(* "restrictions on the grammar"
- switches need default 
- if all values are covered don't allow default for switch (hard to do purely syntactically)
- every expression evals to 0 or more values (hard to do syntactically)
- in variable declarations/assignments expressions must evaluate to the correct # of values
  - otherwise expressions cannot evaluate to multiple value
  - this is hard to handle syntactically
- expressions that are also statements must evaluate to 0 values (hard to do syntactically)
- continue and break can only be used inside loop bodies
  - need to be in same function as loop
  - see continue_break_check below *
- loop conditions must evaluate to exactly 1 value (hard to do syntactically)
- functions cannot be defined inside for loop init blocks
  - see loop_init_check below *
- "leave" statements need to be inside a function
- literals cannot be larger than their type
  (i will do this later, requires type environments - this can wait until better treatment of literals)
  *)

(* question: do we need to dig through expressions for function calls? *)
(* question: interpretation of
The continue and break statements cannot be used in other parts of a loop, not even when it is scoped inside a second loop’s body.
*)


(* Syntactic check to ensure that continue and break statements don't occur
   outside loop bodies *)
fun continue_break_check' :: "bool \<Rightarrow> YulStatement \<Rightarrow> bool" and
    continue_break_check_case' :: "bool \<Rightarrow> YulSwitchCase \<Rightarrow> bool" where
  "continue_break_check' inLoop (YulBlock sl) =
    List.list_all (continue_break_check' inLoop) sl"
| "continue_break_check' inLoop (YulIf _ sl) =
    List.list_all (continue_break_check' inLoop) sl"
| "continue_break_check' inLoop
    (YulForLoop pre _ post body) =
    (List.list_all (continue_break_check' False) pre \<and>
     List.list_all (continue_break_check' False) post \<and>
     List.list_all (continue_break_check' True) body)"
| "continue_break_check' inLoop (YulSwitch _ sc) =
    List.list_all (continue_break_check_case' inLoop) sc"
| "continue_break_check' inLoop
  (YulFunctionDefinitionStatement 
    (YulFunctionDefinition _ _ _ sl)) =
    List.list_all (continue_break_check' False) sl"

| "continue_break_check_case' inLoop (YulSwitchCase _ sl) =
    List.list_all (continue_break_check' inLoop) sl"

| "continue_break_check' inLoop YulBreak = inLoop"
| "continue_break_check' inLoop YulContinue = inLoop"
| "continue_break_check' inLoop _ = True"


definition continue_break_check :: "YulStatement \<Rightarrow> bool" where
"continue_break_check = continue_break_check' False"

(* Syntactic check to ensure functions are not defined inside
   for loop init blocks *)
fun loop_init_check' :: "bool \<Rightarrow> YulStatement \<Rightarrow> bool"
and
  loop_init_check_case' :: "bool \<Rightarrow> YulSwitchCase \<Rightarrow> bool"
  where
  "loop_init_check' inInit (YulBlock sl) =
    List.list_all (loop_init_check' inInit) sl"
| "loop_init_check' inInit (YulIf _ sl) = 
   List.list_all (loop_init_check' inInit) sl"
| "loop_init_check' inInit (YulForLoop pre _ post body) = 
   (List.list_all (loop_init_check' True) pre \<and>
    List.list_all (loop_init_check' inInit) post \<and>
    List.list_all (loop_init_check' inInit) body)"
| "loop_init_check' inInit (YulSwitch _ sc) =
    List.list_all (loop_init_check_case' inInit) sc"
| "loop_init_check' inInit
   (YulFunctionDefinitionStatement 
    (YulFunctionDefinition _ _ _ sl)) =
    (if inInit then False
     else List.list_all (loop_init_check' False) sl)"

| "loop_init_check_case' inInit (YulSwitchCase _ sl) =
    List.list_all (loop_init_check' inInit) sl"

| "loop_init_check' inInit _ = True"

definition loop_init_check :: "YulStatement \<Rightarrow> bool" where
"loop_init_check = loop_init_check' False"


end