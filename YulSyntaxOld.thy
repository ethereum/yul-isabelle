theory YulSyntax imports Main

begin

(* https://solidity.readthedocs.io/en/v0.5.10/yul.html#specification-of-yul *)

(* "leave" ? *)

(* note that we are assuming numbers have been parsed *)
datatype bool_literal =
  BLit bool

datatype number_literal =
  NLit "int"

datatype string_literal =
  SLit "char list"

datatype literal =
  NL number_literal
| SL string_literal
| BL bool_literal
(* | hex_literal *)

datatype identifier = 
  Id "char list"

datatype identifier_list =
  Ids "identifier" "identifier list"

datatype unsigned_signed =
  Unsigned
| Signed

datatype int_size =
  i8 | i32 | i64 | i128 | i256

datatype builtin_type_name = 
  BBool
| BInt unsigned_signed int_size

datatype type_name =
  TI identifier
| TB builtin_type_name

datatype typed_identifier_list =
  TIds "(identifier * type_name)" "(identifier * type_name) list"

datatype break_continue =
  XBreak
  | XContinue

datatype 
expression =
  EF "function_call"
  | EI "identifier"
  | EL "literal"
and
function_call =
  Call identifier "expression list"

datatype variable_declaration =
  Var "typed_identifier_list" "expression option"

datatype assignment =
  Asgn "identifier_list" "expression"

datatype block =
  Block "statement list"
and
  statement =
  SB block
  | SF function_definition
  | SV variable_declaration
  | SA assignment
  | SI ifst
  | SE expression
  | SS switch
  | SL for_loop 
  | SX break_continue
and
function_sig =
  FSig "typed_identifier_list" "typed_identifier_list" "block"
and
function_definition =
  Fun "identifier" "function_sig"
and
ifst =
  Ifst "expression" "block"
and
switch =
  Switch "expression" "casest" "casest list" "default option"
| Switch0 expression default
and
casest =
  Case literal block
and
default =
  Default block
and
for_loop =
  For block expression block block


(* "restrictions on the grammar"
- switches need default (handled above)
- if all values are covered don't allow default (hard to do purely syntactically)
- every expression evals to 0 or more value (hard to do syntactically)
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
- literals cannot be larger than their type
  (i will do this later, requires type environments)
  *)

(* question: do we need to dig through expressions for function calls? *)

fun continue_break_check_s' :: "bool \<Rightarrow> statement \<Rightarrow> bool"
and
  continue_break_check_b' :: "bool \<Rightarrow> block \<Rightarrow> bool"
and
  continue_break_check_c' :: "bool \<Rightarrow> casest \<Rightarrow> bool" 
  where
  "continue_break_check_b' inLoop (Block sl) =
    List.list_all (continue_break_check_s' inLoop) sl"
| "continue_break_check_c' inLoop (Case _ b) = continue_break_check_b' inLoop b"
| "continue_break_check_s' inLoop (SB b) = continue_break_check_b' inLoop b"
| "continue_break_check_s' inLoop (SF (Fun _ (FSig _ _ b))) = continue_break_check_b' False b"
| "continue_break_check_s' inLoop (SI (Ifst _ b)) = continue_break_check_b' inLoop b"
| "continue_break_check_s' inLoop (SS (Switch _ c cs (Some (Default b)))) = 
     (continue_break_check_c' inLoop c \<and>
      List.list_all (continue_break_check_c' inLoop) cs \<and>
      continue_break_check_b' inLoop b)"
| "continue_break_check_s' inLoop (SS (Switch _ c cs None)) = 
     (continue_break_check_c' inLoop c \<and>
      List.list_all (continue_break_check_c' inLoop) cs)"
| "continue_break_check_s' inLoop (SS (Switch0 _ (Default b))) = 
     (continue_break_check_b' inLoop b)"
| "continue_break_check_s' inLoop (SL (For bi e b1 b2)) =
    (continue_break_check_b' inLoop bi \<and>
     continue_break_check_b' True b1 \<and>
     continue_break_check_b' True b2)"
| "continue_break_check_s' inLoop (SX _) = inLoop"
| "continue_break_check_s' inLoop (SE _) = True"
| "continue_break_check_s' inLoop (SV _) = True"
| "continue_break_check_s' inLoop (SA _) = True"

definition continue_break_check_s :: "statement \<Rightarrow> bool" where
"continue_break_check_s = continue_break_check_s' False"

fun loop_init_check_s' :: "bool \<Rightarrow> statement \<Rightarrow> bool"
and
  loop_init_check_b' :: "bool \<Rightarrow> block \<Rightarrow> bool"
and
  loop_init_check_c' :: "bool \<Rightarrow> casest \<Rightarrow> bool"
  where
  "loop_init_check_b' inInit (Block sl) =
    List.list_all (loop_init_check_s' inInit) sl"
| "loop_init_check_c' inInit (Case _ b) = loop_init_check_b' inInit b"
| "loop_init_check_s' inInit (SB b) = loop_init_check_b' inInit b"
| "loop_init_check_s' inInit (SF (Fun _ (FSig _ _ b))) =
    (if inInit then False
     else loop_init_check_b' inInit b)"
| "loop_init_check_s' inInit (SI (Ifst _ b)) = loop_init_check_b' inInit b"
| "loop_init_check_s' inInit (SS (Switch _ c cs (Some (Default b)))) = 
     (loop_init_check_c' inInit c \<and>
      List.list_all (loop_init_check_c' inInit) cs \<and>
      loop_init_check_b' inInit b)"
| "loop_init_check_s' inInit (SS (Switch _ c cs None)) = 
     (loop_init_check_c' inInit c \<and>
      List.list_all (loop_init_check_c' inInit) cs)"
| "loop_init_check_s' inInit (SS (Switch0 _ (Default b))) = 
     (loop_init_check_b' inInit b)"
| "loop_init_check_s' inInit (SL (For bi e b1 b2)) =
    (loop_init_check_b' True bi \<and>
     loop_init_check_b' inInit b1 \<and>
     loop_init_check_b' inInit b2)"
| "loop_init_check_s' inInit (SX _) = inInit"
| "loop_init_check_s' _ (SE _) = True"
| "loop_init_check_s' _ (SV _) = True"
| "loop_init_check_s' _ (SA _) = True"


end