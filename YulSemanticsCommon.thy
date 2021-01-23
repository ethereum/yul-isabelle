theory YulSemanticsCommon imports YulSyntax
begin

(* Primitives common to both small and big step Yul semantics *)
datatype mode =
  Regular
  | Break
  | Continue
  | Leave

(* allow direct access to locals? *)
datatype ('g, 'v, 't) YulFunctionBody =
  YulBuiltin "'g \<Rightarrow> 'v list \<Rightarrow> (('g * 'v list) + String.literal)"
  | YulFunction "('v, 't) YulStatement list"

datatype ('g, 'v, 't) function_sig =
  YulFunctionSig
  (YulFunctionSigArguments: "'t YulTypedName list")
  (YulFunctionSigReturnValues: "'t YulTypedName list")
  (YulFunctionSigBody: "('g, 'v, 't) YulFunctionBody")

type_synonym 'v locals = "YulIdentifier \<Rightarrow> 'v option"

definition locals_empty :: "'v locals" where
"locals_empty = (\<lambda> _ . None)"

(* restrict e1 to the identifiers of e2 *)
definition restrict :: "'v locals \<Rightarrow> 'v locals \<Rightarrow> 'v locals" where
"restrict e1 e2 i =
  (if e2 i = None then None
      else e1 i)"

fun strip_id_type :: "'t YulTypedName \<Rightarrow> YulIdentifier" where
"strip_id_type (YulTypedName name type) = name"

fun strip_id_types :: "'t YulTypedName list \<Rightarrow> YulIdentifier list" where
"strip_id_types l =
  List.map strip_id_type l"

fun put_value :: "'v locals \<Rightarrow> YulIdentifier \<Rightarrow> 'v \<Rightarrow> 'v locals" where
"put_value L i v =
  (\<lambda> i' . if i' = i then Some v else L i')"

fun put_values :: "'v locals \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list \<Rightarrow> 'v locals option" where
"put_values L [] [] = Some L"
| "put_values L (ih#it) (vh#vt) =
   (case put_values L it vt of
    None \<Rightarrow> None
    | Some L' \<Rightarrow> Some (put_value L' ih vh))"
| "put_values L _ _ = None"

fun get_values :: "'v locals \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list option" where
"get_values L ids =
   List.those (List.map L (ids))"

fun make_locals :: "(YulIdentifier * 'v) list \<Rightarrow> 'v locals" where
"make_locals [] = locals_empty"
| "make_locals ((ih, vh)#t) =
    put_value (make_locals t) ih vh"

syntax plus_literal_inst.plus_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
  ("_ @@ _")

(* store results of yul statements *)
record ('g, 'v, 't) result =
  global :: "'g"
  locals :: "'v locals list"
  (* value stack, used within expression evaluation, as well as
     for assignments and function arguments *)
  stack :: "'v list"  
  funs :: "('g, 'v, 't) function_sig locals list"
  (* TODO: this was a mode option *)
  (*mode :: "mode"*)

datatype ('g, 'v, 't, 'z) YulResult =
  YulResult "('g, 'v, 't, 'z) result_scheme"
  (* errors can optionally carry failed state *)
  | ErrorResult "String.literal" "('g, 'v, 't, 'z) result_scheme option"

fun gatherYulFunctions :: "('v, 't) YulStatement list \<Rightarrow> 
                           ('g, 'v, 't, 'z) YulResult \<Rightarrow>
                           ('g, 'v, 't, 'z) YulResult" where
"gatherYulFunctions [] yr = yr"
| "gatherYulFunctions 
    ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t)
     (YulResult r) =
     (case funs r of
      [] \<Rightarrow> ErrorResult (STR ''empty function context'') (Some r)
      | F#Ft \<Rightarrow>
       gatherYulFunctions t
        (YulResult (r \<lparr> funs := (put_value F name 
                                          (YulFunctionSig args rets (YulFunction body)) # Ft) \<rparr>)))"
| "gatherYulFunctions (_#t) r =
    gatherYulFunctions t r"

(* "locale parameters" passed to Yul semantics
   (capture behaviors needed by certain control primitives) *)
record ('g, 'v, 't) YulDialect =
  is_truthy :: "'v \<Rightarrow> bool"
  init_state :: "'g"
  default_val :: "'v"
  builtins :: "('g, 'v, 't) function_sig locals"

end