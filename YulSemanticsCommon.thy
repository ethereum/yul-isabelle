theory YulSemanticsCommon imports YulSyntax
begin

(* Primitives common to both small and big step Yul semantics *)
datatype mode =
  Regular
  | Break
  | Continue
  | Leave

datatype function_sig =
  YulFunctionSig
  (YulFunctionSigArguments: "YulTypedName list")
  (YulFunctionSigReturnValues: "YulTypedName list")
  (YulFunctionSigBody: "YulStatement list")

type_synonym 'v locals = "YulIdentifier \<Rightarrow> 'v option"

definition locals_empty :: "'v locals" where
"locals_empty = (\<lambda> _ . None)"

(* restrict e1 to the identifiers of e2 *)
definition restrict :: "'v locals \<Rightarrow> 'v locals \<Rightarrow> 'v locals" where
"restrict e1 e2 i =
  (if e2 i = None then None
      else e1 i)"

fun strip_id_type :: "YulTypedName \<Rightarrow> YulIdentifier" where
"strip_id_type (YulTypedName name type) = name"

fun strip_id_types :: "YulTypedName list \<Rightarrow> YulIdentifier list" where
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

syntax plus_literal_inst.plus_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
  ("_ @@ _")

record ('g, 'v) result =
  global :: "'g"
  locals :: "'v locals list"
  funs :: "function_sig locals list"
  mode :: "mode option"
  vals :: "'v list option"

datatype ('g, 'v) YulResult =
  YulResult "('g, 'v) result"
  | ErrorResult "String.literal"

fun gatherYulFunctions :: "YulStatement list \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult" where
"gatherYulFunctions [] yr = yr"
| "gatherYulFunctions 
    ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t)
     (YulResult r) =
     (case funs r of
      [] \<Rightarrow> ErrorResult (STR ''empty function context'')
      | F#Ft \<Rightarrow>
       gatherYulFunctions t
        (YulResult (r \<lparr> funs := (put_value F name (YulFunctionSig args rets body) # Ft) \<rparr>)))"
| "gatherYulFunctions (_#t) r =
    gatherYulFunctions t r"


end