theory Syntax imports Main Oalist
begin

type_synonym name = String.literal

datatype expr1 =
  ELit int
  | EVar name

datatype expr =
  E1 "expr1 list"
  | EPrim name "expr1 list"
  | EFun name "expr1 list"

(* how to handle multiple returns?
 * expr1 vs expr? *)
datatype statement =
  SBlock "(name list)" "statement list"
  | SAssn "name list" expr
  | SIf expr1 statement statement
  | SWhile expr1 statement
  | SSkip

datatype fundec =
  Decl "name list" "name list" "statement"

type_synonym varmap =
  "(name, int) oalist list"

(* varmap argument can be useful for diagnostics *)
type_synonym 'g builtin =
  "'g \<Rightarrow> int list \<Rightarrow> varmap \<Rightarrow> ('g * int list) option"

type_synonym 'g fctx =
  "(name, fundec + 'g builtin) oalist"

datatype 'g program =
  Prog "'g fctx" "statement"

fun varmap_get :: "varmap \<Rightarrow> String.literal \<Rightarrow> int option" where
  "varmap_get [] s = None"
| "varmap_get (hl#t) s =
   (case get hl s of
    Some v \<Rightarrow> Some v
    | None \<Rightarrow> varmap_get t s)"

fun varmap_gets :: "varmap \<Rightarrow> String.literal list \<Rightarrow> int list option" where
  "varmap_gets vm [] = Some []"
| "varmap_gets vm (nh # nt) =
   (case varmap_get vm nh of
    None \<Rightarrow> None
    | Some vh \<Rightarrow>
      (case varmap_gets vm nt of
       None \<Rightarrow> None
       | Some vt \<Rightarrow> Some (vh#vt)))"

fun varmap_insert :: "varmap \<Rightarrow> String.literal \<Rightarrow> int \<Rightarrow> varmap" where
  "varmap_insert [] s i = []" (* bogus *)
| "varmap_insert (hl#t) s i =
   update s i hl # t"

fun varmap_inserts :: "varmap \<Rightarrow> (String.literal * int) list \<Rightarrow> varmap" where
"varmap_inserts vm [] = vm"
| "varmap_inserts vm ((n, v)#t) =
   varmap_inserts (varmap_insert vm n v) t"

fun varmap_update :: "varmap \<Rightarrow> String.literal \<Rightarrow> int \<Rightarrow> varmap" where
  "varmap_update [] s i = []" (* bogus *)
| "varmap_update (hl#t) s i =
   (case get hl s of
    Some _ \<Rightarrow> (update s i hl #t)
    | None \<Rightarrow> hl # varmap_update t s i)"

fun varmap_updates :: "varmap \<Rightarrow> (String.literal * int) list \<Rightarrow> varmap" where
"varmap_updates vm [] = vm"
| "varmap_updates vm ((n, v)#t) =
   varmap_updates (varmap_update vm n v) t"

fun varmap_push :: "varmap \<Rightarrow> varmap" where
"varmap_push x = (empty#x)"

fun varmap_pop :: "varmap \<Rightarrow> varmap" where
"varmap_pop [] = []"
| "varmap_pop (h#t) = t"

datatype 'x orerror =
  Ok 'x
  | Error String.literal

type_synonym 'g state =
  "(varmap * 'g) orerror"

(* extend a variable map with a context of new declarations *)
fun varmap_extend :: "varmap \<Rightarrow> name list \<Rightarrow> varmap" where
"varmap_extend vm [] = vm"
| "varmap_extend vm (nh#nt) =
   varmap_extend (varmap_insert vm nh 0) nt"


end