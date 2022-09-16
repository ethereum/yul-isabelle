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

(* enforce distinctness on name lists here? *)
datatype statement =
  SBlock "(name list)" "statement list"
  | SAssn "name list" expr
  | SIf expr1 statement statement
  | SWhile expr1 statement
  | SSkip


lemma statement_induct_strong :
  fixes P1 :: "statement \<Rightarrow> bool"
  fixes P2 :: "statement list \<Rightarrow> bool"

  assumes LB : "\<And> x1 x2 .
    P2 x2 \<Longrightarrow> P1 (SBlock x1 x2)"
  assumes LA : "\<And> x1 x2 . P1 (SAssn x1 x2)"
  assumes LI : "\<And> x1 x2 x3 .
    P1 x2 \<Longrightarrow> P1 x3 \<Longrightarrow> P1 (SIf x1 x2 x3)"
  assumes LW : "\<And> x1 x2 .
    P1 x2 \<Longrightarrow> P1 (SWhile x1 x2)"
  assumes LS : "P1 SSkip"

  assumes LNil : "P2 []"
  assumes LCons : "\<And> h t .
    P1 h \<Longrightarrow> P2 t \<Longrightarrow> P2 (h#t)"

  shows "P1 stm \<and> P2 stms"
  using assms
proof-
  {
    fix stm
    have "P1 stm \<and> (\<forall> x1 x2 . stm = SBlock x1 x2 \<longrightarrow> P2 x2)"
    proof(induction stm)
      case (SBlock x1 x2)
      then show ?case using LB LA LI LW LS LNil LCons
      proof(induction x2)
        case Nil
        then show ?case 
          by(auto)
      next
        case (Cons h t)

        then show ?case 
          by(auto intro: LB LA LI LW LS LNil LCons)
      qed
    next
      case (SAssn x1 x2)
      then show ?case using LA
        by auto
    next
      case (SIf x1 stm1 stm2)
      then show ?case 
        using LI
        by(auto)
    next
      case (SWhile x1 stm)
      then show ?case 
        using LW
        by(auto)
    next
      case SSkip
      then show ?case 
        using LS
        by(auto)
    qed
  } 
  then show ?thesis
    by auto
qed

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