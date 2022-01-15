theory Renamer
  imports "../Yul/YulSyntax" "../Yul/YulSemanticsSingleStep" 

begin

definition digit_to_nat :: "char \<Rightarrow> nat option"
  where
"digit_to_nat c = 
  (case c of
    (CHR ''0'') \<Rightarrow> Some 0
    | (CHR ''1'') \<Rightarrow> Some 1
    | (CHR ''2'') \<Rightarrow> Some 2
    | (CHR ''3'') \<Rightarrow> Some 3
    | (CHR ''4'') \<Rightarrow> Some 4
    | (CHR ''5'') \<Rightarrow> Some 5
    | (CHR ''6'') \<Rightarrow> Some 6
    | (CHR ''7'') \<Rightarrow> Some 7
    | (CHR ''8'') \<Rightarrow> Some 8
    | (CHR ''9'') \<Rightarrow> Some 9
    | _ \<Rightarrow> None
    )"

definition nat_to_digit :: "nat \<Rightarrow> char option" where
"nat_to_digit n =
  (case n of
    0 \<Rightarrow> Some (CHR ''0'')
    | Suc 0 \<Rightarrow> Some (CHR ''1'')
    | Suc (Suc 0) \<Rightarrow> Some (CHR ''2'')
    | Suc (Suc (Suc 0)) \<Rightarrow> Some (CHR ''3'')
    | Suc (Suc (Suc (Suc 0))) \<Rightarrow> Some (CHR ''4'')
    | Suc (Suc (Suc (Suc (Suc 0)))) \<Rightarrow> Some (CHR ''5'')
    | Suc (Suc (Suc (Suc (Suc (Suc 0))))) \<Rightarrow> Some (CHR ''6'')
    | Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<Rightarrow> Some (CHR ''7'')
    | Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<Rightarrow> Some (CHR ''8'')
    | Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) \<Rightarrow> Some (CHR ''9'')
    | _ \<Rightarrow> None)"

lemma nat_to_digit_to_nat :
  "nat_to_digit n = Some d \<Longrightarrow> digit_to_nat d = Some n"
  by(auto simp add: nat_to_digit_def digit_to_nat_def
      split: nat.splits)

lemma digit_to_nat_to_digit :
  "digit_to_nat d = Some n \<Longrightarrow> nat_to_digit n = Some d"
  by(auto simp add: nat_to_digit_def digit_to_nat_def
      split: char.splits bool.splits)

fun digits_to_nat' :: "char list \<Rightarrow> nat option" where
"digits_to_nat' [] = None"
| "digits_to_nat' [h] = digit_to_nat h"
| "digits_to_nat' (h#t) =
   (case digit_to_nat h of
    None \<Rightarrow> None
    | Some nh \<Rightarrow>
      (case digits_to_nat' t of
        None \<Rightarrow> None
        | Some nt \<Rightarrow>
          Some (10 * nt + nh)))"

definition digits_to_nat :: "char list \<Rightarrow> nat option" where
"digits_to_nat l = digits_to_nat' (rev l)"

fun nat_to_digits' :: "nat \<Rightarrow> char list option" where
"nat_to_digits' n =
  (case nat_to_digit (n mod 10) of
    None \<Rightarrow> None
    | Some d \<Rightarrow>
      (if n div 10 = 0
       then Some [d]
       else (case (nat_to_digits' (n div 10)) of
          None \<Rightarrow> None
          | Some r \<Rightarrow> Some (d # r))))"

definition nat_to_digits :: "nat \<Rightarrow> char list option" where
"nat_to_digits n =
  (case nat_to_digits' n of
    None \<Rightarrow> None
    | Some r \<Rightarrow> Some (rev r))"

(* possible idea: use strong induction to show nat_to_digit can never be None
   (or just change the definition so that it won't be None ever )
*)
lemma nat_to_digits_to_nat' :
  shows "nat_to_digits' n = Some dl \<Longrightarrow> digits_to_nat' dl = Some n"
proof(induction arbitrary: dl rule: full_nat_induct)
  case (1 n)
  have Leq : "n mod 10 < 10"
    by arith

(* I'm hoping this will speed things up a bit. *)
  obtain m where M: "m = n mod 10"
    by(auto)

  show ?case 
  proof(cases dl)
    case Nil

    show ?thesis
    proof(cases "nat_to_digit (n mod 10)")
      case None

    have False using Leq None
      unfolding sym[OF M]
      by(auto simp add: nat_to_digits_def nat_to_digit_def split: nat.splits; arith)

    then show ?thesis by auto
    next
      case (Some d)
      then show ?thesis using Nil "1.prems"
        by(simp add: nat_to_digits_def split: if_splits option.splits)
    qed
  next
    case (Cons dh dt)
    show ?thesis
    proof(cases "nat_to_digit (n mod 10)")
      case None
  
      have False using Leq None
        unfolding sym[OF M]
        by(auto simp add: nat_to_digits_def nat_to_digit_def split: nat.splits; arith)
    
      then show ?thesis by auto
    next
      case (Some d)
      show ?thesis 
      proof(cases "n div 10 = 0")
        case N0 : True

        then show ?thesis using Cons "1.prems" Some
          by(simp add: nat_to_digits_def nat_to_digit_to_nat)
      next
        case Nnon0 : False
        have IH' : "\<And> m. Suc m \<le> n \<Longrightarrow>
            (\<And> x. nat_to_digits' m = Some x \<Longrightarrow> digits_to_nat' x = Some m)"
          using "1.IH"
          by auto

        have I1 : "Suc (n div 10) \<le> n"
          using Nnon0
          by(arith)

        show ?thesis
        proof(cases dt)
          case Nil' : Nil
          then show ?thesis 
            using Cons "1.prems" Some Nnon0 
            by(auto split: if_splits option.splits)
        next
          case Cons' : (Cons dh' dt')

          have I2 : "nat_to_digits' (n div 10) = Some (dt)"
            using Cons Cons' "1.prems" Some Nnon0
            by(simp;
               cases "nat_to_digit (n div 10 mod 10)"; auto simp del: nat_to_digits'.simps;
               cases "nat_to_digits' (n div 10 div 10)"; auto simp del: nat_to_digits'.simps)

          have Dh_eq : "d = dh"
            using Cons Cons' "1.prems" Some Nnon0
            by(simp; auto split: option.splits simp del: nat_to_digits'.simps)

          have Dh : "digit_to_nat dh = Some (n mod 10)"
            using Cons Cons' "1.prems" Some Nnon0 IH'[OF I1 I2] Dh_eq
            by(simp  add: nat_to_digit_to_nat)

          show ?thesis using Cons Cons' "1.prems" Some Nnon0 IH'[OF I1 I2] Dh_eq Dh
            by(simp )
        qed
      qed
    qed
  qed
qed

lemma nat_to_digits_to_nat :
  assumes H : "nat_to_digits n = Some dl"
  shows "digits_to_nat dl = Some n"
proof-

  obtain r  where R: "nat_to_digits' n = Some r" "dl = rev r" using H
    by(auto simp add: nat_to_digits_def digits_to_nat_def simp del: nat_to_digits'.simps split: option.splits)

  show ?thesis using H nat_to_digits_to_nat'[OF R(1)] R
    by(auto simp add: nat_to_digits_def digits_to_nat_def simp del: nat_to_digits'.simps)
qed

fun digits_canonical :: "char list \<Rightarrow> bool"
  where
"digits_canonical [] = True" 
| "digits_canonical [x] = True"
| "digits_canonical (h#t) =
    (h \<noteq> CHR ''0'' \<and> digits_canonical t)"

lemma digits_canonical_prefix :
  assumes "digits_canonical (l1 @ l2)"
  shows "digits_canonical l1" using assms
proof(induction l1)
  case Nil
  then show ?case by auto
next
  case (Cons h1 t1)
  show ?case 
  proof(cases t1)
    case Nil' : Nil
    then show ?thesis using Cons
      by(auto)
  next
    case Cons' : (Cons h2 t2)
    then show ?thesis using Cons
      by(auto)
  qed
qed

(*
lemma digits_to_nat_to_digits'_0 :
  shows "digits_to_nat' [CHR''0''] = Some n \<Longrightarrow> nat_to_digits' n = Some [CHR''0'']"
*)

lemma digit_to_nat_lt_10 :
  assumes H: "digit_to_nat d = Some n"
  shows "n < 10"
  using H
  by(auto simp add: digit_to_nat_def split: char.splits bool.splits)

lemma digits_to_nat_to_digits' :
  assumes H0 : "digits_canonical (rev dl)"
  assumes H: "digits_to_nat' dl = Some n"
  shows "nat_to_digits' n = Some dl"
  using assms
proof(induction dl arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons dh dt)

  have I1 : "digits_canonical (rev dt)"
    using Cons.prems(1) digits_canonical_prefix[of "rev dt" "[dh]"]
    by auto

  show ?case 
  proof(cases dt)
    case Nil' : Nil

    then have "n < 10"
      using digit_to_nat_lt_10
      using Cons
      by(auto)

    then have "n mod 10 = n"
      by auto

    then show ?thesis
      using Cons Nil' digit_to_nat_to_digit[of dh]
      by(auto)
  next
    case Cons' : (Cons dh' dt')

    then obtain n1 where N1: "digit_to_nat dh = Some n1"
      using Cons.prems
      by(cases "digit_to_nat dh"; auto)

    then have N1_lt_10 : "n1 < 10"
      using digit_to_nat_lt_10
      using Cons
      by(auto)

    then have N1_mod : "n1 mod 10 = n1"
      by auto

    obtain rest where Rest : "digits_to_nat' (dh' # dt') = Some rest"
      using Cons.prems N1 Cons'
      by(cases "digits_to_nat' (dh' # dt')"; auto)

    then have Rest' : "digits_to_nat' dt = Some rest"
      using Cons'
      by auto

    have Roundtrip1 : "nat_to_digit n1 = Some dh"
      using digit_to_nat_to_digit[OF N1]
      by auto

    have Rest_nz : "rest  \<noteq> 0"
      using Cons.prems Cons.IH[OF I1 Rest'] N1 Cons' Rest N1_mod Roundtrip1
      by(cases "nat_to_digit (rest mod 10)"; auto split: if_splits; cases rest; auto simp add: nat_to_digit_def)

    then show ?thesis using Cons.prems Cons.IH[OF I1 Rest'] N1 Cons' Rest N1_mod Rest_nz Roundtrip1
      by(cases "nat_to_digit (rest mod 10)"; auto)
  qed
qed

lemma digits_to_nat_to_digits :
  assumes H0 : "digits_canonical dl"
  assumes H: "digits_to_nat dl = Some n"
  shows "nat_to_digits n = Some dl"
proof-

  have H0' : "digits_canonical (rev (rev dl))" using H0
    by (auto)

  show ?thesis using H
    using digits_to_nat_to_digits'[OF H0']
    by(auto simp add: nat_to_digits_def digits_to_nat_def
        simp del: nat_to_digits'.simps digits_to_nat'.simps)
qed

lemma nat_to_digit_Some :
  assumes "n < 10"
  shows "\<exists> d . nat_to_digit n = Some d"
  using assms
  by(auto simp add: nat_to_digit_def split: nat.splits)

lemma nat_to_digits_Some' :
  "\<exists> l . nat_to_digits' n = Some l"
proof(induction rule: full_nat_induct)
  case (1 n)

  have "n mod 10 < 10"
    by auto

  then obtain d1 where D1 : "nat_to_digit (n mod 10) = Some d1"
    using nat_to_digit_Some[of "n mod 10"]
    by (auto )

  show ?case
  proof(cases "n div 10 = 0")
    case True

    then have "n mod 10 = n"
      by auto

    then show ?thesis using D1
      by(auto)
  next
    case False

    then have "(\<exists>l. nat_to_digits' (n div 10) = Some l)"
      using spec[OF "1.IH", of "n div 10"]
      by(auto)

    then obtain l' where IH' : "nat_to_digits' (n div 10) = Some l'"
      by auto

    then show ?thesis using D1
      by(auto)
  qed
qed

lemma nat_to_digits_Some :
  "\<exists> l . nat_to_digits n = Some l"
  using nat_to_digits_Some'[of n]
  unfolding nat_to_digits_def
  by(auto)

definition nat_to_digits_tot :: "nat \<Rightarrow> char list" where
"nat_to_digits_tot n =
  (case nat_to_digits n of
    Some dl \<Rightarrow> dl)"

definition fresh_suffix :: "nat \<Rightarrow> char list" where
"fresh_suffix n = CHR ''_'' # nat_to_digits_tot n"

definition fresh_name :: "YulIdentifier \<Rightarrow> nat \<Rightarrow> YulIdentifier" where
"fresh_name v n =
  (if n = 0 then v
  else String.implode (String.explode v @ fresh_suffix n))"

(* we need to do something about leading zeroes here. *)

function freshen' :: "YulIdentifier \<Rightarrow> nat \<Rightarrow> YulIdentifier list \<Rightarrow> YulIdentifier" where
"freshen' v n l =
  (if List.member l (fresh_name v n)
   then freshen' v (Suc n) (remove1 (fresh_name v n) l)
   else fresh_name v n)"
  by pat_completeness auto

termination freshen'
proof(relation "measure (\<lambda> (v, n, l) . length l)")
  show "wf (measure (\<lambda>(v, n, l). length l))"
    by auto
next
  fix v n l
  assume "List.member l (fresh_name v n)"
  then have "fresh_name v n \<in> set l"
    by (auto simp add: List.member_def)
  then show "((v, Suc n, remove1 (fresh_name v n) l), v, n, l)
       \<in> measure (\<lambda>(v, n, y). length y)"
   by(cases "length l"; auto simp add: length_remove1)
qed

definition freshen :: "YulIdentifier \<Rightarrow> YulIdentifier list \<Rightarrow> YulIdentifier" where
"freshen v l = freshen' v 0 l"

(* statements vs expressions *)
datatype YulIndexElement=
  SiFunctionCallStatementArgs
  | SiFunctionCallExpressionArgs
  | SiAssignmentRhsArgs
  | SiVariableDeclarationRhsArgs
  | SiBlock
  | SiIf
  | SiSwitchExprArgs
  | SiSwitchCase
  | SiFunctionBody
  | SiForPre
  | SiForCondArgs
  | SiForPost
  | SiForBody

(* need to add FunctionDefinitionArgs, FunctionDefinitionRets *)

type_synonym YulIndex = 
  "(YulIndexElement * nat) list"


fun yul_idx_get ::
  "(('v, 't) YulStatement + ('v, 't) YulExpression)\<Rightarrow>
   YulIndex \<Rightarrow>
   (('v, 't) YulStatement + ('v, 't) YulExpression) option"
(*
and
  yul_statement_get_list ::
  "('v, 't) YulStatement list"
*)
  where
(* done *)
"yul_idx_get
  x [] = Some x"

(* Raw function calls *)
| "yul_idx_get 
  x
  ((SiFunctionCallStatementArgs, n)#t) =
  (case x of
   (Inl (YulFunctionCallStatement (YulFunctionCall _ args))) \<Rightarrow>
    (if length args < n then None
     else yul_idx_get (Inr (args ! n)) t)
   | _ \<Rightarrow> None)"
| "yul_idx_get
  x
  ((SiFunctionCallExpressionArgs, n)#t) =
  (case x of
   (Inr (YulFunctionCallExpression (YulFunctionCall _ args))) \<Rightarrow>
    (if length args < n then None
     else yul_idx_get (Inr (args ! n)) t)
   | _ \<Rightarrow> None)"

(* Assignments and declarations, if RHS is a function call *)
| "yul_idx_get
   x
   ((SiAssignmentRhsArgs, n)#t) =
   (case x of
    (Inl (YulAssignmentStatement (YulAssignment _ (YulFunctionCallExpression (YulFunctionCall _ args))))) \<Rightarrow>
     (if length args < n then None
      else yul_idx_get (Inr (args ! n)) t)
    | _ \<Rightarrow> None)"
(* Assignments and declarations, if RHS is a function call *)
| "yul_idx_get
   x
   ((SiVariableDeclarationRhsArgs, n)#t) =
   (case x of
    (Inl (YulVariableDeclarationStatement
            (YulVariableDeclaration _
              (Some (YulFunctionCallExpression (YulFunctionCall _ args)))))) \<Rightarrow>
     (if length args < n then None
      else yul_idx_get (Inr (args ! n)) t)
    | _ \<Rightarrow> None)"

(* Function definition *)
| "yul_idx_get
  x
  ((SiFunctionBody, n)#t) =
  (case x of
   (Inl (YulFunctionDefinitionStatement (YulFunctionDefinition _ _ _ l))) \<Rightarrow>
    (if length l < n then None
     else yul_idx_get (Inl (l!n)) t)
   | _ \<Rightarrow> None)"

(* Control constructs *)
| "yul_idx_get
  x
  ((SiBlock, n)#t) =
  (case x of
    (Inl (YulBlock l)) \<Rightarrow>
      (if length l < n then None
       else yul_idx_get (Inl (l ! n)) t)
    | _ \<Rightarrow> None)"

| "yul_idx_get
  x
  ((SiIf, n)#t) =
  (case x of
    (Inl (YulIf _ l)) \<Rightarrow>
      (if length l < n then None
       else yul_idx_get (Inl (l ! n)) t)
    | _ \<Rightarrow> None)"


| "yul_idx_get 
    x
    ((SiForPre, n)#t) =
    (case x of
      (Inl (YulForLoop l _ _ _)) \<Rightarrow>
        (if length l < n then None
         else yul_idx_get (Inl (l!n)) t)
    | _ \<Rightarrow> None)"

| "yul_idx_get
    x
    ((SiForBody, n)#t) =
    (case x of
      (Inl (YulForLoop _ _ l _)) \<Rightarrow>
        (if length l < n then None
         else yul_idx_get (Inl (l!n)) t)
      | _ \<Rightarrow> None)"
| "yul_idx_get
    x
    ((SiForPost, n)#t) =
    (case x of
      (Inl (YulForLoop _ _ _ l)) \<Rightarrow>
        (if length l < n then None
         else yul_idx_get (Inl (l!n)) t)
      | _ \<Rightarrow> None)"

| "yul_idx_get
    x
    ((SiForCondArgs, n)#t) =
    (case x of
      (Inl (YulForLoop _ (YulFunctionCallExpression (YulFunctionCall _ args)) _ _)) \<Rightarrow>
        (if length args < n then None
         else yul_idx_get (Inr (args ! n)) t)
      | _ \<Rightarrow> None)"

(* switch *)

| "yul_idx_get
    x
    ((SiSwitchExprArgs, n)#t) =
    (case x of
      (Inl (YulSwitch (YulFunctionCallExpression (YulFunctionCall _ args)) _)) \<Rightarrow>
        (if length args < n then None
         else yul_idx_get (Inr (args ! n)) t)
      | _ \<Rightarrow> None)"

| "yul_idx_get
    x
    ((SiSwitchCase, n)#t) =
    (case x of 
      (Inl (YulSwitch _ l)) \<Rightarrow>
        (if length l < n then None
         else
          (case (l!n) of
           (YulSwitchCase _ body) \<Rightarrow> yul_idx_get (Inl (body ! n)) t))
      | _ \<Rightarrow> None)"


(*
 inductive specification of renaming of Yul programs
*)
(*
type_synonym renaming = 
  "(YulIndex, YulIdentifier) alist"

definition renaming_ok' :: "('x * 'y) list \<Rightarrow> bool" where
"renaming_ok' r =
  (distinct o map snd) r"

lift_definition renaming_ok :: "renaming \<Rightarrow> bool" is renaming_ok' .
*)

type_synonym renaming = 
  "(YulIndex * YulIdentifier) list"

(* TODO: we can do better than requiring new variable names to be distinct -
 * but this requires reasoning about contexts/blocks to ensure there are
 * no name collisions generated *)

(* TODO :
 * Currently we are not guaranteeing that the results of substitution don't cause collisions with
 * existing variables. I.e., cases where substitution causes variable shadowing where there wasn't before.
 *)
definition renaming_ok :: "renaming \<Rightarrow> bool" where
"renaming_ok r =
  ((distinct o map fst) r \<and>
   (distinct o map snd) r)"

(* if name matches, rename to new name, otherwise leave *)
definition rename_v ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier" where
"rename_v old new x =
  (if x = old then new else x)"

definition rename_v_t ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> 't YulTypedName \<Rightarrow> 't YulTypedName" where
"rename_v_t old new x =
  (case x of
    (YulTypedName n t) \<Rightarrow>
    (YulTypedName (rename_v old new n) t))"

(* same, for lists of assigned values. here we assume we have already ensured the list does not contain duplicates. *)
definition rename_vs ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier list \<Rightarrow> YulIdentifier list" where
"rename_vs old new xs =
  map (rename_v old new) xs"

definition rename_vs_t ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> 't YulTypedName list \<Rightarrow> 't YulTypedName list" where
"rename_vs_t old new xs =
  map (rename_v_t old new) xs"

(* in the foregoing, we are assuming that we have no shadowing. *)

(* helper function used once we encounter a binder being renamed. 
 * it renames all occurrences of that variable in the subtree, not checking for collisions.*)
fun rename1_statement ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement" 
and rename1_expr ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression"
(* might be able to remove this third function *)
and rename1_switch_case ::
  "YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> ('v, 't) YulSwitchCase \<Rightarrow> ('v, 't) YulSwitchCase"
  where
"rename1_statement v v'
  (YulFunctionCallStatement (YulFunctionCall n args)) =
  (YulFunctionCallStatement (YulFunctionCall (rename_v v v' n)
    (map (rename1_expr v v') args)))"

| "rename1_statement v v'
   (YulAssignmentStatement (YulAssignment ns e)) =
   (YulAssignmentStatement (YulAssignment (rename_vs v v' ns) (rename1_expr v v' e)))"

(* TODO: this is almost definitely an error case, but we assume the error has already
 * been signaled and do the naive thing *)
| "rename1_statement v v'
   (YulVariableDeclarationStatement (YulVariableDeclaration ns oe)) =
   (YulVariableDeclarationStatement
    (YulVariableDeclaration
      (rename_vs_t v v' ns)
      (case oe of None \<Rightarrow> None | Some e \<Rightarrow> Some (rename1_expr v v' e))))"

| "rename1_statement v v'
  (YulFunctionDefinitionStatement (YulFunctionDefinition n args rets body)) =
  (YulFunctionDefinitionStatement
    (YulFunctionDefinition (rename_v v v' n)
                           (rename_vs_t v v' args)
                           (rename_vs_t v v' rets)
                           (map (rename1_statement v v') body)))"

| "rename1_statement v v'
  (YulIf e body) =
  (YulIf (rename1_expr v v' e)
         (map (rename1_statement v v') body))"

| "rename1_statement v v'
  (YulSwitch e cs) =
  (YulSwitch (rename1_expr v v' e)
             (map (rename1_switch_case v v') cs))"

| "rename1_statement v v'
  (YulForLoop pre cond post body) =
  (YulForLoop (map (rename1_statement v v') pre)
              (rename1_expr v v' cond)
              (map (rename1_statement v v') post)
              (map (rename1_statement v v') body))"

| "rename1_statement v v'
   (YulBlock l) =
   (YulBlock (map (rename1_statement v v') l))"

| "rename1_statement v v' x = x"

| "rename1_switch_case v v'
  (YulSwitchCase x body) =
  (YulSwitchCase x (map (rename1_statement v v') body))"

| "rename1_expr v v' (YulFunctionCallExpression (YulFunctionCall n args)) =
   (YulFunctionCallExpression (YulFunctionCall (rename_v v v' n)
    (map (rename1_expr v v') args)))"

| "rename1_expr v v' (YulIdentifier n) =
   (YulIdentifier (rename_v v v' n))"

| "rename1_expr v v' x = x"

(* problem is that function definitions also declare parameters
 * (inputs + outputs), and we need to properly handle those. *)
fun find_and_rename_statement ::
  "YulIndex \<Rightarrow> YulIdentifier \<Rightarrow>
    ('v, 't) YulStatement \<Rightarrow>
    ('v, 't) YulStatement option" where

(* base cases must correspond to a variable binding. *)

(* we assume we are applied at the block level. *)
(* this doesn't check for use before define *)
"find_and_rename_statement [] v st = None"
| "find_and_rename_statement
    [(ix, n)] v st =
    let v_old =
      (case yul_idx_get [(ix, n)] st of
        Some (YulFunctionDefinitionStatement (YulFunctionDefinition)
    

(*
fun rename_statement ::
  "renaming \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement"
*)

(* need to either catch duplicate ids in the same scope, or have a pass that does *)

(* restriction: can't define functions in init block of for loop *)
(* one approach to renaming: walk the tree and do the renaming in one pass.
 *)
(* this current one won't catch duplicate ids in the same scope. *)
(* this one also just renames declaration sites, not usage sites.
 * still hopefully it will give a flavor of what the rest should look like. *)
fun rename_inplace' ::
  "('v, 't) YulStatement \<Rightarrow>
   YulIdentifier list \<Rightarrow>
   (('v, 't) YulStatement * YulIdentifier list) option"
and
  rename_inplace'_list ::
  "('v, 't) YulStatement list \<Rightarrow>
   YulIdentifier list \<Rightarrow>
   (('v, 't) YulStatement list * YulIdentifier list) option"
and
  rename_inplace'_switch ::
  "('v, 't) YulSwitchCase list \<Rightarrow>
   YulIdentifier list \<Rightarrow>
   (('v, 't) YulSwitchCase list * YulIdentifier list) option"
  where
(* do we need to rename the parameters to functions? *)
"rename_inplace' (YulFunctionDefinitionStatement
  (YulFunctionDefinition name p1 p2 body)) ids =
    (let name' = freshen name ids in
     (case rename_inplace'_list body (name'#ids) of
      Some (body', ids') \<Rightarrow> 
        Some ((YulFunctionDefinitionStatement
              (YulFunctionDefinition name' p1 p2 body')), (ids'))
      | None \<Rightarrow> None))"
| "rename_inplace' (YulBlock ls) ids = 
   (case rename_inplace'_list ls ids of
      Some (ls', ids') \<Rightarrow> Some (YulBlock ls', ids')
     | None \<Rightarrow> None)"
| "rename_inplace' (YulIf c body) ids =
   (case rename_inplace'_list body ids of
      Some (body', ids') \<Rightarrow> Some (YulIf c body', ids')
      | None \<Rightarrow> None)"
| "rename_inplace' (YulSwitch c cases) ids = 
   (case rename_inplace'_switch cases ids of
    Some (cases', ids') \<Rightarrow> Some (YulSwitch c cases', ids')
    | _ \<Rightarrow> None)"
| "rename_inplace' (YulForLoop pre c post body) ids =
    (case rename_inplace'_list pre ids of
     Some (pre', ids') \<Rightarrow> 
      (case rename_inplace'_list post ids' of
       Some (post', ids'') \<Rightarrow>
       (case rename_inplace'_list body ids'' of
        Some (body', ids''') \<Rightarrow>
          Some (YulForLoop pre' c post' body', ids''')
          | _ \<Rightarrow> None)
       | _ \<Rightarrow> None)
     | _ \<Rightarrow> None)"

| "rename_inplace' x ids = Some (x, ids)"

| "rename_inplace'_list [] ids = Some ([], ids)"
| "rename_inplace'_list (h#t) ids = 
    (case rename_inplace' h ids of
     None \<Rightarrow> None
     | Some (h', ids') \<Rightarrow>
       (case rename_inplace'_list t (ids') of
        None \<Rightarrow> None
        | Some (t', ids'') \<Rightarrow> Some (h'#t', ids'')))"

| "rename_inplace'_switch [] ids = Some ([], ids)"
| "rename_inplace'_switch ((YulSwitchCase c body)#t) ids =
   (case rename_inplace'_list body ids of
    Some (body', ids') \<Rightarrow>
     (case rename_inplace'_switch t ids' of
      Some (t', ids'') \<Rightarrow> Some ((YulSwitchCase c body')#t', ids'')
      | None \<Rightarrow> None)
    | None \<Rightarrow> None)"


end