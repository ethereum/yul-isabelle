theory Renamer
  imports YulSyntax YulSemanticsSingleStep

begin

(* find the first occurrence of an item in a list *)
(*
fun position' :: "'a list \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> nat option" where
"position' [] _ _ = None"
| "position' (h#t) k n =
  (if h = k then Some n
   else position' t k (Suc n))"

definition position :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
"position l k = position' l k 0"

definition digits :: "char list" where
"digits = 
  [ (CHR ''0''), (CHR ''1''), (CHR ''2''), (CHR ''3''), (CHR ''4'')
  , (CHR ''5''), (CHR ''6''), (CHR ''7''), (CHR ''8''), (CHR ''9'')
  ]"

fun digit_to_nat :: "char \<Rightarrow> nat option" where
"digit_to_nat c =
  position digits c"
*)


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


(* we need to do something about leading zeroes here. *)

(*
  gather function defs
  depth?
*)
(*
definition freshen :: "YulIdentifier \<Rightarrow> YulIdentifier list \<Rightarrow> YulIdentifier" where
"freshen i l =
  

(* restriction: can't define functions in init block of for loop *)
fun rename_inplace' ::
  "('v, 't) YulStatement \<Rightarrow>
   YulIdentifier list \<Rightarrow>
   ('v, 't) YulStatement option"
  where
"rename_inplace' (YulFunctionDefinitionStatement
  (YulFunctionDefinition name _ _ body)) =
    ()"
  | "rename_inplace' x l = Some x"
*)
end