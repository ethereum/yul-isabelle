theory Tries
imports Main "HOL-Word.Word"
begin

datatype ('v) bintrie =
  TLeaf
  | TNode "'v option" "('v) bintrie" "('v) bintrie"


class rx_key =
  fixes rx_divmod ::
    "'a \<Rightarrow> ('a * bool) option"
  fixes rx_emp :: "'a"
  fixes rx_size :: "'a \<Rightarrow> nat"

  assumes rx_divmod_distinct :
    "\<And> (x :: 'a) (x' :: 'a) .
      rx_divmod x = rx_divmod x' \<Longrightarrow> x = x'"

  assumes rx_size_emp : "rx_size rx_emp = 0"

  assumes rx_size_divmod :
    "rx_divmod x = Some (y, b) \<Longrightarrow> rx_size x > rx_size y"
begin
end

lemma rx_divmod_emp :
  "rx_divmod (rx_emp :: 'a :: rx_key) = None"
proof(cases "rx_divmod (rx_emp :: 'a :: rx_key)")
  case None
  then show ?thesis 
    by(auto)
next
  case (Some a)
  obtain y b where A : "a = (y, b)"
    by(cases a; auto)
  then show ?thesis 
    using rx_size_divmod[of "rx_emp :: 'a :: rx_key" y b]
    unfolding rx_size_emp using Some A by auto
qed

lemma rx_emp_size :
  fixes a :: "'a :: rx_key"
  assumes H : "rx_size a = 0"
  shows "a = rx_emp"
proof(cases "rx_divmod a")
  case None
  then show ?thesis using rx_divmod_distinct[of a rx_emp]
    unfolding rx_divmod_emp by auto
next
  case (Some a')
  obtain y b where A' : "a' = (y, b)"
    by(cases a'; auto)
  then show ?thesis 
    using H rx_size_divmod[of a y b] Some by auto
qed

(*
function (sequential) bt_insert ::
  "'v bintrie \<Rightarrow> ('k :: semiring_bits) \<Rightarrow> 'v \<Rightarrow> 'v bintrie" where
"bt_insert TLeaf k v =
  (if k = 0 then TNode (Some v) TLeaf TLeaf
   else
   (if k mod 2 = 0 then
       TNode None (bt_insert TLeaf (k div 2) v) TLeaf
    else
       TNode None TLeaf (bt_insert TLeaf (k div 2) v)))"
| "bt_insert (TNode x t1 t2) k v =
   (if k = 0 then TNode (Some v) t1 t2
    else
    (if k mod 2 = 0 then
        TNode x (bt_insert t1 (k div 2) v) t2
     else
        TNode x t1 (bt_insert t2 (k div 2) v)))"
  by pat_completeness auto
*)

function (sequential) bt_insert ::
  "'v bintrie \<Rightarrow> ('k :: rx_key) \<Rightarrow> 'v \<Rightarrow> 'v bintrie" where
"bt_insert TLeaf k v =
  (case rx_divmod  k of
    None \<Rightarrow> TNode (Some v) TLeaf TLeaf
    | Some (k', False) \<Rightarrow> TNode None (bt_insert TLeaf (k') v) TLeaf
    | Some (k', True) \<Rightarrow> TNode None TLeaf (bt_insert TLeaf (k') v))"
| "bt_insert (TNode x t1 t2) k v =
  (case rx_divmod  k of
    None \<Rightarrow> TNode (Some v) t1 t2
    | Some (k', False) \<Rightarrow> TNode x (bt_insert t1 (k') v) t2
    | Some (k', True) \<Rightarrow> TNode x t1 (bt_insert t2 (k') v))"
  by pat_completeness auto

termination
  by(relation "measure (\<lambda> (t, k, v) . rx_size k)"; 
      auto simp add: rx_size_divmod)

function (sequential) bt_get ::
  "'v bintrie \<Rightarrow> ('k :: rx_key) \<Rightarrow> 'v option" where
"bt_get TLeaf k = None"
| "bt_get (TNode x t1 t2) k =
  (case rx_divmod k of
   None \<Rightarrow> x
   | Some (k', False) \<Rightarrow> bt_get t1 k'
   | Some (k', True) \<Rightarrow> bt_get t2 k')"
  by pat_completeness auto

termination
  by(relation "measure (\<lambda> (t, k) . rx_size k)"; 
      auto simp add: rx_size_divmod)

lemma bt_insert_get_eq :
  fixes t :: "('v) bintrie"
  fixes k :: "'k :: rx_key"
  shows "bt_get (bt_insert t k v) k = Some v"
proof(induction "rx_size k" arbitrary: k t v rule: nat_less_induct)
  case 1
  show ?case 
  proof(cases t)
    case TLeaf
    show ?thesis 
    proof(cases "rx_divmod k")
      case None
      then show ?thesis using TLeaf by(simp)
    next
      case (Some a)
      obtain b k' where A : "a = (k', b)"
        by(cases a; auto)

      have LessSz : "rx_size k' < rx_size k"
        using rx_size_divmod Some A by auto

      show ?thesis
      proof(cases b)
        case True

        (* TODO: this is _awful_ *)
        then show ?thesis using True Some TLeaf 
          spec[OF mp[OF spec[OF HOL.mp[OF spec[OF "1", of "rx_size k'"] LessSz], of k'] refl]
              , of TLeaf] A
          by(auto)
      next
        case False
        then show ?thesis using Some TLeaf 
          spec[OF mp[OF spec[OF HOL.mp[OF spec[OF "1", of "rx_size k'"] LessSz], of k'] refl]
              , of TLeaf] A
          by(auto)
      qed
    qed
  next
    case (TNode vx t1 t2)
    show ?thesis
    proof(cases "rx_divmod k")
      case None
      then show ?thesis using TNode by(simp)
    next
      case (Some a)
      obtain b k' where A : "a = (k', b)"
        by(cases a; auto)

      have LessSz : "rx_size k' < rx_size k"
        using rx_size_divmod Some A by auto

      show ?thesis
      proof(cases b)
        case True

        (* TODO: this is _awful_ *)
        then show ?thesis using True Some TNode
          spec[OF mp[OF spec[OF HOL.mp[OF spec[OF "1", of "rx_size k'"] LessSz], of k'] refl]
              , of t2] A
          by(auto)
      next
        case False
        then show ?thesis using Some TNode
          spec[OF mp[OF spec[OF HOL.mp[OF spec[OF "1", of "rx_size k'"] LessSz], of k'] refl]
              , of t1] A
          by(auto)
      qed
    qed
  qed
qed

lemma bt_insert_get_neq :
  fixes t :: "('v) bintrie"
  fixes k k' :: "'k :: rx_key"
  assumes H : "k \<noteq> k'"
  shows "bt_get (bt_insert t k' v) k = bt_get t k" using assms
proof(induction "rx_size k" arbitrary: k k' t v rule: nat_less_induct)
  case 1
  show ?case 
  proof(cases t)
    case TLeaf
    show ?thesis 
    proof(cases "rx_divmod k")
      case None

      show ?thesis
      proof(cases "rx_divmod k'")
        case None' : None
        then show ?thesis using "1.prems" TLeaf None rx_divmod_distinct[of k k'] by(auto)
      next
        case Some' : (Some a')
        obtain j' b' where A' : "a' = (j', b')" by(cases a'; auto)

        show ?thesis
        proof(cases b')
          case True' : True
          then show ?thesis using A' Some' None TLeaf by(auto)
        next
          case False' : False
          then show ?thesis using A' Some' None TLeaf by(auto)
        qed
      qed
    next
      case (Some a)
      obtain j b where A : "a = (j, b)"
        by(cases a; auto)

      have LessSz : "rx_size j < rx_size k"
        using rx_size_divmod Some A by auto

      show ?thesis
      proof(cases "rx_divmod k'")
        case None' : None
        show ?thesis
        proof(cases b)
          case True
          then show ?thesis using A Some None' TLeaf by(auto)
        next
          case False
          then show ?thesis using A Some None' TLeaf by(auto)
        qed
      next
        case Some' : (Some a')
        obtain j' b' where A' : "a' = (j', b')" by(cases a'; auto)

        have LessSz' : "rx_size j' < rx_size k'"
          using rx_size_divmod Some' A' by auto

        show ?thesis
        proof(cases b)
          case True
          show ?thesis
          proof(cases b')
            case True' : True

            have Neq' : "j \<noteq> j'"
              using rx_divmod_distinct[of k k']
                A A' Some Some' True True' TLeaf "1"(2)
              by(auto)

            then show ?thesis using A A' Some Some' True True' TLeaf
                spec[OF mp[OF spec[OF mp[OF spec[OF mp[OF spec[OF "1"(1), of "rx_size j"] LessSz], of j] refl], of j'] Neq']
                    , of TLeaf]
              by(auto)
          next
            case False' : False
            then show ?thesis using A A' Some Some' True False' TLeaf by(auto)
          qed
        next
          case False
          show ?thesis
          proof(cases b')
            case True' : True
            then show ?thesis using A A' Some Some' False True' TLeaf by(auto)
          next
            case False' : False
            have Neq' : "j \<noteq> j'"
              using rx_divmod_distinct[of k k']
                A A' Some Some' False False' TLeaf "1"(2)
              by(auto)

            then show ?thesis using A A' Some Some' False False' TLeaf
                spec[OF mp[OF spec[OF mp[OF spec[OF mp[OF spec[OF "1"(1), of "rx_size j"] LessSz], of j] refl], of j'] Neq']
                    , of TLeaf]
              by(auto)
          qed
        qed
      qed
    qed
  next
    case (TNode vx t1 t2)
    show ?thesis
    proof(cases "rx_divmod k")
      case None

      show ?thesis
      proof(cases "rx_divmod k'")
        case None' : None
        then show ?thesis using "1.prems" TNode None rx_divmod_distinct[of k k'] by(auto)
      next
        case Some' : (Some a')
        obtain j' b' where A' : "a' = (j', b')" by(cases a'; auto)

        show ?thesis
        proof(cases b')
          case True' : True
          then show ?thesis using A' Some' None TNode by(auto)
        next
          case False' : False
          then show ?thesis using A' Some' None TNode by(auto)
        qed
      qed
    next
      case (Some a)
      obtain j b where A : "a = (j, b)"
        by(cases a; auto)

      have LessSz : "rx_size j < rx_size k"
        using rx_size_divmod Some A by auto

      show ?thesis
      proof(cases "rx_divmod k'")
        case None' : None
        show ?thesis
        proof(cases b)
          case True
          then show ?thesis using A Some None' TNode by(auto)
        next
          case False
          then show ?thesis using A Some None' TNode by(auto)
        qed
      next
        case Some' : (Some a')
        obtain j' b' where A' : "a' = (j', b')" by(cases a'; auto)

        have LessSz' : "rx_size j' < rx_size k'"
          using rx_size_divmod Some' A' by auto

        show ?thesis
        proof(cases b)
          case True
          show ?thesis
          proof(cases b')
            case True' : True

            have Neq' : "j \<noteq> j'"
              using rx_divmod_distinct[of k k']
                A A' Some Some' True True' TNode "1"(2)
              by(auto)

            then show ?thesis using A A' Some Some' True True' TNode
                spec[OF mp[OF spec[OF mp[OF spec[OF mp[OF spec[OF "1"(1), of "rx_size j"] LessSz], of j] refl], of j'] Neq']
                    , of t2]
              by(auto)
          next
            case False' : False
            then show ?thesis using A A' Some Some' True False' TNode by(auto)
          qed
        next
          case False
          show ?thesis
          proof(cases b')
            case True' : True
            then show ?thesis using A A' Some Some' False True' TNode by(auto)
          next
            case False' : False
            have Neq' : "j \<noteq> j'"
              using rx_divmod_distinct[of k k']
                A A' Some Some' False False' TNode "1"(2)
              by(auto)

            then show ?thesis using A A' Some Some' False False' TNode
                spec[OF mp[OF spec[OF mp[OF spec[OF mp[OF spec[OF "1"(1), of "rx_size j"] LessSz], of j] refl], of j'] Neq']
                    , of t1]
              by(auto)
          qed
        qed
      qed
    qed
  qed
qed

(* instances: nat, word, string literal *)

fun rx_divmod_nat ::
  "nat \<Rightarrow> (nat * bool) option" where
"rx_divmod_nat i = 
  (if i = (0 :: nat) then None
   else Some (i div 2, (i mod 2 = 1)))"

lemma rx_divmod_nat_distinct :
  assumes H : "rx_divmod_nat n1 = rx_divmod_nat n2"
  shows "n1 = n2" using assms
proof(induction n1  arbitrary: n2 rule: nat_bit_induct)
  case zero
  then show ?case 
    by(cases n2; auto)
next
  case (even n)
  show ?case
  proof(cases n2)
    case 0
    then show ?thesis using even
      by(auto)
  next
    case (Suc nat)
    then show ?thesis using even
      by(auto)
  qed
next
  case (odd n)
  show ?case
  proof(cases n)
    case 0
    then show ?thesis 
    proof(cases n2)
      case Zero' : 0
      then show ?thesis using 0 odd.prems
        by(auto)
    next
      case (Suc nat)
      then show ?thesis using 0 odd.prems
        by(auto)
    qed
  next
    case (Suc n')
    then show ?thesis
    proof(cases n2)
      case Zero' : 0
      then show ?thesis using Suc odd.prems
        by(auto)
    next
      case Suc' : (Suc nat)
      have Odd: "odd (Suc nat)"
        using Suc odd.prems Suc'
        unfolding odd_iff_mod_2_eq_one
        by(clarsimp)
        
      then show ?thesis using Suc odd.prems Suc' 
          odd_two_times_div_two_nat[OF Odd]
          odd.IH[of "n2 div 2"]
        by(auto)
    qed
  qed
qed

instantiation nat :: rx_key begin

definition nat_rx_divmod :
"rx_divmod = rx_divmod_nat "

definition nat_rx_emp : 
"rx_emp = (0 :: nat)"

definition nat_rx_size :
"rx_size n = (n :: nat)"

instance proof
  fix x x' :: nat
  show "rx_divmod x = rx_divmod x' \<Longrightarrow> x = x'"
    using rx_divmod_nat_distinct[of x x']
    unfolding nat_rx_divmod
    by auto
next
  show "rx_size (rx_emp :: nat) = (0 :: nat)"
    unfolding nat_rx_emp nat_rx_size by auto
next
  fix x y :: nat
  fix b :: bool
  assume "rx_divmod x = Some (y, b)"
  then show "rx_size y < rx_size x"
    by(cases x; auto simp add: nat_rx_divmod nat_rx_size)
qed
end

fun rx_divmod_word ::
  "(('a :: len) word) \<Rightarrow> (('a :: len) word * bool) option" where
"rx_divmod_word i = 
  (if i = word_of_int 0 then None
   else Some (word_of_int ((uint i) div 2), ((uint i) mod 2 = 1)))"

(* TODO *)
lemma rx_divmod_word_distinct :
  fixes w1 w2 :: "('a :: len) word"
  assumes H : "rx_divmod_word w1 = rx_divmod_word w2"
  shows "w1 = w2" using assms
proof(cases "w1 = 0")
  case True
  show ?thesis 
  proof(cases "w2 = 0")
    case True' : True
    then show ?thesis using True by auto
  next
    case False' : False
    then show ?thesis using H True by(auto)
  qed
next
  case False
  show ?thesis 
  proof(cases "w2 = 0")
    case True' : True
    then show ?thesis using H False
      by(auto)
  next
    case False' : False
    then show ?thesis 
    proof(cases "uint w1 mod 2 = 1")
      case True'' : True

      have Eq : "(word_of_int (uint w1 div 2) :: 'a word) = word_of_int (uint w2 div 2)"
        using False False' H True''
        by(auto)

      have Lt1 : "uint w1 < 2 ^ LENGTH('a)"
        using uint_lt[of w1] by auto

      hence Lt1' : "uint w1 div 2 < 2 ^ LENGTH('a)"
        using uint_0[of w1] by(arith)

      have Lt2 : "uint w2 < 2 ^ LENGTH('a)"
        using uint_lt[of w2] by auto

      hence Lt2' : "uint w2 div 2 < 2 ^ LENGTH('a)"
        using uint_0[of w2] by(arith)

      have Ge1 : "0 \<le> uint w1 div 2" using uint_0[of w1]
        by arith

      have Ge2 : "0 \<le> uint w2 div 2" using uint_0[of w2]
        by arith

      have "uint w1 div 2 = uint w2 div 2" 
        using arg_cong[OF Eq, of uint] 
           uint_0[of "w2 div 2"] uint_0[of "w1 div 2"]
          int_mod_eq'[OF Ge1 Lt1'] int_mod_eq'[OF Ge2  Lt2']
        by(simp add: uint_word_of_int)

      then show ?thesis using H False False' True''
          Misc_Arithmetic.dme[of "uint w1" 2]
          Misc_Arithmetic.dme[of "uint w2" 2]
        by(auto)
    next
      case False'' : False
      then obtain q qa where
        Q: "uint w1 = 2 * q" "uint w2 = 2 * qa" and
           Qeq : "(word_of_int q :: 'a word) = word_of_int qa"
        using False False' H by(auto) 

      have Qgt0 : "0 \<le> q"
        using Word.uint_range'[of w1] Q by auto

      have QLt : "q < 2 ^ LENGTH('a)" using uint_lt[of w1] Q Qgt0
        by(auto)

      have Qagt0 : "0 \<le> qa"
        using Word.uint_range'[of w2] Q by auto

      have QaLt : "qa < 2 ^ LENGTH('a)" using uint_lt[of w2] Q Qagt0
        by(auto)

      have Qeq' : "q = qa"
        using False False' H Q Qeq 
        unfolding word.abs_eq_iff no_bintr_alt1
          using int_mod_eq'[OF Qgt0 QLt] int_mod_eq'[OF Qagt0 QaLt]
          by(auto)

      show ?thesis using False False' H Q Qeq word_uint_eqI[of w1 w2]
        unfolding word.abs_eq_iff no_bintr_alt1 Qeq'
        by(auto)
    qed
  qed
qed


instantiation word :: (len) rx_key begin
definition word_rx_divmod :
  "rx_divmod (w :: ('a :: len) word) = rx_divmod_word w"

definition word_rx_emp :
"rx_emp = (word_of_int 0 :: 'a word)"

definition word_rx_size :
"rx_size (n :: ('a :: len) word) =
  unat n"

declare [[show_sorts]] declare [[show_types]]
instance proof
  fix x x' :: "'a word"
  show "rx_divmod x = rx_divmod x' \<Longrightarrow> x = x'"
    using rx_divmod_word_distinct[of x x']
    unfolding word_rx_divmod by auto
next
  show "rx_size (rx_emp :: 'a word) = (0::nat)"
    unfolding word_rx_emp word_rx_size by auto
next
  fix x y :: "'a word"
  fix b :: bool
  assume H: "rx_divmod x = Some (y, b)"
  then show "rx_size y < rx_size x"
  proof(cases "x = 0")
    case True
    then show ?thesis using H by(simp add: word_rx_size word_rx_divmod)
  next
    case False

    then have NZ : "uint x \<noteq> 0" 
      using word_uint_eqI[of x 0]
      by(cases "uint x = 0"; auto)

    have GZ : "(0::int) < uint x"
      using NZ uint_ge_0[of x] by(arith)

    have Rew2 : "\<And> q . 0 < q \<Longrightarrow> q mod (2::int) ^ LENGTH('a) < (2::int) * q"
    proof-
      fix q :: int
      assume H : "0 < q"
      have Leq : "q mod (2::int) ^ LENGTH('a) \<le> q" using int_mod_le H
        by auto

      have Lt : "q < (2 :: int) * q" using H by auto

      thus "q mod (2::int) ^ LENGTH('a) < (2::int) * q"
        using Leq Lt by arith
    qed

    show ?thesis
    proof(cases "(uint x mod (2::int) = (1::int))")
      case True' : True

      have Rew1 : "(uint x div (2::int)) mod (2::int) ^ LENGTH('a) < uint x"
      proof-
        have Lt : "uint x div 2 < uint x" using GZ by auto

        have Leq : "(uint x div (2::int)) mod (2::int) ^ LENGTH('a) \<le> uint x div 2"
          using int_mod_le GZ by auto

        show "(uint x div (2::int)) mod (2::int) ^ LENGTH('a) < uint x"
          using Lt Leq by arith
      qed

      show ?thesis using True' False GZ H uint_0[of x]
        by(auto simp add: word_rx_size word_rx_divmod unat_def uint_word_of_int Rew1)
    next
      case False' : False
      then show ?thesis using False GZ H uint_0[of x]
        by(auto simp add: word_rx_size word_rx_divmod unat_def uint_word_of_int Rew2 )
    qed
  qed
qed
end      

type_synonym partial_char =
    "(bool *
     (bool *
     (bool *
     (bool *
     (bool *
     (bool *
      bool option) option) option) option) option) option) option"

fun partial_char_sz :: "partial_char \<Rightarrow> nat" where
"partial_char_sz None = 0"
| "partial_char_sz (Some (_, None)) = 1"
| "partial_char_sz (Some (_, Some (_, None))) = 2"
| "partial_char_sz (Some (_, Some (_, Some (_, None)))) = 3"
| "partial_char_sz (Some (_, Some (_, Some (_, Some (_, None))))) = 4"
| "partial_char_sz (Some (_, Some (_, Some (_, Some (_, Some (_, None)))))) = 5"
| "partial_char_sz (Some (_, Some (_, Some (_, Some (_, Some (_, Some (_, None))))))) = 6"
| "partial_char_sz (Some (_, Some (_, Some (_, Some (_, Some (_, Some (_, Some _))))))) = 7"

fun partial_char_split :: "char \<Rightarrow> partial_char * bool" where
"partial_char_split c =
 (Some (digit1 c, Some (digit2 c, Some (digit3 c, Some (digit4 c, 
  Some (digit5 c, Some (digit6 c, Some (digit7 c))))))), digit0 c)"

fun partial_char_divmod ::
  "partial_char \<Rightarrow> (partial_char * bool) option" where
"partial_char_divmod None = None"
| "partial_char_divmod (Some (b, None)) = Some (None, b)"
| "partial_char_divmod 
  (Some (b0, Some (b1, None))) =
  Some (Some (b1, None), b0)"
| "partial_char_divmod
  (Some (b0, Some (b1, Some (b2, None)))) =
   Some (Some (b1, Some (b2, None)), b0)"
| "partial_char_divmod
  (Some (b0, Some (b1, Some (b2, Some (b3, None))))) =
   Some (Some (b1, Some (b2, Some (b3, None))), b0)"
| "partial_char_divmod
  (Some (b0, Some (b1, Some (b2, Some (b3, Some (b4, None)))))) =
   Some (Some (b1, Some (b2, Some (b3, Some (b4, None)))), b0)"
| "partial_char_divmod
  (Some (b0, Some (b1, Some (b2, Some (b3, Some (b4, Some (b5, None))))))) =
   Some (Some (b1, Some (b2, Some (b3, Some (b4, Some (b5, None))))), b0)"
| "partial_char_divmod
  (Some (b0, Some (b1, Some (b2, Some (b3, Some (b4, Some (b5, Some (b6)))))))) =
  Some (Some (b1, Some (b2, Some (b3, Some (b4, Some (b5, Some (b6, None)))))), b0)"

datatype str' =
  S "char list" 
    "partial_char"

definition str'_emp :: "str'" where
"str'_emp = S [] None"

fun str'_size :: "str' \<Rightarrow> nat" where
"str'_size (S l pc) = 8 * length l + partial_char_sz pc"

fun str'_divmod :: "str' \<Rightarrow> (str' * bool) option" where
"str'_divmod (S [] None) = None"
| "str'_divmod (S (ch#ct) None) =
   (case partial_char_split ch of
    (pc, b) \<Rightarrow> Some (S ct pc, b))"
| "str'_divmod (S t (Some (X))) =
  (case partial_char_divmod (Some X) of
   None \<Rightarrow> None \<comment> \<open>bogus\<close>
   | Some (pc', b) \<Rightarrow> Some (S t pc', b))"

fun str'_of_lit :: "String.literal \<Rightarrow> str'" where
"str'_of_lit l =
  (S (String.explode l) None)"

(* TODO: instance for string keys *)
(*
instantiation String.literal :: rx_key begin
*)
end