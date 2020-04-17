theory AbiEncodeCorrect imports AbiEncodeSpec AbiEncode

begin

(*

(* sketch of what an inductively valid version of the lemma would look like *)
lemma abi_encode_succeed_gen :
  shows
  "(\<forall> code pre post . encode v = Some code \<longrightarrow>
         can_encode_as v (pre @ code @ post) (int (length pre)) (int (length (pre @ code))))"
   and "(True)"
  and "(\<forall> i res off l pre . encode_tuple_tails vs i = Some res \<longrightarrow> 
        (off, l) \<in> set res \<longrightarrow>
        
        True)"

proof(induction rule: encode_encode_tuple_heads_encode_tuple_tails.induct)

(*
  apply(induct v rule: encode_encode_tuple_heads_encode_tuple_tails.induct(1))
*)

(* need rules for heads and tails as well *)

proof(induction v rule: abi_value.induct)
case (Vuint x1 x2)
  then show ?case 
    apply(cut_tac pre = "([])" and post = "[]" in can_encode_as_can_encode_as_list_can_encode_as_list_dyn.intros(1))
      defer
      apply(simp)
     apply(simp)
    sorry
next
case (Vsint x1 x2)
then show ?case sorry
next
  case (Vaddr x)
  then show ?case sorry
next
case (Vbool x)
  then show ?case sorry
next
case (Vfixed x1 x2 x3a)
  then show ?case sorry
next
  case (Vufixed x1 x2 x3a)
  then show ?case sorry
next
case (Vfbytes x1 x2)
  then show ?case sorry
next
  case (Vfunction x1 x2)
  then show ?case sorry
next
  case (Vfarray x1 x2 x3a)
  (* need static and non static cases here *)
  then show ?case sorry
next
  case (Vtuple x1 x2)
  then show ?case
    apply(simp) apply(safe)
     apply(simp split: option.splits)
     apply(clarify)
    defer
     apply(rule_tac can_encode_as_can_encode_as_list_can_encode_as_list_dyn.intros(12))
        apply(clarsimp)
    apply(safe)
    sorry
next
  case (Vbytes x)
  then show ?case sorry
next
  case (Vstring x)
  then show ?case sorry
next
  case (Varray x1 x2)
  then show ?case sorry
qed
  
  apply(rule can_encode_as.intros)
  sorry


*)

(* new induction principle for AbiValue. *)

lemma my_abi_value_induct :
  assumes Huint : "(\<And> n i . P1 (Vuint n i))"
  and Hsint : "(\<And> n i . P1 (Vsint n i))"
  and Haddr : "(\<And> i . P1 (Vaddr i))"
  and Hbool : "(\<And> b . P1 (Vbool b))"
  and Hfixed : "(\<And> m n r . P1 (Vfixed m n r))"
  and Hufixed : "(\<And> m n r . P1 (Vufixed m n r))"
  and Hfbytes : "(\<And> n bs . P1 (Vfbytes n bs))"
  and Hfunction : "(\<And> i j . P1 (Vfunction i j))"
  and Hfarray : "(\<And> t n l . P2 l \<Longrightarrow> P1 (Vfarray t n l))"
  and Htuple : "(\<And> ts vs . P2 vs \<Longrightarrow> P1 (Vtuple ts vs))"
  and Hbytes : "(\<And> bs . P1 (Vbytes bs))"
  and Hstring : "(\<And> s . P1 (Vstring s))"
  and Harray : "(\<And> t vs . P2 vs \<Longrightarrow> P1 (Varray t vs))"
  and Hln : "P2 []"
  and Hlc : "(\<And> t l . P1 t \<Longrightarrow> P2 l \<Longrightarrow>  P2 (t # l))"
shows "P1 v \<and> P2 l"
proof-
  {fix v
    have "P1 v \<and> (\<forall> l t n . v = Vfarray t n l \<longrightarrow> P2 l)
               \<and> (\<forall> vs ts . v = Vtuple ts vs \<longrightarrow> P2 vs)
               \<and> (\<forall> vs t . v = Varray t vs \<longrightarrow> P2 vs)"
    proof(induction)
case (Vuint x1 x2)
then show ?case using Huint by auto next
next
  case (Vsint x1 x2)
then show ?case using Hsint by auto next
next
  case (Vaddr x)
  then show ?case using Haddr by auto next
next
  case (Vbool x)
  then show ?case using Hbool by auto next
next
  case (Vfixed x1 x2 x3a)
  then show ?case using Hfixed by auto next
next
  case (Vufixed x1 x2 x3a)
  then show ?case using Hufixed by auto next
next
case (Vfbytes x1 x2)
  then show ?case using Hfbytes by auto next
next
  case (Vfunction x1 x2)
  then show ?case using Hfunction by auto next
next
  case (Vfarray x1 x2 l)
  then show ?case using Hfarray
  proof(induct l)
    case Nil
    then show ?case using Hln Hfarray by auto next
  next
    case (Cons a l)
    then show ?case using Hlc Hfarray
      apply(clarsimp)
      apply(subgoal_tac "P1 a") apply(clarsimp) apply(metis)
      apply(subgoal_tac "P2 l")  apply(clarsimp) apply(metis)
      done
  qed
next
  case (Vtuple x1 l)
  then show ?case using Htuple
  proof(induct l)
    case Nil
    then show ?case using Hln Htuple by auto next
  next
    case (Cons a l)
    then show ?case using Hlc Htuple
      apply(clarsimp)
      apply(subgoal_tac "P1 a") apply(clarsimp) apply(metis)
      apply(subgoal_tac "P2 l")  apply(clarsimp) apply(metis)
      done
  qed
next
  case (Vbytes x)
  then show ?case using Hbytes by auto next
next
  case (Vstring x)
then show ?case using Hstring by auto next
next
  case (Varray x1 l)
  then show ?case 
  proof(induct l)
    case Nil
    then show ?case using Hln Harray by auto next
  next
    case (Cons a l)
    then show ?case using Hlc Harray
      apply(clarsimp)
      apply(subgoal_tac "P1 a") apply(clarsimp) apply(metis)
      apply(subgoal_tac "P2 l")  apply(clarsimp) apply(metis)
      done
  qed
qed}
  thus ?thesis
    apply(case_tac v) apply(auto)
    done
qed
  

(* helper lemma 1:
   if encoder succeeds, value was valid *)

lemma abi_encode_succeed_valid [rule_format] :
    "\<forall> full_code . encode v = Ok full_code \<longrightarrow>
       abi_type_valid (abi_get_type v) \<and>
       abi_value_valid v"
  apply(induction v; auto simp add: encode_def)
  done

lemma abi_encode_succeed_validt [rule_format] :
      "\<forall> full_code . encode v = Ok full_code \<longrightarrow>
       abi_type_valid (abi_get_type v)"
  apply(simp add:abi_encode_succeed_valid)
  done


lemma abi_encode_succeed_validv [rule_format] :
    "\<forall> full_code . encode v = Ok full_code \<longrightarrow>
       abi_value_valid v"
  apply(clarsimp)
  apply(drule_tac abi_encode_succeed_valid)
  apply(auto)
  done

lemma all_imp_E :
  "(\<And> x . P x \<Longrightarrow> Q x) \<Longrightarrow>
   (\<forall> x . (P x \<longrightarrow> Q x))"
  apply(blast)
  done

(* helper lemma 2: if value was valid, encoder spec will succeed *)

(* if the encoder succeeds, we get a valid encoding according to spec *)
(*
lemma abi_encode_succeed :
  "\<And>  full_code . encode v = Ok full_code \<Longrightarrow>
         can_encode_as v full_code 0 (length full_code)"
*)
(* idea: generalize to add suffixes using dyn?
what about prefixes? *)

(* idea:
    clause 1: encode \<longrightarrow> can_encode for single values

    clause 2.a: static encodes
        - encode vfarray \<longrightarrow> can_encode_as_list for static farray
        - encode vtuple \<longrightarrow> can_encode_as_list for static tuple

    clause 2.b: dynamic encodes
        - encode vfarray \<rightarrow> can_encode_as_list_dyn for dyn farray
        - encode vftuple \<longrightarrow> can_encode_as_list for static tuple
        - encode varray \<longrightarrow> can_encode_as_list_dyn for array

*)

(* TODO: check higher bounds for dynamic cases. *)

(* TODO: we should not have length full_code here. *)

(* TODO: need to include bytes/string here *)

(* TODO: need to handle length fields properly (arrays, bytestreams, strings). *)

(* TODO: need to relate array contents to bounds *)

(*
lemma abi_encode_succeed_gen :
  "(\<forall> code pre post .
      encode v = Ok code \<longrightarrow>
      can_encode_as v (pre @ code @ post) (int (length pre)))"
*)

(*
abi_type_isdynamic t \<Longrightarrow>
       abi_type_valid t \<Longrightarrow>
       farray_value_valid_aux t n l \<Longrightarrow>
       list_all abi_value_valid_aux l \<Longrightarrow>
       encode'_tuple_tails l 0 = Ok x1 \<Longrightarrow>
       encode'_tuple_heads l x1 (heads_length l) [] = Ok code \<Longrightarrow>
       x1a = code \<Longrightarrow>
       is_head_and_tail l (?heads9 code pre post) (?head_types9 code pre post)
        (?tails9 code pre post)
*)

lemma encode_tuple_tails_len :
  "\<And> headlen len_total bvs .
      encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
      length vs = length bvs"
proof(induction vs)
  case Nil
  then show ?case by simp
next
  case (Cons a vs)
  then show ?case 
    apply(clarsimp)
    apply(simp split: if_splits)
     apply(simp split: sum.splits)
     apply(atomize)
    apply(simp split: if_splits)
     apply(auto)

     apply(simp split: sum.splits)
     apply(atomize)
    apply(simp split: if_splits)
    apply(auto)
    done
qed

lemma allI4 :
  "(\<And> a b c d . P a b c d) \<Longrightarrow>
    \<forall> a b c d . P a b c d"
proof(metis)
qed

lemma allI5 :
  "(\<And> a b c d e . P a b c d e) \<Longrightarrow>
    \<forall> a b c d e . P a b c d e"
proof(metis)
qed

lemma encode_tuple_heads_len :
  "\<And> bss tails result .
    encode'_tuple_heads vs bss tails = Ok result \<Longrightarrow>
    length vs = length bss"
proof(induction vs)
  case Nil
  then show ?case
    apply(case_tac bss; auto)
    done
next
  case (Cons a vs)
  then show ?case
    apply(case_tac bss; auto) 
    apply(simp split:if_splits sum.splits)
    done
qed

lemma encode'_tuple_tails_correct_overflow [rule_format] :
  "\<And> headlen len_total bvs offset enc .
    encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
   (\<forall> enc . (offset, enc) \<in> set bvs \<longrightarrow>
   uint_value_valid 256 offset)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(auto)
    apply(simp split:if_split_asm sum.split_asm)
    apply(atomize)
     apply(fastforce)

    apply(case_tac a;  fastforce)
    done
qed

(*
(* need an is_head_and_tail assumption? *)
lemma encode_tuple_tails_correct_gen :
  "\<And> vs_pre headlen len_total bvs vbvs hds tls.
     
     encode'_tuple_tails (vs) headlen len_total = Ok bvs \<Longrightarrow>
     vbvs = (List.zip (vs) bvs) \<Longrightarrow>
     hds = List.map (\<lambda> (v, (ptr, enc)) .
                        (if (abi_type_isstatic (abi_get_type v)) then v
                            else (Vuint 256 ptr))) vbvs  \<Longrightarrow>
     tls = List.map (\<lambda> (v, (ptr, enc)) . (ptr, v))
                    (List.filter (abi_type_isdynamic o abi_get_type o fst) vbvs) \<Longrightarrow>
     is_head_and_tail vs hds 
                         (List.map (\<lambda> v . if abi_type_isstatic (abi_get_type v) then abi_get_type v
                                              else Tuint 256) vs) (set tls)"
proof(induction vs)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(rule_tac iht_nil)
    done
next
  case (Cons a vs)
  then show ?case
    proof (cases "abi_type_isstatic (abi_get_type a)")
    case True
    then show ?thesis using Cons.prems Cons.IH
      apply(case_tac hds; clarsimp)
      apply(case_tac bvs; clarsimp)
      apply(simp split: sum.split_asm)
       apply(simp split:if_split_asm sum.split_asm)
qed
*)

(* Need a clause here saying that all the Tuints are valid as uint 256 *)
(* problem with bvs? *)
declare [[show_types]]

lemma encode_tuple_tails_correct :
  "\<And> headlen len_total bvs vbvs hds tls.
     encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
     vbvs = (List.zip vs bvs) \<Longrightarrow>
     hds = List.map (\<lambda> (v, (ptr, enc)) .
                        (if (abi_type_isstatic (abi_get_type v)) then v
                            else (Vuint 256 ptr))) vbvs  \<Longrightarrow>
     tls = List.map (\<lambda> (v, (ptr, enc)) . (ptr, v))
                    (List.filter (abi_type_isdynamic o abi_get_type o fst) vbvs) \<Longrightarrow>
     is_head_and_tail vs hds 
                         (List.map (\<lambda> v . if abi_type_isstatic (abi_get_type v) then abi_get_type v
                                              else Tuint 256) vs) (tls)"
proof(induction vs)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(rule_tac iht_nil)
    done
next
  case (Cons a vs)
  then show ?case
  proof (cases "abi_type_isstatic (abi_get_type a)")
    case True
    then show ?thesis using Cons.prems Cons.IH
      apply(case_tac hds; clarsimp)
      apply(case_tac bvs; clarsimp)
      apply(simp split: sum.split_asm)
       apply(simp split:if_split_asm sum.split_asm)

      apply(case_tac "encode'_tuple_tails vs headlen len_total"; clarsimp)
      apply(case_tac "uint_value_valid 256 (len_total + headlen)"; clarsimp)
      apply(atomize)
      apply(drule_tac x = headlen in spec) apply(drule_tac x = len_total in spec) apply(clarsimp)
      apply(drule_tac x = a and xs = vs  in iht_static) apply(simp) apply(simp)
      apply(simp)
      done next
    case False
    then show ?thesis using Cons.prems Cons.IH
      apply(case_tac hds; clarsimp)
      apply(case_tac bvs; clarsimp)
       apply(simp split: sum.split_asm)
       apply(simp split:if_split_asm)
      apply(atomize)
      apply(case_tac a; clarsimp)

(* first case = farray *)
           apply(simp split:sum.split_asm if_split_asm)
           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

          apply(drule_tac x = "Vfarray x91 x92 x93" and ptr = "len_total + headlen"  in iht_dynamic)
           apply(clarsimp)
      apply(simp)

(* second case = tuple *)
           apply(simp split:sum.split_asm if_split_asm)
           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

          apply(drule_tac x = "Vtuple x101 x102" and ptr = "len_total + headlen"  in iht_dynamic)
           apply(clarsimp)
         apply(simp) 

(* third case = bytes *)
       apply(simp split:sum.split_asm if_split_asm)
         apply(drule_tac x = headlen in spec) 
         apply(drule_tac x = " (len_total +
         (int (length (word_rsplit (word_of_int (int (length x11a)) :: 256 word))) +
          int (length (case divmod_nat (length x11a) 32 of (d, 0) \<Rightarrow> x11a | (d, Suc rem) \<Rightarrow> x11a @ replicate (31 - rem) 0))))" in spec)
         apply(clarsimp)

        apply(drule_tac x = headlen in spec) 

    apply(drule_tac x = " (len_total +
         (int (length (word_rsplit (word_of_int (int (length x11a)) :: 256 word))) +
          int (length (case divmod_nat (length x11a) 32 of (d, 0) \<Rightarrow> x11a | (d, Suc rem) \<Rightarrow> x11a @ replicate (31 - rem) 0))))" in spec)
         apply(clarsimp)
    apply(drule_tac x = x1 in spec) 

        apply(simp split:prod.splits) 
      (* i still don't understand why this is necessary *)
      apply(safe_step) apply(fastforce)
          apply(drule_tac x = "Vbytes x11a" and ptr = "len_total + headlen"  in iht_dynamic)
         apply(clarsimp)
        apply(clarsimp)

(* fourth case - vstring *)
       apply(simp split:sum.split_asm if_split_asm)
         apply(drule_tac x = headlen in spec) 
         apply(drule_tac x = " (len_total +
         (int (length (word_rsplit (word_of_int (int (length x12a)) :: 256 word))) +
          int (length x1)))" in spec)
         apply(clarsimp)

         apply(drule_tac x = headlen in spec) 
         apply(drule_tac x = " (len_total + int(length b))" in spec)
         apply(clarsimp)

      apply(drule_tac x = "Vstring x12a"
and ptr = "len_total + headlen" in iht_dynamic)
        apply(clarsimp)
      apply(clarsimp)

(* fifth case = array *)
           apply(simp split:sum.split_asm if_split_asm)
           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

           apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec) apply(clarsimp)

          apply(drule_tac x = "Varray x131 x132" and ptr = "len_total + headlen"  in iht_dynamic)
           apply(clarsimp)
      apply(simp)
      done

  qed
qed

lemma funext :
  "
      (\<forall> a . f a = g a) \<Longrightarrow> (\<lambda> a . f a) = (\<lambda> a . g a)"
proof(auto)
qed

(* need to strengthen this to talk about arbitrary tails that have already been computed. *)
(*
lemma encode_tuple_heads_correct [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs ts_post vs_post code_post .
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails =     ((\<lambda>x. case x of (v, ptr, enc) \<Rightarrow> (ptr, v)) ` {x \<in> set (zip l bvs). abi_type_isdynamic (abi_get_type (fst x))}) \<longrightarrow>
   encode_static (Vtuple ts_post vs_post) = Ok code_post \<longrightarrow>
   encode'_tuple_heads vs bvs code_post = Ok code \<longrightarrow>
   encode_static (Vtuple (ts@ts_post) (vs@vs_post)) = Ok code)" (* tails is not the same as tls *)
*)

(* was "tails =", but i think maybe needs to be supseteq *)
(* the map2 (maybe also map) hypothesis is insufficiently general *)
(* do we need to talk about children here? *)
(* list comes from bvs *)

(*
       encode'_tuple_tails l (0::int) (heads_length l) = Ok a \<Longrightarrow>
       encode'_tuple_heads l a [] = Ok code \<Longrightarrow>
       is_head_and_tail l (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) l a)
        (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l)
        (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l a))) \<Longrightarrow>
       encode_static
        (Vtuple (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l)
          (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) l a)) =
       Ok code

*)

lemma encode_static_static [rule_format]:
"(\<forall> code . encode_static v = Ok code \<longrightarrow>
  abi_type_isstatic (abi_get_type v)) \<and>
 (\<forall> v t n code . v = Vfarray t n l \<longrightarrow>
     abi_type_isstatic t \<longrightarrow>
     those_err (map encode_static l) = Ok code \<longrightarrow>
     abi_type_isstatic (abi_get_type v))"
proof(induction rule: my_abi_value_induct)
  case (1 n i)
  then show ?case by auto
next
  case (2 n i)
  then show ?case by auto
next
  case (3 i)
  then show ?case by auto
next
  case (4 b)
  then show ?case by auto
next
  case (5 m n r)
  then show ?case by auto
next
  case (6 m n r)
  then show ?case by auto
next
  case (7 n bs)
  then show ?case by auto
next
  case (8 i j)
  then show ?case by auto
next
  case (9 t n l)
  then show ?case 
    apply(clarsimp)
    apply(simp split:sum.splits)
    apply(case_tac l; clarsimp)
next
  case (10 ts vs)
  then show ?case by auto
next
case (11 bs)
  then show ?case by auto
next
  case (12 s)
  then show ?case by auto
next
  case (13 t vs)
  then show ?case by auto
next
  case 14
  then show ?case by auto
next
  case (15 t l)
  then show ?case by auto
qed

(* need to change this so that we leave off the tail part *)
(* ts_pre/vs_pre. not post *)
(* code vs code_post *)
lemma encode_tuple_heads_correct [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs ts_post vs_post code_post code pre post tails_code .
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<longrightarrow>
   abi_value_valid (Vtuple ts_post vs_post) \<longrightarrow>
   abi_type_isstatic (Ttuple ts_post) \<longrightarrow>
   abi_value_valid (Vtuple ys xs) \<longrightarrow>
  abi_type_isstatic (Ttuple ys) \<longrightarrow>
   encode_static (Vtuple ts_post vs_post) = Ok code_post \<longrightarrow>
   encode'_tuple_heads vs bvs code_post = Ok (code) \<longrightarrow>
   can_encode_as (Vtuple (ts_post@ys) (vs_post@xs)) (pre @code @ post) (int (length pre)))" (* tails is not the same as tls *)
(*
lemma encode_tuple_heads_correct [rule_format] :
"
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs  code pre post  .
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<longrightarrow>
   abi_value_valid (Vtuple ys xs) \<longrightarrow>
  abi_type_isstatic (Ttuple ys) \<longrightarrow>
   encode'_tuple_heads vs bvs [] = Ok (code) \<longrightarrow>
   encode_static (Vtuple (ys) (xs)) = Ok code)"
*)
proof(induction rule:AbiEncodeSpec.is_head_and_tail.induct)
  case iht_nil
  then show ?case 
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    apply(simp split:sum.split_asm)
    apply(rule_tac Estatic) apply(auto)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    apply(simp split:sum.split_asm)

     apply(simp add:tuple_value_valid_aux_def )

    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(drule_tac x = "vs_post @ [x]" in spec) apply(clarsimp)
    apply(drule_tac x = "x1 @ [x1a]" in spec)
    apply(simp split:sum.split)
    apply(subgoal_tac "those_err (map encode_static vs_post @ [Ok x1a]) = Ok (x1 @ [x1a])")
     apply(clarsimp)
    apply(drule_tac x = "x1a @ x1b"  in spec) apply(clarsimp)
     apply(subgoal_tac "encode'_tuple_heads xs list (concat x1 @ x1a) = Ok (x1a @ x1b)")
      apply(clarsimp)

    (* lemmas needed:
       - those_err (easy)
       - encode'_tuple_heads can always be "shifted" (medium)
*) sorry
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case 
    apply(clarsimp)
     apply(simp split:sum.split_asm)
      apply(rule_tac conjI)
     apply(clarsimp)
     apply(case_tac bvs; clarsimp)

    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
     apply(simp split:sum.split_asm) apply(clarsimp)
      apply(drule_tac x = list in spec) apply(clarsimp)
     apply(simp add:tuple_value_valid_aux_def )

    (* lemma: if encode_tuple_heads works for one accumulator then it works
       for any prefix *)
       apply(clarsimp)
(* either this is very wrong because we can't characterize ba,
   or we need to find the right place to insert ba. *)
    apply(drule_tac x = "vs_post @ [Vuint (256::nat) ptr]" in spec) apply(clarsimp)
    apply(case_tac "those_err (map encode_static vs_post @ [Ok (word_rsplit (word_of_int ptr :: 256 word))])"; clarsimp)
    (* err case should be contradiction *)
    apply(drule_tac x = "x1 @ [ba]" in spec) apply(clarsimp)
    apply(drule_tac x = "x1 @ [(word_rsplit (word_of_int ptr :: 256 word)) :: 8 word list]" in spec) apply(clarsimp)
    apply(subgoal_tac " those_err (map encode_static vs_post @ [Ok (word_rsplit (word_of_int ptr :: 256 word))]) = Ok (x1 @ [word_rsplit (word_of_int ptr :: 256 word)])")
     apply(clarsimp)

    apply(case_tac " encode'_tuple_heads xs list (concat x1 @ b)"; clarsimp)

       apply(case_tac "those_err (map (encode_static \<circ> (\<lambda>(x, ptr, enc). if \<not> abi_type_isdynamic (abi_get_type x) then x else Vuint 256 ptr)) (zip xs list) @ map encode_static vs_post)"; clarsimp)

    apply(drule_tac x =
"map (\<lambda>(x, ptr, enc). if \<not> abi_type_isdynamic (abi_get_type x) then x else Vuint 256 ptr) (zip xs list) @ vs_post" in spec)
apply(clarsimp)
(* unsure here *)
    

    apply(clarsimp)
    sorry
(*
    apply(case_tac
"map (encode_static \<circ> (\<lambda>(x, ptr, enc). if \<not> abi_type_isdynamic (abi_get_type x) then x else Vuint 256 ptr)) (zip xs list)", clarsimp)
    apply(case_tac xs; clarsimp)
     apply(case_tac "encode'_tuple_heads xs list (concat x1 @ b)"; clarsimp)
    apply(case_tac " those_err (map encode_static xs @ map encode_static vs_post)"; clarsimp)
     apply(drule_tac x = list in spec) apply(clarsimp)
     apply(case_tac " those_err (map encode_static xs @ map encode_static vs_post)"; clarsimp)

     apply(subgoal_tac "(\<lambda>x. case x of (v, ptr, enc) \<Rightarrow> (ptr, v)) ` {x \<in> set (zip xs list). abi_type_isdynamic (abi_get_type (fst x))} \<subseteq> tails")
    apply(clarsimp)

    apply(drule_tac x = vs_post in spec) apply(clarsimp)
    apply(case_tac "encode_static x"; clarsimp)
     apply(case_tac " those_err (map encode_static xs @ map encode_static vs_post)"; clarsimp)
     apply(case_tac bvs; clarsimp)
     apply(case_tac "encode'_tuple_heads xs list (concat x1) "; clarsimp)
     apply(case_tac bvs; clarsimp)
*)
qed
(* TODO: are our dyn cases constraining
   head/head_types/tails enough? *)
(* here is our full description *)
(*
lemma abi_encode_succeed_gen_new :
  "(\<forall>  code pre post . encode v = Ok code \<longrightarrow>
          (can_encode_as v (pre @ code @ post) (int (length pre)))) \<and>
   (
    (
     (\<forall> t n code pre post .
          abi_type_isdynamic t \<longrightarrow>
          encode (Vfarray t n vs) = Ok code \<longrightarrow>
          (\<exists> heads tails . 
             is_head_and_tail vs (replicate n t) tail
          (can_encode_as_list_dyn vs (pre @ code @ post) (int (length pre)) (int (length (pre @ code))))) \<and>
     (\<forall> ts t code pre post .
           t \<in> set ts \<longrightarrow>
           abi_type_isdynamic t \<longrightarrow>
           encode (Vtuple ts vs) = Ok code \<longrightarrow>
          (can_encode_as_list_dyn vs (pre @ code @ post) (int (length pre)) (int (length (pre @ code))))) \<and>
     (\<forall> t code pre post .
          encode (Varray t vs) = Ok code \<longrightarrow>
          (can_encode_as_list_dyn vs (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))))))
     "
*)

lemma map2_map_fst' :
  "\<And> f l' . 
    length l = length l' \<Longrightarrow>
    map f l = map2 (\<lambda> x _ . f x) l l'"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(auto)
    apply(case_tac l') apply(auto)
    done
qed

(* need abi_value_valid premise *)
lemma abi_encode_succeed_gen_new :
  "(\<forall>  code pre post . encode v = Ok code \<longrightarrow>
          (can_encode_as v (pre @ code @ post) (int (length pre)))) \<and> True"

(* \<and>
   (
    (
     (\<forall>  (a :: (int * 8 word list) list) n code (pre :: 8 word list) (post :: 8 word list) .
          encode'_tuple_heads l a [] = Ok code \<longrightarrow>
       is_head_and_tail l (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) l a)
        (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l)
        (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l a))) \<longrightarrow>
        ((
             can_encode_as (Vtuple (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l)
                                   (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) l a)) (pre @ code @ post) (int (length pre))
        )
        \<and>
        (\<forall> aa ab b . (aa, ab, b) \<in> set (zip l a) \<longrightarrow> can_encode_as aa (pre @ code @ post) (ab + int (length pre))))
        )))"
*)
proof(induction rule: my_abi_value_induct)
case (1 n i)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (2 n i)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (3 i)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (4 b)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (5 m n r)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (6 m n r)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (7 n bs)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (8 i j)
  then show ?case
    apply(clarify)
    (* function case currently unimplimented - this is a bug. *)
    sorry
next
  case (9 t n l)
  then show ?case
  proof(cases "abi_type_isstatic t")
    case True
    then show ?thesis using 9
      apply(clarsimp)
      apply(rule_tac Estatic)
        apply(simp)
       apply(simp add:encode_def split:if_split_asm)
      apply(simp add:encode_def split:if_split_asm)
      done
  next
    case False
    then show ?thesis using 9
      apply(clarsimp)
(*      apply(thin_tac "\<forall>t n code.
          encode (Vfarray t n l) = Ok code \<longrightarrow>
          (\<forall>pre post v'. v' \<in> set l \<longrightarrow> encode v' = Ok code \<longrightarrow> can_encode_as v' (pre @ code @ post) (int (length pre))) ") *)
      apply(simp add:encode_def)
      apply(case_tac " abi_type_valid t \<and> farray_value_valid_aux t n l \<and> list_all abi_value_valid_aux l"; clarsimp)
      apply(case_tac " encode'_tuple_tails l 0 (heads_length l) "; clarsimp)
      apply(case_tac "encode'_tuple_heads l a []"; clarsimp)
      apply(frule_tac encode_tuple_tails_correct)
         apply(simp)
      apply(simp) apply(simp)
      apply(rule_tac Efarray_dyn)
        apply(simp)
         apply(simp)
        apply(simp)
       apply(simp)

(* need to split here. split code into head and tail. *)
       apply(drule_tac x = a in  spec)
      apply(clarsimp)
       apply(subgoal_tac "(filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l a))
=
 (filter (\<lambda>a::abi_value \<times> int \<times> 8 word list. abi_type_isdynamic (abi_get_type (fst a))) (zip l a))")

        apply(clarsimp)
       apply(clarsimp)
       apply(simp add: Fun.o_def)

             apply(drule_tac x = a in  spec)
      apply(clarsimp)
       apply(subgoal_tac "(filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l a))
=
 (filter (\<lambda>a::abi_value \<times> int \<times> 8 word list. abi_type_isdynamic (abi_get_type (fst a))) (zip l a))")

       apply(clarsimp)
       apply(drule_tac x = pre in spec) apply(drule_tac x = post in spec)
       apply(clarsimp)
       apply(drule_tac x = aa in spec) apply(drule_tac x = ab in spec) apply(clarsimp)
      apply(clarsimp)
       apply(simp add: Fun.o_def)
      done
      
  qed
next
  case (10 ts vs)
  then show ?case sorry

next
  case (11 bs)
  then show ?case
    apply(clarify)
    (* need to handle count. *)
    sorry

next
  case (12 s)
  then show ?case sorry
next



  case (13 t vs)
  then show ?case
    sorry
next

(* these cases seem like they may actually be the hard ones. *)
(* The array piece doesn't match. This is to be expected. We are not accounting for
   the length properly lol *)
  case 14
  then show ?case apply(simp add:encode_def) apply(clarsimp)
    apply(rule_tac Estatic)
      apply(simp add:tuple_value_valid_aux_def)
     apply(simp add:tuple_value_valid_aux_def)

    apply(simp) apply(case_tac a) apply(clarsimp)
    apply(clarsimp)
    done
next
  case (15 t l)
  then show ?case
    apply(clarsimp)
    apply(auto)
       apply(rule_tac Estatic)
         apply(clarsimp)
         apply(simp add:list_ex_iff) apply(clarsimp)
         apply(fastforce)

        defer
        apply(clarsimp)
    apply(simp split:sum.splits) apply(rule_tac conjI)
    
    
    apply(rule_tac pre_and_v_code_len = "int (length pre + length code)" in Elcons_static)

         apply(simp add:encode_def)
         apply(simp only: split:if_split_asm sum.split_asm)
           apply(clarsimp)
         apply(case_tac "those_err (encode_static t # map encode_static l)") apply(clarsimp)

    sorry
qed

*)

lemma abi_encode_succeed_gen :
  "\<forall>  full_code offset . encode v = Ok full_code \<longrightarrow>
         (can_encode_as v full_code offset (length full_code + offset))"
proof(induction v)
  case (Vuint x1 x2)
  then show ?case 
    apply(cut_tac n = x1 and i = x2 and pre1 = "[]" and post1 in Euint)
    apply(auto simp add: encode_def intro:can_encode_as_can_encode_as_list_can_encode_as_list_dyn.intros)
    apply(simp split:if_splits)
    apply(cut_tac Euint) apply(auto)
        apply(auto simp add: encode_def intro:Euint)

next
  case (Vsint x1 x2)
  then show ?case sorry
next
  case (Vaddr x)
  then show ?case sorry
next
  case (Vbool x)
then show ?case sorry
next
  case (Vfixed x1 x2 x3a)
  then show ?case sorry
next
  case (Vufixed x1 x2 x3a)
  then show ?case sorry
next
  case (Vfbytes x1 x2)
  then show ?case sorry
next
  case (Vfunction x1 x2)
  then show ?case sorry
next
  case (Vfarray x1 x2 x3a)
  then show ?case 
  proof(cases "abi_type_isdynamic x1")
    case True
    then show ?thesis using Vfarray
      apply(simp)
      apply(drule_tac all_imp_E)
      apply(clarsimp)
      apply(rule_tac pre_and_vs_code_len = "(int (length full_code) + int offset)" in Efarray_dyn)
(* i dont really understand why we are getting
a metavariable here. *)
        apply(simp)

        defer defer
        apply(case_tac x3a) apply(clarsimp) apply(simp add:encode_def)
      apply(simp split:if_split_asm)
         apply(rule_tac n = "int offset" in Elnil_dyn)

        apply(clarsimp) apply(simp add:encode_def)
      apply(case_tac a; clarsimp)
        apply(case_tac "abi_type_isdynamic (abi_get_type a)")
      
         apply(rule_tac Elcons_dyn_h) apply(simp)

      sorry
  next
    case False
    then show ?thesis using Vfarray
      apply(clarsimp)
      apply(rule_tac Efarray_static)
      defer apply(simp )
  qed
    
    sorry
next
  case (Vtuple x1 x2)
  then show ?case sorry
next
  case (Vbytes x)
  then show ?case sorry
next
  case (Vstring x)
  then show ?case sorry
next
  case (Varray x1 x2)
  then show ?case sorry
qed
  sorry
   

(* if the encoder fails, there is no valid encoding according to spec *)
lemma abi_encode_fail :
  "\<And> v full_code . encode v = None \<Longrightarrow>
         can_encode_as v full_code 0 (int (length full_code)) \<Longrightarrow>
         False"

  sorry

end