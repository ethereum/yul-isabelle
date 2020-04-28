theory AbiEncodeCorrect imports AbiEncodeSpec AbiEncode HOL.Int

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
     apply(auto)

     apply(simp split: sum.splits)
     apply(atomize)
    apply(simp split: if_splits)
    apply(auto)
    done
qed

lemma encode_tuple_heads_len :
  "\<And> bss tails result .
    encode'_tuple_heads vs bss  = Ok result \<Longrightarrow>
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
    apply(simp split:if_splits sum.splits prod.splits)
    done
qed

lemma encode'_tuple_tails_correct_overflow [rule_format] :
  "\<And> headlen len_total bvs offset enc .
    encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
   (\<forall> v enc . (v, offset, enc) \<in> set (zip vs bvs) \<longrightarrow>
   abi_type_isdynamic (abi_get_type v) \<longrightarrow>
   uint_value_valid 256 offset)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(auto)
    apply(simp split:if_split_asm sum.split_asm)
    apply(atomize) apply(clarsimp) 
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
      apply(atomize)
      apply(drule_tac x = headlen in spec) apply(drule_tac x = len_total in spec) apply(clarsimp)
      apply(drule_tac x = a and xs = vs  in iht_static) apply(simp) apply(simp)
       apply(simp)

      apply(atomize) apply(clarsimp)
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

(*
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
*)

(* need to change this so that we leave off the tail part *)
(* ts_pre/vs_pre. not post *)
(* code vs code_post *)
lemma encode_tuple_heads_correct1 [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs  code pre post heads_code tails_code .
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<longrightarrow>
   abi_value_valid (Vtuple ys xs) \<longrightarrow>
   abi_type_isstatic (Ttuple ys) \<longrightarrow>
   encode'_tuple_heads vs bvs = Ok (heads_code, tails_code) \<longrightarrow>
   encode_static (Vtuple (ys) (xs)) = Ok (heads_code))" 
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
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    apply(simp split:sum.split_asm)

     apply(simp add:tuple_value_valid_aux_def )

    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(simp split:sum.split)
    done
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

    apply(simp split:sum.split)
    done
qed

(* this isn't quite it - need to tweak parts copied from correct1. *)
(* need to characterize this further. Not enough to know that
is_head_and_tail - also need encode'_tuple_tails
*)
(*
lemma encode_tuple_heads_correct2 [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs  code heads_code tails_code ab ac ba ab_code.
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<longrightarrow>
   abi_value_valid (Vtuple ys xs) \<longrightarrow>
   encode'_tuple_heads vs bvs = Ok (heads_code, tails_code) \<longrightarrow>
   (ac, ab) \<in> set tails \<longrightarrow>
   abi_type_isdynamic (abi_get_type ab) \<longrightarrow>
   (\<exists> ab_code pre post . encode' ab = Ok ab_code \<and> tails_code = pre @ ab_code @ post \<and>
       ac = int (length heads_code) + int (length pre)))"
*)

lemma encode_tuple_heads_correct2 [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   (\<forall> bvs heads_length  code heads_code tails_code ab ac ba ab_code.
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint 256 ptr) vs bvs) \<longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint 256) vs) \<longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<longrightarrow>
   encode'_tuple_tails vs (0::int) (heads_length) = Ok bvs \<longrightarrow>
   abi_value_valid (Vtuple ys xs) \<longrightarrow>
   encode'_tuple_heads vs bvs = Ok (heads_code, tails_code) \<longrightarrow>
   (ac, ab) \<in> set tails \<longrightarrow>
   abi_type_isdynamic (abi_get_type ab) \<longrightarrow>
   (\<exists> ab_code pre post . encode' ab = Ok ab_code \<and> tails_code = pre @ ab_code @ post \<and>
       ac = int (heads_length) + int (length pre)))"
proof(induction rule:AbiEncodeSpec.is_head_and_tail.induct)
  case iht_nil
  then show ?case
    apply(clarsimp)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case 
    apply(clarify)
    apply(case_tac bvs; clarsimp)
    apply(case_tac "encode_static x"; clarsimp) 
    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def)
    apply(simp split:sum.splits)
    apply(case_tac x1a; clarsimp)

    apply(drule_tac x = heads_lengtha in spec) apply(clarsimp)
    apply(drule_tac x = ae in spec)
    apply(drule_tac x = af in spec)

    apply(subgoal_tac
"(af, ae)
       \<in> (\<lambda>x::abi_value \<times> int \<times> 8 word list. case x of (v::abi_value, ptr::int, enc::8 word list) \<Rightarrow> (ptr, v)) `
          {x::abi_value \<times> int \<times> 8 word list \<in> set (zip xs list). abi_type_isdynamic (abi_get_type (fst x))}")
     apply(clarsimp) apply(clarsimp)

    apply(force)
    done
    
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarify)
    apply(case_tac bvs; clarsimp)
        apply(simp split:sum.splits)
    apply(simp split:if_splits)
    apply(drule_tac x = list in spec)
    apply(clarsimp)
    apply(drule_tac x = "(heads_lengtha + length bb)" in spec)
    apply(clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
    apply(drule_tac x = ab in spec)
    apply(drule_tac x = ac in spec)
    apply(clarsimp)
    apply(case_tac "ac = int heads_lengtha \<and> ab = x") apply(clarsimp)
    apply(clarsimp)
     apply(rule_tac x = "bb @ pre" in exI) apply(clarsimp)

    done
qed

lemma those_err_success [rule_format]:
  "\<forall> x out . those_err xs = Ok out \<longrightarrow>
    x \<in> set xs \<longrightarrow> (? x' . x = Ok x')"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    apply(clarsimp)
    apply(case_tac a; clarsimp)
    apply(case_tac "those_err xs"; clarsimp)
    done
qed

definition err_force :: "'x orerror \<Rightarrow> 'x" where
"err_force xe =
  (case xe of Ok x \<Rightarrow> x)"

lemma those_err_map [rule_format]:
  "\<forall> x out . those_err xs = Ok out \<longrightarrow>
     out = map err_force xs"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    apply(clarsimp)
    apply(case_tac a; clarsimp)
    apply(case_tac "those_err xs"; clarsimp)
    apply(simp add:err_force_def)
    done
qed
     

declare [[show_types]]

lemma foldl_plus [rule_format]:
  "\<forall>  x  i.
      x + (foldl ((+) :: int \<Rightarrow> int \<Rightarrow> int) (i :: int) xs) =
      foldl ((+) :: int \<Rightarrow> int \<Rightarrow> int) (x + i) xs"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    apply(clarsimp)
    apply(simp add: add.assoc)
    done
qed
(*
\<forall> ts v code v' t' code' .
        v = (Vtuple ts vs) \<longrightarrow>
        encode_static v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        (v', t') \<in> set (zip vs ts) \<longrightarrow>
        encode_static v' = Ok code' \<longrightarrow>
        (abi_static_size t' = length code'
*)

lemma encode_static_size' [rule_format]:
  "(\<forall> code . 
     encode_static v = Ok code \<longrightarrow>
     abi_value_valid v \<longrightarrow>
     abi_static_size (abi_get_type v) = length code) \<and>
    (
     (\<forall> t n v code  .
        v = (Vfarray t n vs) \<longrightarrow>
        encode_static v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        (
         n * (abi_static_size t) = length code)) \<and>
      ( \<forall> ts v code  .
        v = (Vtuple ts vs) \<longrightarrow>
        encode_static v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        foldl (+) 0 (map abi_static_size ts) = length code))"
proof(induction rule: my_abi_value_induct)
case (1 n i)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (2 n i)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (3 i)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (4 b)
  then show ?case by (case_tac b; auto simp add:word_rsplit_def bin_rsplit_len)
next
  case (5 m n r)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (6 m n r)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (7 n bs)
  then show ?case 
    apply(clarsimp)
    apply(simp split:prod.splits) apply(auto)
    apply(case_tac x2;auto) 
  apply(simp add:fbytes_value_valid_def)
     apply(simp add:divmod_nat_def) apply(clarsimp)
     apply(case_tac bs; clarsimp) 
     apply(drule_tac Nat.dvd_imp_le) apply(simp) apply(simp)
  apply(simp add:fbytes_value_valid_def)
     apply(simp add:divmod_nat_def) apply(clarsimp)
    apply(case_tac bs; clarsimp) 
    apply(subgoal_tac "length list = nat") apply(clarsimp)
    apply(case_tac "length list = 31"; clarsimp)  done
next
  case (8 i j)
  then show ?case by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (9 t n l)
  then show ?case 
    apply(clarsimp)
    done
  next
  case (10 ts vs)
  then show ?case 
    apply(clarsimp)
    done
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
  then show ?case
    apply(clarsimp) apply(simp add:farray_value_valid_aux_def tuple_value_valid_aux_def)
    done
next
  case (15 v l)
  then show ?case
    apply(clarsimp)
    apply(rule_tac conjI)

    apply(thin_tac
"\<forall>(ts::abi_type list) code::8 word list.
       (case those_err (map encode_static l) of Inl (bs::8 word list list) \<Rightarrow> Ok (concat bs) | Inr (x::char list) \<Rightarrow> Err x) = Ok code \<longrightarrow>
       list_all abi_type_valid ts \<and> tuple_value_valid_aux ts l \<and> list_all abi_value_valid_aux l \<longrightarrow> foldl (+) (0::int) (map abi_static_size ts) = int (length code)"
)
     apply(clarsimp)
     apply(drule_tac x = t in spec) apply(clarsimp)
     apply(case_tac n; clarsimp)
      apply(simp add:farray_value_valid_aux_def)
     apply(simp add:farray_value_valid_aux_def)
    apply(clarsimp)
    apply(case_tac "encode_static v"; clarsimp)
     apply(simp split:sum.splits)
     apply(clarsimp)
    apply(simp add:int_distrib)

    (* tuple *)
    apply(thin_tac "\<forall>(t::abi_type) (n::nat) code::8 word list.
       (case those_err (map encode_static l) of Inl (bs::8 word list list) \<Rightarrow> Ok (concat bs) | Inr (x::char list) \<Rightarrow> Err x) = Ok code \<longrightarrow>
       abi_type_valid t \<and> farray_value_valid_aux t n l \<and> list_all abi_value_valid_aux l \<longrightarrow> int n * abi_static_size t = int (length code)")

     apply(clarsimp)
     apply(case_tac ts; clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
     apply(simp add:tuple_value_valid_aux_def)

     apply(case_tac " those_err (encode_static v # map encode_static l) "; clarsimp)
    apply(case_tac "encode_static v"; clarsimp)
     apply(case_tac "those_err (map encode_static l)"; clarsimp)
    apply(cut_tac f = "(+)"
and a = "0 :: int"
and x = "abi_static_size (abi_get_type v)"
and xs = "(map (abi_static_size \<circ> abi_get_type) l)" in foldl_Cons)
     apply(rotate_tac -1)
    apply(drule_tac sym)
    apply(clarsimp)
    apply(cut_tac
x = "int (length a)"
and i = "0"
and xs = "(map (abi_static_size \<circ> abi_get_type) l)"
in foldl_plus)
    apply(simp)
    done

qed

lemma encode_static_size :
"encode_static v = Ok code \<Longrightarrow>
     abi_value_valid v \<Longrightarrow>
     abi_static_size (abi_get_type v) = length code"
  apply(cut_tac encode_static_size')
  apply(auto)
  done

(*
  "encode v = Ok code \<Longrightarrow> encode v = Ok code \<Longrightarrow> can_encode_as v code _ _" (done)

--------

  "is_canonical code \<Longrightarrow> can_encode_as v code _ _ \<Longrightarrow> encode v = Ok code" (next)

  "encode v = Err _ \<Longrightarrow> can_encode_as v code \<Longrightarrow> False" (my version)

  "can_encode_as v code \<Longrightarrow> (\<exists> code' . encode v = Ok code')" (daniel's version - more intuitive)

  (another option - claim about valid values - that can_encode_as and encode both hold (for some code)
   for v iff v is valid) (probably best option of all)
  "abi_value_valid v = \<exists> code . can_encode_as v code"
  "abi_value_valid v = \<exists> code . encode v = Ok code"

---------

  "can_encode_as v code \<Longrightarrow> decode code = Ok v"

  "decode code = Ok v \<Longrightarrow> can_encode_as v code"

*)
lemma encode_tuple_heads_headslength [rule_format]:
  "\<forall> a aa b . encode'_tuple_heads l a = Ok (aa, b) \<longrightarrow>
      list_all abi_value_valid l \<longrightarrow>
      length aa = heads_length l"
proof(induction l)
  case Nil
  then show ?case 
    apply(clarify)
    apply(case_tac a; auto)
    done
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac aa; auto)
    apply(simp split:if_split_asm sum.splits)
     apply(clarsimp)
     apply(drule_tac x = list in spec) apply(drule_tac x = aa in spec) apply(clarsimp)
     apply(drule_tac encode_static_size) apply(simp) apply(simp)

    apply(case_tac x1) apply(clarsimp) 
    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(simp add:word_rsplit_def)
    apply(simp add: bin_rsplit_len)
    done
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

lemma abi_encode_succeed_gen_new :
  "(\<forall>  code pre post . encode v = Ok code \<longrightarrow>
          (can_encode_as v (pre @ code @ post) (int (length pre))))"

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
proof(induction v )
case (Vuint n i)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vsint n i)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vaddr x)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vbool b)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vfixed m n r)
  then show ?case
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vufixed m n r)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vfbytes n bs)
  then show ?case 
    apply(clarify)
    apply(rule_tac Estatic)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (Vfunction i j)
  then show ?case
    apply(clarify)
    (* function case currently unimplimented - this is a bug. *)
    sorry
next
  case (Vfarray t n l)
  then show ?case
  proof(cases "abi_type_isstatic t")
    case True
    then show ?thesis using Vfarray
      apply(clarsimp)
      apply(rule_tac Estatic)
        apply(simp)
       apply(simp add:encode_def split:if_split_asm)
      apply(simp add:encode_def split:if_split_asm)
      done
  next
    case False
    then show ?thesis using Vfarray
      apply(clarsimp)
(*      apply(thin_tac "\<forall>t n code.
          encode (Vfarray t n l) = Ok code \<longrightarrow>
          (\<forall>pre post v'. v' \<in> set l \<longrightarrow> encode v' = Ok code \<longrightarrow> can_encode_as v' (pre @ code @ post) (int (length pre))) ") *)
      apply(simp add:encode_def)
      apply(case_tac " abi_type_valid t \<and> farray_value_valid_aux t n l \<and> list_all abi_value_valid_aux l"; clarsimp)
      apply(case_tac " encode'_tuple_tails l 0 (heads_length l) "; clarsimp)
      apply(case_tac "encode'_tuple_heads l a"; clarsimp)

(*headlen len_total bvs vbvs hds tls *)
      apply(frule_tac 
vbvs = "(List.zip l a)"
and
hds= "List.map (\<lambda> (v, (ptr, enc)) .
                        (if (abi_type_isstatic (abi_get_type v)) then v
                            else (Vuint 256 ptr))) (List.zip l a)"
and
tls = " List.map (\<lambda> (v, (ptr, enc)) . (ptr, v))
                    (List.filter (abi_type_isdynamic o abi_get_type o fst) (List.zip l a)) 
 "
in
encode_tuple_tails_correct)
         apply(simp)
      apply(simp) apply(simp)
      apply(rule_tac vs = l in Efarray_dyn)
        apply(simp)
         apply(simp)
        apply(simp)
       apply(simp)

       apply(cut_tac
v = "(Vtuple (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l)
          (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) l a))"
and
 pre = "pre" and code = "aa" and post = "b@post" in Estatic)
         apply(clarsimp)
         apply(simp add:list_ex_iff)
         apply(clarsimp) apply(fastforce)

        apply(clarsimp)

      apply(simp add:tuple_value_valid_aux_def farray_value_valid_aux_def) apply(clarsimp)
         apply(rule_tac conjI)
         apply(simp add:list_all_iff)
         apply(rule_tac conjI)

      apply(subgoal_tac
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l =
 map (\<lambda> (v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip l a)")
           apply(clarsimp)
          apply(rule_tac map2_map_fst') apply(simp add:encode_tuple_tails_len)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(rule_tac conjI) apply(clarsimp)
          apply(drule_tac set_zip_leftD) apply(clarsimp)
apply(frule_tac set_zip_leftD) apply(clarsimp)
         apply(drule_tac x = ab in bspec) apply(clarsimp)
(*apply(drule_tac set_zip_rightD)*)
         apply(frule_tac v = ab and offset = ac and enc = ba in encode'_tuple_tails_correct_overflow) apply(clarsimp) apply(simp) apply(simp)

        apply(rule_tac encode_tuple_heads_correct1; simp)
         apply(simp add:list_all_iff) apply(simp add:farray_value_valid_aux_def)
         apply(rule_tac conjI) apply(clarsimp) 
          apply(auto) (*TODO: something saner here *)
           apply(simp add:list_all_iff)

          apply(simp add:tuple_value_valid_aux_def) 
      apply(subgoal_tac
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l =
 map (\<lambda> (v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip l a)")
           apply(clarsimp)
          apply(rule_tac map2_map_fst') apply(simp add:encode_tuple_tails_len)

         apply(drule_tac set_zip_leftD) apply(simp)
        apply(frule_tac set_zip_leftD)
(* apply(drule_tac set_zip_rightD) *)
         apply(frule_tac v = ab and offset = ac and enc = ba in encode'_tuple_tails_correct_overflow)  apply(clarsimp) apply(simp) apply(simp)

       apply(simp add:list_ex_iff) apply(clarsimp) apply(fastforce)

      apply(frule_tac heads_length = "length aa"
              and ac = "ac" and ab = "ab" in encode_tuple_heads_correct2)
              apply(auto)
           defer (* this should be another easy lemma *)
           apply(simp add:farray_value_valid_aux_def) apply(clarsimp)
           apply(simp add:list_all_iff)

          apply(simp add:tuple_value_valid_aux_def farray_value_valid_aux_def)
          apply(clarsimp) 

      apply(subgoal_tac
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) l =
 map (\<lambda> (v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip l a)")
           apply(clarsimp) 
          apply(rule_tac map2_map_fst') apply(simp add:encode_tuple_tails_len)

         apply(simp add:list_all_iff) apply(clarsimp)
          apply(simp add:tuple_value_valid_aux_def farray_value_valid_aux_def)

         apply(rule_tac conjI) apply(clarsimp)
          apply(frule_tac x = ad in set_zip_leftD)
          apply(drule_tac x = ad in bspec) apply(clarsimp)
      apply(simp) apply(clarsimp)
         apply(frule_tac v = ad and offset = ae and enc = bb in encode'_tuple_tails_correct_overflow) apply(clarsimp) apply(clarsimp)
      apply(simp)
      apply(simp add:list_all_iff)

      apply(cut_tac
f =  "(\<lambda>x::abi_value \<times> int \<times> 8 word list. case x of (v::abi_value, ptr::int, enc::8 word list) \<Rightarrow> (ptr, v))"
and x = "(ab, ac, ba)" in Set.imageI) apply(simp) apply(simp)
        apply(force)

       apply(atomize)

       apply(simp add:list_all_iff)
       apply(drule_tac x = ab in spec)  apply(frule_tac set_zip_leftD) apply(simp)
       apply(rotate_tac -1)
       apply(drule_tac x = ab_code in spec)
       apply(simp split:if_split_asm)
        apply(rotate_tac -1)
        apply(drule_tac x = "pre @ aa @ prea" in spec)
      apply(rotate_tac -1)
        apply(drule_tac x = "posta @ post" in spec) apply(clarsimp) 
      apply(subgoal_tac
"int (length pre) + (int (length aa) + int (length prea)) =
(int (length aa) + int (length prea) + int (length pre))")
         apply(clarsimp)
      apply(simp)

       apply(simp add:farray_value_valid_aux_def) apply(clarsimp)
      apply(simp add: list_all_iff)

      apply(drule_tac encode_tuple_heads_headslength) apply(clarsimp)
       apply(simp add:farray_value_valid_aux_def)
       apply(simp add:list_all_iff)

      apply(simp)
      done
      
  qed
next
  case (Vtuple ts vs)
  then show ?case 
  proof(cases "abi_type_isstatic (Ttuple ts)")
    case True
    then show ?thesis
      apply(clarsimp)
      apply(rule_tac Estatic)
        apply(simp)
       apply(simp add:list_all_iff encode_def split:if_splits sum.splits prod.splits)
      apply(simp add:list_all_iff encode_def split:if_splits sum.splits prod.splits)
      done
  next
    case False
    then show ?thesis using Vtuple
      apply(clarsimp)
      apply(simp add:encode_def split:if_split_asm sum.split_asm prod.split_asm)
      apply(frule_tac encode_tuple_tails_correct) apply(simp) apply(simp) apply(simp)
apply(simp add:list_ex_iff) apply(clarsimp)
      apply(rule_tac t = x in Etuple_dyn)
           apply(simp) apply(clarsimp) apply(simp) apply(simp)

       apply(drule_tac encode_tuple_heads_correct1) apply(simp) apply(simp)

      apply(subgoal_tac
" (\<lambda>a::abi_value \<times> int \<times> 8 word list. abi_type_isdynamic (abi_get_type (fst a))) =
(abi_type_isdynamic \<circ> abi_get_type \<circ> fst)")
            apply(simp) apply(fastforce)

          apply(simp add:tuple_value_valid_aux_def)
          apply(rule_tac conjI)
           apply(simp add:list_all_iff) apply(clarsimp)
      apply(case_tac "xa \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})"; clarsimp)

          apply(rule_tac conjI) apply(clarsimp) 
      apply(subgoal_tac
" map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs =
 map (\<lambda>(v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)")
            apply(simp)
            apply(clarsimp) apply(rule_tac map2_map_fst')  apply(simp add:encode_tuple_tails_len)

          apply(simp add: list_all_iff) apply(clarsimp) apply(rule_tac conjI)
           apply(drule_tac set_zip_leftD) apply(clarsimp)
apply(frule_tac set_zip_leftD) apply(clarsimp)
         apply(drule_tac x = xa in bspec) apply(clarsimp)
          apply(frule_tac set_zip_rightD)
          apply(frule_tac v = a and offset = aa and enc = b in encode'_tuple_tails_correct_overflow) apply(clarsimp) apply(simp) apply(simp)

         apply(simp) apply(simp add:list_ex_iff) apply(clarsimp) apply(fastforce)

        apply(assumption)

       apply(simp split:sum.split_asm)
       apply(rule_tac Estatic) apply(simp)
         apply(simp add:list_ex_iff) apply(clarsimp) apply(fastforce)

        apply(simp add:tuple_value_valid_aux_def)
        apply(simp add:list_all_iff) apply(clarsimp)
        apply(rule_tac conjI) apply(clarsimp)
         apply(case_tac "x \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})"; clarsimp)

        apply(rule_tac conjI)
      apply(subgoal_tac
" map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs =
 map (\<lambda>(v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)")
            apply(simp)
          apply(clarsimp) apply(rule_tac map2_map_fst')  apply(simp add:encode_tuple_tails_len)

        apply(clarsimp)
        apply(rule_tac conjI)
         apply(clarsimp)
         apply(drule_tac set_zip_leftD) apply(clarsimp)
        apply(frule_tac set_zip_leftD)
        apply(frule_tac set_zip_rightD) apply(clarsimp)
        apply(simp add:encode'_tuple_tails_correct_overflow)

       apply(simp)

      apply(atomize)
      apply(frule_tac heads_length = "length x1b" and ac = "offset" and ab = "v"
in encode_tuple_heads_correct2)
              apply(simp)
             apply(simp)
      apply(subgoal_tac
"(\<lambda>a::abi_value \<times> int \<times> 8 word list. abi_type_isdynamic (abi_get_type (fst a)))
=
(abi_type_isdynamic \<circ> abi_get_type \<circ> fst)")
             apply(simp)
            apply(fastforce)
           apply(drule_tac encode_tuple_heads_headslength)
            apply(simp add:list_all_iff)
            apply(clarsimp)
            apply(simp add:tuple_value_valid_aux_def)

            apply(subgoal_tac "\<exists> vxa . (xa, vxa) \<in> set (zip vs ts)")
             apply(clarsimp)

            apply(clarsimp)
            apply(rule_tac xs = vs and ys = ts in in_set_impl_in_set_zip1) apply(simp)
             apply(simp) apply(rule_tac x = y in exI) apply(clarsimp)

           apply(clarsimp)
      apply(simp)
        apply(rule_tac conjI)
         apply(clarsimp)
           apply(simp add:list_all_iff)
           apply(clarsimp)
           apply(safe_step) apply(clarsimp)

      apply(simp add:tuple_value_valid_aux_def)
            apply(subgoal_tac "\<exists> vxb . (xb, vxb) \<in> set (zip vs ts)")
             apply(clarsimp)
            apply(clarsimp)
            apply(rule_tac xs = vs and ys = ts in in_set_impl_in_set_zip1) apply(simp)
             apply(simp) apply(rule_tac x = y in exI) apply(clarsimp)

      apply(simp add:tuple_value_valid_aux_def)
           apply(fastforce)

          apply(rule_tac conjI)
           apply(simp add:tuple_value_valid_aux_def)
           apply(subgoal_tac 
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs =
 map (\<lambda>(v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)")
            apply(clarsimp)
           apply(rule_tac map2_map_fst') apply(simp add: encode_tuple_tails_len)
           apply(simp add:list_all_iff)
          apply(clarsimp)
          apply(rule_tac conjI)
      apply(drule_tac x = ab and y ="(ac, ba)" in set_zip_leftD) 
           apply(rotate_tac 1) apply(drule_tac x = ab in bspec) apply(clarsimp) apply(simp)

          apply(frule_tac set_zip_rightD) apply(clarsimp)
          apply(simp add:encode'_tuple_tails_correct_overflow)

         apply(simp)
        apply(simp)

       apply(simp)
       apply(fastforce)

      apply(clarify)
      apply(drule_tac x = v in spec)
      apply(clarsimp)
      apply(frule_tac set_zip_leftD) apply(clarsimp)
      apply(drule_tac x = ab_code in spec)
      apply(simp split:if_split_asm)
       apply(drule_tac x = "pre @ x1b @ prea" in spec)
       apply(drule_tac x = "posta @ post" in spec)
       apply(clarsimp)
      apply(subgoal_tac
"(int (length pre) + (int (length x1b) + int (length prea)))
=
(int (length x1b) + int (length prea) + int (length pre))"
)
        apply(clarsimp)
       apply(arith)

      apply(simp add:tuple_value_valid_aux_def)
            apply(subgoal_tac "\<exists> va . (a, va) \<in> set (zip vs ts)")
      apply(clarsimp)
       apply(simp add: list_all_iff)

      apply(clarsimp)
            apply(rule_tac xs = vs and ys = ts in in_set_impl_in_set_zip1) apply(simp)
       apply(simp) apply(rule_tac x = y in exI) apply(clarsimp)
      done
  qed
next
  case (Vbytes bs)
  then show ?case
    apply(clarify)
    apply(cut_tac  l = bs and pre = pre and count = "word_rsplit (word_of_int (int (length bs)))"
and code = "drop 32 code"
and post = post in Ebytes)
       apply(simp add:bytes_value_valid_def encode_def) apply(simp split:if_splits)

      apply(simp add:encode_def) apply(simp add:bytes_value_valid_def)
    apply(simp split:if_splits)
    apply(simp split:prod.splits)
    apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length bs)) :: 256 word) :: 8 word list) = 32")
       apply(clarsimp)
      apply(simp add: word_rsplit_def)
       apply(simp add:bin_rsplit_len)
     apply(simp add:encode_def) apply(simp add:bytes_value_valid_def)
     apply(simp split:if_splits)
     apply(cut_tac
v = "(Vuint (256::nat) (int (length bs)))"
and pre = pre and code = "word_rsplit (word_of_int (int (length bs)) :: 256 word)" and post = "(drop 32 code) @ post" in Estatic)
        apply(simp) apply(simp add:bytes_value_valid_def)
      apply(simp)
     apply(simp)

    apply(simp add:encode_def)
    apply(simp add:bytes_value_valid_def split:if_splits prod.splits)
    apply(clarsimp)
    apply(case_tac x2; clarsimp)

    apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length bs)) :: 256 word) :: 8 word list) = 32")
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
     apply(simp add:bin_rsplit_len)

        apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length bs)) :: 256 word) :: 8 word list) = 32")
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
     apply(simp add:bin_rsplit_len)
    done

next
  case (Vstring s)
  then show ?case
    apply(clarsimp)
    apply(rule_tac l = "string_to_bytes s" in Estring)

      apply(simp add:encode_def string_value_valid_def split:if_splits)

     apply(simp)

      (* copy-pasted proof from Vbytes case, should fix *)
    apply(cut_tac  l = "string_to_bytes s" and pre = pre and count = "word_rsplit (word_of_int (int (length (string_to_bytes s))))"
and code = "drop 32 code"
and post = post in Ebytes)
       apply(simp add:string_value_valid_def bytes_value_valid_def encode_def) apply(simp split:if_splits)

      apply(simp add:encode_def) apply(simp add:string_value_valid_def)
    apply(simp split:if_splits)
      apply(simp split:prod.splits)
    apply(clarsimp)
        apply(case_tac x2; clarsimp)
    apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length (string_to_bytes s))) :: 256 word) :: 8 word list) = 32")
        apply(simp)
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
       apply(simp add:bin_rsplit_len)

      apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length (string_to_bytes s))) :: 256 word) :: 8 word list) = 32")
        apply(simp)
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
      apply(simp add:bin_rsplit_len)


     apply(cut_tac
v = "(Vuint (256::nat) (int (length (string_to_bytes s))))"
and pre = pre and code = "word_rsplit (word_of_int (int (length (string_to_bytes s))) :: 256 word)" and post = "(drop 32 code) @ post" in Estatic)
        apply(simp) apply(simp add:string_value_valid_def encode_def split:if_splits)

      apply(simp add: word_rsplit_def)
     apply(simp add:bin_rsplit_len)

    apply(simp)

    apply(simp add:encode_def string_value_valid_def split:if_splits prod.splits)
    apply(simp add:Let_def)
        apply(simp add:encode_def string_value_valid_def split:if_splits prod.splits)
    apply(subgoal_tac
"length (word_rsplit (word_of_int (int (length (string_to_bytes s))) :: 256 word) :: 8 word list) = 32")
        apply(simp)
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
    apply(simp add:bin_rsplit_len)
    done
next
  case (Varray t vs)
  then show ?case
    apply(clarsimp)
    apply(simp add:encode_def split:if_splits)
    apply(simp split:sum.split_asm prod.splits)
    apply(clarsimp)
    apply(frule_tac encode_tuple_tails_correct) apply(simp) apply(simp) apply(simp)


    apply(rule_tac
t = t
and vs = vs
and heads = " (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) vs x1)"
and head_types = "(map (\<lambda>v::abi_value. if abi_type_isstatic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs)"
and tails = "(map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs x1)))"
and full_code = "(pre @ word_rsplit (word_of_int (int (length vs))) @ x1b @ x2 @ post)"
and start = "int (length (pre))"
in
Earray)

        apply(simp) apply(simp)
        apply(rule_tac Estatic; simp)
        apply(simp add:uint_value_valid_def array_value_valid_aux_def)

       apply(drule_tac encode_tuple_heads_correct1; simp)

         apply(simp add:array_value_valid_aux_def tuple_value_valid_aux_def)
         apply(rule_tac conjI) apply(clarsimp)
    apply(simp add:list_all_iff)

       apply(rule_tac conjI) apply(clarsimp)
      apply(subgoal_tac
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs  =
 map (\<lambda> (v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)")
           apply(clarsimp)
          apply(rule_tac map2_map_fst') apply(simp add:encode_tuple_tails_len)

                 apply(simp add:list_all_iff) apply(clarsimp)
         apply(rule_tac conjI) apply(clarsimp)
          apply(drule_tac set_zip_leftD) apply(clarsimp)
apply(frule_tac set_zip_leftD) apply(clarsimp)
         apply(drule_tac x = a in bspec) apply(clarsimp)
apply(frule_tac set_zip_rightD)
         apply(frule_tac v = a and offset = aa and enc = b in encode'_tuple_tails_correct_overflow) apply(clarsimp) apply(simp)

        apply(clarsimp)
         apply(simp add:list_ex_iff) apply(clarsimp)
        apply(case_tac "x \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})") apply(clarsimp)
        apply(clarsimp)

       apply(cut_tac
v = "(Vtuple (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs)
          (map2 (\<lambda>(v::abi_value) (ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr) vs x1))"
and
 pre = "pre @ word_rsplit (word_of_int (int (length vs)))" and code = "x1b" and post = "x2@post" in Estatic)
    apply(clarsimp)
          apply(simp add:list_all_iff list_ex_iff)
          apply(clarsimp)
        apply(case_tac "x \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})") apply(clarsimp)
        apply(clarsimp)

    apply(clarsimp) apply(simp add:list_all_iff)

         apply(rule_tac conjI) apply(clarsimp) 
          apply(case_tac " x \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})") 
    apply(clarsimp)
         apply(simp add:array_value_valid_aux_def) apply(clarsimp)
         apply(simp add:list_all_iff)

    apply(case_tac
"x \<in> abi_get_type ` (set vs \<inter> {v::abi_value. \<not> abi_type_isdynamic (abi_get_type v)})"
; clarsimp)

       apply(rule_tac conjI)   
    apply(simp add:tuple_value_valid_aux_def)
      apply(subgoal_tac
"map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs  =
 map (\<lambda> (v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)")
         apply(clarsimp)
    apply(rule_tac map2_map_fst')
 apply(simp add:encode_tuple_tails_len)

       apply(clarsimp)
    apply(rule_tac conjI) apply(clarsimp)

       apply(drule_tac set_zip_leftD) apply(clarsimp)

      apply(frule_tac set_zip_leftD) 
      apply(frule_tac set_zip_rightD) apply(clarsimp)
      apply(frule_tac v = a and  offset = aa and enc = b in  encode'_tuple_tails_correct_overflow)
       apply(simp) apply(simp add:array_value_valid_aux_def)  apply(clarsimp) apply(simp add:list_all_iff)


    apply(subgoal_tac
" (int (length pre) + (32::int))
=
 (int (length (pre @ word_rsplit (word_of_int (int (length vs)) :: 256 word) :: 8 word list)))
")
    apply(rotate_tac -1)
    apply(cut_tac
P =
"(\<lambda> target . 
can_encode_as
        (Vtuple (map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs)
          (map2 (\<lambda>(x::abi_value) y::int \<times> 8 word list. case y of (ptr::int, enc::8 word list) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type x) then x else Vuint (256::nat) ptr) vs x1))
        ((pre @ word_rsplit (word_of_int (int (length vs)))) @ x1b @ x2 @ post) (target))"
and
t = "(int (length pre) + (32::int))" and s = "int (length (pre @ word_rsplit (word_of_int (int (length vs)) :: 256 word) :: 8 word list))"  in subst
)
        apply(simp) 
      (* this is unbelievably confusing *)
       apply(assumption) apply(simp)

     apply(clarsimp)
      apply(simp add: word_rsplit_def)
       apply(simp add:bin_rsplit_len)

(* tail *)
    apply(simp add:array_value_valid_aux_def)
(*
    apply(drule_tac x = v in spec) apply(clarsimp)
    apply(frule_tac set_zip_leftD) apply(simp)
    apply(drule_tac x = b in spec)
*)
    
    apply(frule_tac
      heads_length = "length x1b"
      and bvs = "x1"
and ac = offset
and ab = v
and heads_code = "x1b" and tails_code = "x2" in
 encode_tuple_heads_correct2)
            apply(simp)
           apply(simp) apply(simp)
         apply(simp)
         apply(frule_tac encode_tuple_heads_headslength) 
    apply(simp add:list_all_iff)
         apply(simp) apply(simp)
        apply(simp add:list_all_iff)
        apply(rule_tac conjI)
         apply(simp add:tuple_value_valid_aux_def)
    apply(subgoal_tac
" map (abi_get_type \<circ> (\<lambda>(v::abi_value, ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr)) (zip vs x1) =
       map (\<lambda>(v, _). if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) (zip vs x1)
") 
    apply(rule_tac t = 
" map (abi_get_type \<circ> (\<lambda>(v::abi_value, ptr::int, enc::8 word list). if \<not> abi_type_isdynamic (abi_get_type v) then v else Vuint (256::nat) ptr)) (zip vs x1)"
and s =
" map2 (\<lambda>(v::abi_value) _::int \<times> 8 word list. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs x1"
and P =
"(\<lambda> lhs . lhs = map (\<lambda>v::abi_value. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tuint (256::nat)) vs)"
in subst) apply(simp)
          apply(simp)
    apply(rule_tac sym)
          apply(rule_tac map2_map_fst')
          apply(simp add:encode_tuple_tails_len)
         apply(simp)

         apply(clarsimp)
        apply(clarsimp)
        apply(rule_tac conjI)
    apply(rotate_tac -1)
         apply(drule_tac set_zip_leftD) apply(simp add:list_all_iff)
    apply(rotate_tac -1)
        apply(frule_tac set_zip_rightD)
        apply(simp add: encode'_tuple_tails_correct_overflow) apply(simp)
      apply(clarsimp)
     apply(simp add:List.image_set) apply(clarsimp)

    apply(clarsimp)
    apply(atomize)
    apply(drule_tac x = a in spec)
    apply(frule_tac set_zip_leftD; clarsimp)
    apply(drule_tac x = ab_code in spec)
    apply(simp split:if_split_asm)
     apply(drule_tac x = "pre @ word_rsplit (word_of_int (int (length vs))) @ x1b @ prea" in spec)
     apply(drule_tac x = "posta @ post" in spec) apply(clarsimp)

    apply(subgoal_tac 
"(int (length pre) + (int (length (word_rsplit (word_of_int (int (length vs))))) + (int (length x1b) + int (length prea)))) =
int (length x1b) + int (length prea) + int (length pre) + (32::int)")
    apply(cut_tac 
P = "(\<lambda> i .  can_encode_as a (pre @ word_rsplit (word_of_int (int (length vs))) @ x1b @ prea @ ab_code @ posta @ post) i)"
and s = "(int (length pre) + (int (length (word_rsplit (word_of_int (int (length vs))))) + (int (length x1b) + int (length prea))))"
and t = "int (length x1b) + int (length prea) + int (length pre) + (32::int)"
in HOL.subst) apply(simp) apply(assumption)
    apply(assumption)
     apply(clarsimp)
      apply(simp add: word_rsplit_def)
     apply(simp add:bin_rsplit_len)

    apply(drule_tac set_zip_leftD; clarsimp)
    apply(simp add:list_all_iff)
    done
qed

lemma encode_tuple_heads_fail [rule_format]:
  "\<forall> bss err.
    encode'_tuple_heads vs bss = Err err \<longrightarrow>
    length vs = length bss \<longrightarrow>
    (\<exists> v err' . v \<in> set vs \<and> encode' v = Err err')"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(clarsimp)
    apply(case_tac bss; clarsimp)
    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(case_tac "abi_type_isdynamic (abi_get_type a)"; clarsimp)
     apply(simp split:if_split_asm sum.split_asm prod.splits)

     apply(clarsimp)
     apply(case_tac "abi_type_isdynamic (abi_get_type v)"; clarsimp)
      apply(rule_tac x = v in exI) apply(clarsimp)
     apply(rule_tac x = v in exI) apply(clarsimp)

    apply(case_tac "encode_static a"; clarsimp)
    apply(case_tac "encode'_tuple_heads vs list"; clarsimp)
     apply(rule_tac x = v in exI) apply(clarsimp)
     apply(rule_tac conjI) apply(clarsimp)
     apply(clarsimp)

     apply(rule_tac x = a in exI) apply(clarsimp)
    done
qed

(* induction on is_head_and_tail? *)
(*
lemma encode_tuple_tails_overflow_fail [rule_format]:
  "\<forall> vs headlen len_total err v .
     encode'_tuple_tails (vs) headlen len_total = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> v . v \<in> set vs \<and> 
     "
  sorry
*)

(* the problem here is that our spec doesn't care if we can't encode
   (empty) offsets for heads that are too big. but our implementation does *)
(* need to generalize for different arguments of encode_tuple_tails *)


(* lemma for tails will be similar, but we also need to take into
   account the possibility that the encoding fails because the
   length is too large *)


lemma is_head_and_tail_vs_elem [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> x . x \<in> set xs \<longrightarrow>
 abi_type_isdynamic (abi_get_type x) \<longrightarrow>
   (\<exists> offset . (offset, x) \<in> set tails \<and>
      (Vuint 256 offset \<in> set ys)))"
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case by auto
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case by auto
qed


(*
lemma is_head_and_tail_elem' [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> t . t \<in> set ts \<longrightarrow>
 abi_type_isdynamic t \<longrightarrow>
   (\<exists> offset x. (offset, x) \<in> set tails \<and>
      x \<in> set xs \<and>
      abi_get_type x = t))"
  sorry
*)
lemma is_head_and_tail_tails_elem [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> offset x . (offset, x) \<in> set tails \<longrightarrow>
 (abi_type_isdynamic (abi_get_type x)  \<and> 
  Vuint 256 offset \<in> set ys \<and>
      x \<in> set xs))"
proof(induction rule:is_head_and_tail.induct; auto)
qed

(*
lemma is_head_and_tail_elem''' [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> y . y  \<in> set ys \<longrightarrow>
    (abi_type_isstatic (abi_get_type y)))"
  sorry
*)

(*
lemma encode_tuple_tails_shift [rule_format]:
  "\<forall> headlen len_total x bss .
    encode'_tuple_tails vs headlen len_total = Ok bss \<longrightarrow>
    encode'_tuple_tails vs headlen (len_total + x) = Ok (map (\<lambda> (offset, bs) . (offset + x, bs)) bss)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
    apply(clarify)
    apply(simp only:encode'_tuple_tails.simps)
    apply(case_tac "abi_type_isstatic (abi_get_type a) ") apply(clarsimp)
    apply(clarsimp)
qed
*)

(*
lemma encode_tuple_tails_overflow_fail' [rule_format]:
  "
     (\<forall> err vs1 vs2 code .
      vs = vs1 @vs2 \<longrightarrow>
     encode'_tuple_tails vs1 0 (heads_length vs) = Ok code \<longrightarrow>
     encode'_tuple_tails (vs2) 0 (foldr (+) (map (\<lambda> (offset, code') . int (length (code'))) code) (heads_length vs) ) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> offset v . (offset, v) \<in> set tls \<and>
     \<not> (uint_value_valid 256 offset)))
     "
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(
qed
*)

(* generalization: compare to heads_length vs, subtract
   this formulation isn't quite right because it doesn't
   invoke heads_length *)
(*
lemma encode_tuple_tails_overflow_fail' [rule_format] :
"
     is_head_and_tail vs hds bvs tls \<Longrightarrow>
     (\<forall> err headlen .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> offset v . (offset - headlen, v) \<in> set tls \<and> offset > headlen \<and>
     \<not> (uint_value_valid 256 (offset - headlen))))
     "
*)
(*

  case iht_nil
  then show ?case
    apply(clarsimp)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case 
    apply(clarsimp)
    apply(simp split:if_splits sum.splits)
    done
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarsimp)
    apply(simp split:if_splits sum.splits)
      apply(frule_tac encode_tuple_tails_correct)
         apply(simp)
        apply(simp)
       apply(simp)

      defer



      apply(clarsimp)
      apply(drule_tac x = err in spec)
    apply(drule_tac x = "headlen + int (length (x1))" in spec)
      apply(clarsimp)
      apply(rule_tac x = "offset - ( int (length (x1)))" in exI)
      apply(clarsimp)
      apply(rule_tac conjI)
       apply(rule_tac x = v in exI)
       apply(clarsimp) 
       apply(subgoal_tac "offset - (headlen + int (length x1)) = offset - int (length x1) - headlen") apply(clarsimp)
       apply(arith)
      apply(clarsimp)
       apply(subgoal_tac "offset - (headlen + int (length x1)) = offset - int (length x1) - headlen") apply(clarsimp)
       apply(arith)

     apply(clarsimp)

    apply(drule_tac x = x in spec) apply(clarsimp)

  (* deferred goal *)

    apply(case_tac x; clarsimp)
    apply(simp split:sum.splits prod.splits)
    
(* need lemma about determinism of is_head_and_tail *)
    apply(clarsimp)
    apply(frule_tac encode'_tuple_tails_correct_overflow)
    apply(rule_tac x = "ptr + headlen" in exI) apply(clarsimp)
    apply(rule_tac conjI) apply(rule_tac x = x in exI) apply(clarsimp)
    apply(subgoal_tac
"(map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip xs x1a)))
=
tails")

    apply(clarsimp)
    sorry
qed
*)

lemma encode_static_correct_converse [rule_format] :
  "can_encode_as v full_code start \<Longrightarrow>
    (\<forall> pre code post . full_code = pre @ code @ post \<longrightarrow>
       start = length pre \<longrightarrow>
     abi_type_isstatic (abi_get_type v) \<longrightarrow>
       abi_static_size (abi_get_type v) = length code \<longrightarrow>
     (abi_value_valid v \<and> encode_static v = Ok code))"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case 
    apply(clarsimp)
    apply(frule_tac encode_static_size)
     apply(simp)
    apply(simp)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def)
    apply(simp add:list_ex_iff)
    done
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    done
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    done
next
  case (Ebytes l pre post count code)
  then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed

lemma encode_correct_converse_valid [rule_format] :
  "can_encode_as v full_code start \<Longrightarrow>
     (abi_value_valid v)"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case by auto
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case by auto
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Ebytes l pre post count code)
  then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed


(*
lemma abi_dynamic_size_bound_correct [rule_format] :
"
(\<forall> bound code . encode v = Ok code \<longrightarrow>
    abi_dynamic_size_bound v = bound \<longrightarrow>           
            abi_value_valid v \<longrightarrow>
            length code \<le> bound)
"  
  sorry
*)
(*
lemma can_encode_as_inv_static [rule_format] :
  "abi_type_isstatic (abi_get_type v) \<longrightarrow>
   can_encode_as v full_code l \<longrightarrow>
   (\<exists> 
*)

definition list_nonneg :: "int list \<Rightarrow> bool" where
"list_nonneg l = list_all (\<lambda> x . 0 \<le> x) l"

lemma list_nonneg_sum [rule_format]:
  " list_nonneg l \<longrightarrow>
         0 \<le> list_sum l"
proof(induction l)
  case Nil
  then show ?case 
    apply(simp add: list_nonneg_def list_sum_def)
    done
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(simp add:list_nonneg_def list_sum_def) apply(clarsimp)
    apply(cut_tac x = a and i = 0 and xs = l in foldl_plus) apply(clarsimp)
    done
qed


lemma elem_lt_list_sum [rule_format] :
  "\<forall> x . x \<in> set l \<longrightarrow>
     list_nonneg l \<longrightarrow>
      x \<le> list_sum l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp) apply(simp add:list_sum_def list_nonneg_def)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(cut_tac l = l in list_nonneg_sum) apply(simp add:list_nonneg_def)
     apply(simp add:list_sum_def)
     apply(cut_tac i = 0 and x = a and xs = l in foldl_plus) apply(clarsimp)

    apply(clarsimp)
     apply(cut_tac l = l in list_nonneg_sum) apply(simp add:list_nonneg_def)
     apply(simp add:list_sum_def)
    apply(cut_tac i = 0 and x = a and xs = l in foldl_plus) apply(clarsimp)
    apply(drule_tac x = x in spec) apply(clarsimp)
    done
qed

lemma abi_static_size_nonneg :
  "0 \<le> abi_static_size v"
  apply(induction v; clarsimp)
  apply(atomize)
  apply(cut_tac l = "map abi_static_size x" in list_nonneg_sum)
   apply(simp add:list_nonneg_def) apply(simp add:list_all_iff)

  apply(simp add:list_sum_def)
  done

lemma abi_dynamic_size_bound_nonneg :
  "0 \<le> abi_dynamic_size_bound v"
  apply(induction v; clarsimp)

  (* farray *)
    apply(atomize)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(simp add: abi_static_size_nonneg)
    apply(clarsimp)

    apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x3a)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x3a \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)

(* tuple *)
    apply(atomize)
    apply(rule_tac conjI)
    apply(clarsimp)
  apply(cut_tac l = "map abi_static_size x1" in list_nonneg_sum)
  apply(simp add:list_nonneg_def)
  apply(simp add:list_all_iff)
    apply(simp add: abi_static_size_nonneg)
    apply(simp add:list_sum_def)

  apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x2)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x2 \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)

(* array *)
      apply(atomize)
  apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x2)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x2 \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
  apply(drule_tac x = xa in spec) apply(clarsimp)
  done

lemma zero_leq_nat:
  "0 \<le> int (n :: nat)"
proof(induction n; auto)
qed

lemma oneplus_times :
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow>
  (1 + a :: int) * (b :: int) =
   b + a * b"
  apply(simp add:int_distrib)
  done

(*

     is_head_and_tail vs hds bvs tls \<Longrightarrow>
     (\<forall> err headlen .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> offset v . (offset - headlen, v) \<in> set tls \<and> offset > headlen \<and>
     \<not> (uint_value_valid 256 (offset - headlen))))
     "

*)

lemma encode_tuple_tails_overflow_fail_farray' [rule_format] :
"
     (\<forall> err headlen   .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     heads_length vs \<le> headlen \<longrightarrow>
     \<not> uint_value_valid 256 (int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs)))
     "
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case

    apply(clarify)
    apply(simp only:encode'_tuple_tails.simps)
    apply(case_tac " abi_type_isstatic (abi_get_type a)") 
    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
           
     apply(rotate_tac -2)
     apply(drule_tac x = err in spec) apply(drule_tac x = headlen in spec)
    apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
     apply(simp only:uint_value_valid_def)
     apply(subgoal_tac "heads_length vs \<le> headlen") apply(simp only:) apply(clarify)
      apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac l = "(abi_dynamic_size_bound a # map abi_dynamic_size_bound vs)" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
    apply(rule_tac conjI)
        apply(rule_tac abi_dynamic_size_bound_nonneg)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
        apply(rule_tac abi_dynamic_size_bound_nonneg)

      apply(subgoal_tac " (0::int) \<le> int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs)")
       apply(clarify)

       apply(simp add:list_sum_def  del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
       apply(arith)

      apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(clarsimp)

     apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
     apply(arith)

    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
      apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)


       apply(simp add: list_sum_def del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
       apply(arith)

    apply(subgoal_tac
"(0::int) \<le> int (length vs) * (32::int) + foldl (+) (0::int) (map abi_dynamic_size_bound vs)"
)
    apply(simp)
           apply(simp add:farray_value_valid_aux_def list_sum_def)
    apply(case_tac a; clarsimp)
(* old proof was wrong i guess *)
(*
    apply(clarify)
    apply(clarsimp)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(rule_tac conjI)
      apply(clarsimp)
      apply(simp split:sum.splits) apply(clarsimp)
      apply(drule_tac x = err in spec)
      apply(drule_tac x = headlen in spec)
      apply(clarsimp)
      apply(subgoal_tac "heads_length vs \<le> headlen")
       apply(clarsimp)
       apply(simp add:farray_value_valid_aux_def)
       apply(drule_tac x = t in spec) apply(clarsimp)
       apply(simp add:uint_value_valid_def)
       apply(clarsimp)
       apply(rule_tac conjI)
        apply(drule_tac
c = "abi_static_size (abi_get_type a)" in
ordered_ab_semigroup_add_class.add_right_mono)
        apply(simp)
        apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
        apply(clarsimp)
    apply(cut_tac n = "length vs" in zero_leq_nat)
        apply(subgoal_tac "((1::int) + int (length vs)) * abi_static_size (abi_get_type a) \<ge> 0")
         apply(arith)
        apply(simp add:left_diff_distrib)
       apply(simp add:int_distrib)
      apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
      apply(clarsimp)

(*apply (smt left_diff_distrib mult_cancel_right2) *)
    apply(clarsimp)
     apply(simp split:sum.splits prod.splits)
     apply(clarsimp)
      apply(drule_tac x = err in spec)
     apply(drule_tac x = headlen in spec)
     apply(clarsimp)
      apply(subgoal_tac "heads_length vs \<le> headlen")
       apply(clarsimp)
      apply(simp add:farray_value_valid_aux_def)
      apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
      apply(clarsimp)


    apply(clarsimp)
    apply(rule_tac conjI)
     apply(simp add:farray_value_valid_aux_def)

    apply(clarsimp)
    apply(simp split:sum.splits prod.splits if_splits)

    apply(case_tac a; clarsimp)
      apply(frule_tac encode_tuple_tails_correct; simp)
*)
qed


lemma encode_correct_converse [rule_format] :
  "\<forall> code start . 
      can_encode_as v code start \<longrightarrow>
      abi_dynamic_size_bound v \<le> (2^256) \<longrightarrow>
  (\<exists> code' . encode v = Ok code')"
proof(induction v)
case (Vuint x1 x2)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vsint x1 x2)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vaddr x)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vbool x)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfixed x1 x2 x3a)
  then show ?case

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vufixed x1 x2 x3a)
  then show ?case

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfbytes x1 x2)
  then show ?case 

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfunction x1 x2)
  then show ?case sorry
next
  case (Vfarray x1 x2 x3a)
  then show ?case
    apply(atomize)
    apply(clarify)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    apply(simp add: farray_value_valid_aux_def) apply(clarsimp)
    apply(simp split:sum.splits)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(frule_tac encode_tuple_heads_fail)
    apply(simp add:encode_tuple_tails_len)
     apply(clarsimp)
     apply(frule_tac x = v in is_head_and_tail_vs_elem) apply(simp)

      apply(subgoal_tac "abi_type_isdynamic (abi_get_type v)")
       apply(clarsimp)
      defer

      apply(subgoal_tac "abi_type_isdynamic (abi_get_type v)")
       apply(clarsimp)
    

    apply(drule_tac x = v in spec)
      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
       apply(clarsimp)
    apply(case_tac
"(case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l)
        | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs) | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs)
        | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s) | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))
       \<le> (115792089237316195423570985008687907853269984665640564039457584007913129639936::int)")        apply(clarsimp)

    apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v") apply(clarsimp)
    apply(clarsimp)
        apply(clarsimp)

        apply(cut_tac v = "Vfarray x1 x2 x3a" in abi_dynamic_size_bound_nonneg)
        apply(simp)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x3a)" in elem_lt_list_sum)
          apply(clarsimp)
         apply(simp add:list_nonneg_def)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)

        apply(simp)

       apply(atomize)
    apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x= v in spec)
       apply(clarsimp)
       apply(fastforce)

      apply(simp add:list_all_iff)

   apply(clarsimp)
     apply(frule_tac encode_tuple_tails_overflow_fail') apply(simp)

    defer (* hopefully easy *)
      apply(simp)
    apply(clarsimp)

      apply(atomize)
(* at this point, the intuition is that the offset can't encode as a u256 *)
      apply(frule_tac offset = "offset - heads_length x3a" and x = v in is_head_and_tail_tails_elem)  
       apply(clarsimp)
      apply(clarsimp)

      apply(drule_tac can_encode_as.cases; simp)
       apply(clarsimp)
       apply(simp add:list_all_iff)
    apply(rotate_tac -1)
       apply(drule_tac x = "Vuint (256::nat) (offset - heads_length x3a)" in bspec)
        apply(clarsimp)
       apply(simp)

    apply(clarsimp)
      apply(simp add:list_all_iff)
    apply(rotate_tac -1)
           apply(drule_tac x = "Vuint (256::nat) (offset - heads_length x3a)" in bspec)
        apply(clarsimp)
       apply(simp)

      apply(simp add:list_all_iff)

    apply(drule_tac x = v in spec) apply(clarsimp)
    apply(atomize)
    apply(drule_tac x = v in is_head_and_tail_vs_elem) apply(clarsimp)
     apply(clarsimp) apply(clarsimp)
    apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec)
    apply(clarsimp)

    apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
     apply(clarsimp)

(* need to talk about how length of full encoding works out implies length of sub encoding
also does *)

    apply(subgoal_tac "(case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l)
        | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs) | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs)
        | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s) | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))
       \<le> (115792089237316195423570985008687907853269984665640564039457584007913129639936::int)")
      apply(clarsimp)

    apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v") apply(clarsimp)
      apply(clarsimp)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x3a)" in elem_lt_list_sum)
       apply(clarsimp) apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff) apply(clarsimp)
      apply(rotate_tac 1)

         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)

     apply(simp)
    apply(rule_tac x = full_code in exI) apply(fastforce)

    done
next
  case (Vtuple x1 x2)
  then show ?case sorry
next
  case (Vbytes x)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vstring x)
  then show ?case
apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def string_value_valid_def)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def string_value_valid_def)
    done
next
  case (Varray x1 x2)
  then show ?case sorry
qed
 


lemma encode_correct_converse :
  "can_encode_as v code start \<Longrightarrow>
  (\<exists> code' . encode v = Ok code')"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case 
    apply(auto simp add:encode_def)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case 
    apply(clarsimp)
    apply(atomize)
    apply(case_tac "encode (Vtuple ts vs)"; auto simp add:encode_def)
apply(case_tac "list_ex abi_type_isdynamic ts"; clarsimp)
     apply(simp split:sum.splits prod.splits)
    apply(clarsimp)
      apply(frule_tac encode_tuple_heads_fail)
       apply(simp add:tuple_value_valid_aux_def)
       apply(simp add:encode_tuple_tails_len)
      apply(clarsimp)
      apply(case_tac "abi_type_isdynamic (abi_get_type v)")
    apply(clarsimp)
      apply(drule_tac x = v in is_head_and_tail_elem)
        apply(simp)
        apply(clarsimp)
       apply(clarsimp)
    apply(rotate_tac 5)
       apply(drule_tac x = offset in spec) apply(drule_tac x = v in spec)
    apply(clarsimp)
    apply(split if_split_asm) apply(clarsimp)
      apply(frule_tac encode_tuple_heads_fail)
        apply(simp add:encode_tuple_tails_len)
    apply(rule_tac x = v in exI)
(* need a lemma here about is_head_and_tail as applied to v *)
      apply(clarify)
      apply(simp add:tuple_value_valid_aux_def)
    apply(drule_tac
      apply(case_tac "list_all abi_type_valid head_types \<and> tuple_value_valid_aux head_types heads \<and> list_all abi_value_valid_aux heads")
    apply(clarsimp)
    apply(case_tac "abi_type_isdynamic (abi_get_type v)"; clarsimp)


      apply(frule_tac encode_tuple_tails_len) apply(clarsimp)
      apply(case_tac vs; clarsimp) apply(case_tac x1; clarsimp)
      apply(case_tac "abi_type_isdynamic (abi_get_type a)"; clarsimp)
    apply(simp split:sum.splits)
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case sorry
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case sorry
next
  case (Ebytes l pre post count code)
  then show ?case sorry
next
  case (Estring full_code s l start)
  then show ?case sorry
qed

(* other direction: 

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
*)
end
