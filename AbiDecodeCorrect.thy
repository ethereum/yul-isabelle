theory AbiDecodeCorrect imports AbiEncodeSpec AbiDecode AbiEncodeCorrect

begin

declare [[show_types]]

lemma uint_reconstruct_valid [rule_format]:
" uint_value_valid x1 x2 \<Longrightarrow>
(0::nat) < x1 \<Longrightarrow> x1 \<le> (256::nat) \<Longrightarrow> 
 (8::nat) dvd x1 \<Longrightarrow>
 uint_value_valid x1 (uint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"

    apply(simp add:uint_value_valid_def) apply(clarify)
    apply(subgoal_tac "(take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) = (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)")
      apply(simp)
     apply(simp add:word_rcat_rsplit)
     apply(subgoal_tac "uint (word_of_int x2 :: 256 word) = x2") apply(simp) apply(rule_tac word_uint.Abs_inverse)
apply(simp) apply(simp add:uints_num)
      apply(subgoal_tac "(2 :: int)^x1 \<le> (2 :: int)^256") apply(simp)
    apply(rule_tac power_increasing) apply(assumption) apply(simp)
     apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done

lemma uint_reconstruct  :
" uint_value_valid x1 x2 \<Longrightarrow>
(0::nat) < x1 \<Longrightarrow> x1 \<le> (256::nat) \<Longrightarrow> 
 (8::nat) dvd x1 \<Longrightarrow>
 uint_value_valid x1 (uint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word)) \<Longrightarrow>
 uint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
     apply(simp add:uint_value_valid_def) apply(clarsimp)

    apply(subgoal_tac "(take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) = (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)")
      apply(simp)
      apply(simp add:word_rcat_rsplit)
      apply(rule_tac word_uint.Abs_inverse) apply(simp) apply(simp add:uints_num)
      apply(subgoal_tac "(2 :: int)^x1 \<le> (2 :: int)^256") apply(simp)
    apply(rule_tac power_increasing) apply(assumption) apply(simp)
  apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done


lemma sint_reconstruct_valid [rule_format] :
" sint_value_valid x1 x2 \<Longrightarrow>
(0::nat) < x1 \<Longrightarrow> x1 \<le> (256::nat) \<Longrightarrow> 
 (8::nat) dvd x1 \<Longrightarrow>
 sint_value_valid x1 (sint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"
    apply(simp add:sint_value_valid_def) apply(clarify)
    apply(subgoal_tac "(take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) = (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)")
      apply(simp)
     apply(simp add:word_rcat_rsplit)
     apply(subgoal_tac "sint (word_of_int x2 :: 256 word) = x2") apply(simp) apply(rule_tac word_sint.Abs_inverse)
apply(simp) apply(simp add:sints_num) 
   apply(subgoal_tac "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)") apply(simp)
    apply(rule_tac power_increasing)  apply(simp) apply(simp)
     apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done

lemma sint_reconstruct[rule_format] :
" sint_value_valid x1 x2 \<Longrightarrow>
(0::nat) < x1 \<Longrightarrow> x1 \<le> (256::nat) \<Longrightarrow> 
 (8::nat) dvd x1 \<Longrightarrow>
 sint_value_valid x1 (sint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word)) \<Longrightarrow>
 sint (word_rcat (take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
    apply(simp add:sint_value_valid_def) apply(clarify)
    apply(subgoal_tac "(take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) = (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)")
      apply(simp)
     apply(simp add:word_rcat_rsplit)
     apply(subgoal_tac "sint (word_of_int x2 :: 256 word) = x2") apply(simp) apply(rule_tac word_sint.Abs_inverse)
apply(simp) apply(simp add:sints_num) 
   apply(subgoal_tac "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)") apply(simp)
    apply(rule_tac power_increasing)  apply(simp) apply(simp)
  apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done

lemma uint_valid_length :
  "uint_value_valid x1 x2 \<Longrightarrow>
   length (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list) = 32"
  apply(simp add:uint_value_valid_def) apply(clarify)
       apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done

lemma sint_valid_length :
  "sint_value_valid x1 x2 \<Longrightarrow>
   length (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list) = 32"
  apply(simp add:sint_value_valid_def) apply(clarify)
       apply(simp add:word_rsplit_def bin_rsplit_len word_rcat_def)
  done

lemma abi_encode_decode_static' :
  "(\<forall> code prefix post . 
   encode_static v = Ok code \<longrightarrow>
   abi_value_valid v \<longrightarrow>
   decode_static (abi_get_type v) (length prefix, (prefix @ code @ post)) = Ok v) \<and>
   ((\<forall> v t n code prefix post.
      v = (Vfarray t n vs) \<longrightarrow>
          encode_static v = Ok code \<longrightarrow>
          abi_value_valid v \<longrightarrow>
          decode_static_tup (List.replicate n t) (length prefix, prefix @ code @ post) = Ok vs) \<and>
     ( \<forall> v ts  code prefix post.
          v = (Vtuple ts vs) \<longrightarrow>
          encode_static v = Ok code \<longrightarrow>
          abi_value_valid v \<longrightarrow>
          decode_static_tup ts (length prefix, prefix @ code @ post) = Ok vs)
   )"
proof(induction rule:my_abi_value_induct)
    (* Vuint *)
  case (1 x1 x2)
  then show ?case apply(clarsimp)
    apply(simp add:Let_def)
    apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in uint_valid_length; simp)
     apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in uint_reconstruct; simp)
     apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in uint_reconstruct_valid; simp)
    done
next
  (* Vsint *)
  case (2 x1 x2)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def)
        apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in sint_valid_length; simp)
     apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in sint_reconstruct; simp)
     apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2 in sint_reconstruct_valid; simp)
    done
next
    (* Vaddr *)
  case (3 x)
  then show ?case 
    apply(clarsimp) apply(simp add:Let_def)
    apply(simp add:addr_value_valid_def)
        apply(cut_tac ?x1.0 = 160 and ?x2.0 = x in uint_valid_length; simp)
     apply(cut_tac  ?x1.0 = 160 and ?x2.0 = x  in uint_reconstruct; simp)
     apply(cut_tac  ?x1.0 = 160 and ?x2.0 = x  in uint_reconstruct_valid; simp)
    done
next
    (* Vbool *)
  case (4 x)
  then show ?case 
    apply(case_tac x) apply(clarsimp)
     apply(simp add:Let_def bool_value_valid_def)
apply(cut_tac ?x1.0 = 256 and ?x2.0 = 1 in uint_reconstruct_valid; simp add:uint_value_valid_def)
     apply(cut_tac ?x1.0 = 256 and ?x2.0 = 1 in uint_reconstruct; simp add:uint_value_valid_def)
    apply(simp add:word_rcat_def word_rsplit_def bin_rsplit_len)

    apply(clarsimp)
     apply(simp add:Let_def bool_value_valid_def)
apply(cut_tac ?x1.0 = 256 and ?x2.0 = 0 in uint_reconstruct_valid; simp add:uint_value_valid_def)
     apply(cut_tac ?x1.0 = 256 and ?x2.0 = 0 in uint_reconstruct; simp add:uint_value_valid_def)
    apply(simp add:word_rcat_def word_rsplit_def bin_rsplit_len)
    done
next
  (* Vfixed *)
  case (5 x1 x2 x3a)
  then show ?case 
        apply(clarsimp)
    apply(simp add:Let_def)
    apply(simp add:fixed_value_valid_def)
     apply(simp add:fixed_value_valid_def split:option.splits prod.splits if_split_asm)
    apply(clarsimp)
    apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2a in sint_valid_length; simp add:sint_value_valid_def)
    apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2a in sint_reconstruct_valid; simp add:sint_value_valid_def)
     apply(cut_tac ?x1.0 = 256 and ?x2.0 = x2a in sint_reconstruct; simp add:sint_value_valid_def)
           apply(subgoal_tac "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)") apply(simp)
       apply(rule_tac power_increasing)  apply(simp) apply(simp)
       apply(subgoal_tac "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)") apply(simp)
     apply(rule_tac power_increasing)  apply(simp) apply(simp)



    apply(rule_tac conjI)

(* first part - if it's valid it works *)
    apply(clarify)
     apply(simp add: Rat.of_int_def)
     apply(drule_tac quotient_of_div) apply(simp)
    apply(drule_tac quotient_of_div) apply(simp)
     apply(clarsimp)
     apply(simp add:Rat.divide_rat_def)
     apply(subgoal_tac "(x3a * ((10::rat) ^ x2 * (inverse (10 :: rat) ^ x2)) :: rat) = (rat_of_int x1a * inverse ((10::rat) ^ x2) :: rat)")
      apply(cut_tac a = "(10::rat) ^ x2 :: rat" in Fields.division_ring_class.right_inverse) apply(simp)
    apply(cut_tac s = "(10::rat) ^ x2 * inverse ((10::rat) ^ x2) :: rat" and t = "1 :: rat" and
    P = "(\<lambda> r . x3a * (r :: rat) = rat_of_int x1a * inverse ((10::rat) ^ x2))" in subst)
        apply(assumption)
       apply(simp only: power_inverse)
      apply(simp)
     apply(simp only: power_inverse) 
     apply(simp only: sym [OF semigroup_mult_class.mult.assoc])


(* second part - it's valid *)

    apply(clarsimp)
     apply(drule_tac quotient_of_div) apply(simp)
    apply(simp add:Rat.quotient_of_int)
    done
next
  (* Vufixed *)
  case (6 x1 x2 x3a)
  then show ?case

        apply(clarsimp)
    apply(simp add:Let_def)
    apply(simp add:ufixed_value_valid_def)
     apply(simp add:ufixed_value_valid_def split:option.splits prod.splits if_split_asm)
    apply(clarsimp)
    apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2a in uint_valid_length; simp add:uint_value_valid_def)
    apply(cut_tac ?x1.0 = x1 and ?x2.0 = x2a in uint_reconstruct_valid; simp add:uint_value_valid_def)
     apply(cut_tac ?x1.0 = 256 and ?x2.0 = x2a in uint_reconstruct; simp add:uint_value_valid_def)
           apply(subgoal_tac "(2 :: int)^(x1) \<le> (2 :: int)^(256)") apply(simp)
       apply(rule_tac power_increasing)  apply(simp) apply(simp)
       apply(subgoal_tac "(2 :: int)^(x1) \<le> (2 :: int)^(256)") apply(simp)
     apply(rule_tac power_increasing)  apply(simp) apply(simp)



    apply(rule_tac conjI)

(* first part - if it's valid it works *)
    apply(clarify)
     apply(simp add: Rat.of_int_def)
     apply(drule_tac quotient_of_div) apply(simp)
    apply(drule_tac quotient_of_div) apply(simp)
     apply(clarsimp)
     apply(simp add:Rat.divide_rat_def)
     apply(subgoal_tac "(x3a * ((10::rat) ^ x2 * (inverse (10 :: rat) ^ x2)) :: rat) = (rat_of_int x1a * inverse ((10::rat) ^ x2) :: rat)")
      apply(cut_tac a = "(10::rat) ^ x2 :: rat" in Fields.division_ring_class.right_inverse) apply(simp)
    apply(cut_tac s = "(10::rat) ^ x2 * inverse ((10::rat) ^ x2) :: rat" and t = "1 :: rat" and
    P = "(\<lambda> r . x3a * (r :: rat) = rat_of_int x1a * inverse ((10::rat) ^ x2))" in subst)
        apply(assumption)
       apply(simp only: power_inverse)
      apply(simp)
     apply(simp only: power_inverse) 
     apply(simp only: sym [OF semigroup_mult_class.mult.assoc])


(* second part - it's valid *)

    apply(clarsimp)
     apply(drule_tac quotient_of_div) apply(simp)
    apply(simp add:Rat.quotient_of_int)
    done
next
  (* Vfbytes *)
  case (7 x1 x2)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def)
    apply(simp add:fbytes_value_valid_def split:option.splits prod.splits if_split_asm)
    apply(clarsimp)
    apply(rule_tac conjI)

    apply(clarsimp)
     apply(case_tac x2a; clarsimp)

    apply(case_tac x2a; clarsimp)
    apply(simp)
    done
next
  (* Vfunction *)
  case (8 x1 x2)
  then show ?case 
    apply(clarsimp)
    done
next
  (* need a decode_static_tup clause (i.e. generalized induction rule) *)
  (* Vfarray *)
  case (9 x1 x2 x3a)
  then show ?case
    apply(clarsimp)
    done
next
  (* Vtuple *)
  case (10 x1 x2)
  then show ?case apply(clarsimp) done
next
  (* Vbytes *)
  case (11 x)
  then show ?case
    apply(clarsimp)
    done
next
  (* Vstring *)
  case (12 x)
  then show ?case
    apply(clarsimp)
    done
next
  (* Varray*)
  case (13 x1 x2)
  then show ?case
    apply(clarsimp)
    done
next
  (* nil *)
  case 14
  then show ?case
    apply(clarsimp)
  apply(simp add:farray_value_valid_aux_def tuple_value_valid_aux_def split:sum.splits)
    done
next
  (* cons *)
  case (15 t l)
  then show ?case
    apply(clarsimp)
    apply(rule_tac conjI)

    (* farray *)
     apply(rotate_tac -1) apply(drule_tac mythin) apply(clarsimp)
     apply(simp add:farray_value_valid_aux_def tuple_value_valid_aux_def split:sum.splits)
      apply(case_tac "encode_static t"; clarsimp)
      apply(drule_tac x = "abi_get_type t" in spec) apply(clarsimp) apply(rotate_tac -1)
      apply(drule_tac x = "prefix @ a" in spec) apply(clarsimp)
      apply(cut_tac v = t and code = a in encode_static_size; simp)

     apply(case_tac "encode_static t"; clarsimp)

    (* tuple *)
     apply(rotate_tac 1) apply(drule_tac mythin) apply(clarsimp)
     apply(simp add:farray_value_valid_aux_def tuple_value_valid_aux_def split:sum.splits)
      apply(case_tac "encode_static t"; clarsimp)
      apply(drule_tac x = "prefix @ a" in spec) apply(clarsimp)
      apply(cut_tac v = t and code = a in encode_static_size; simp)

     apply(case_tac "encode_static t"; clarsimp)
    done
qed

lemma abi_encode_decode_static :
"encode_static v = Ok code \<Longrightarrow>
   abi_value_valid v \<Longrightarrow>
   decode_static (abi_get_type v) (length prefix, (prefix @ code @ post)) = Ok v"
  apply(cut_tac abi_encode_decode_static'; auto)
  done
(*
lemma abi_decode_encode_static' :
  "(\<forall> code prefix post . 
   encode_static v = Ok code \<longrightarrow>
   abi_value_valid v \<longrightarrow>
   decode_static (abi_get_type v) (length prefix, (prefix @ code @ post)) = Ok v) \<and>
   ((\<forall> v t n code prefix post.
      v = (Vfarray t n vs) \<longrightarrow>
          encode_static v = Ok code \<longrightarrow>
          abi_value_valid v \<longrightarrow>
          decode_static_tup (List.replicate n t) (length prefix, prefix @ code @ post) = Ok vs) \<and>
     ( \<forall> v ts  code prefix post.
          v = (Vtuple ts vs) \<longrightarrow>
          encode_static v = Ok code \<longrightarrow>
          abi_value_valid v \<longrightarrow>
          decode_static_tup ts (length prefix, prefix @ code @ post) = Ok vs)
   )"
*)
(*
lemma abi_decode_static_succeed :
  "can_encode_as v full_code start \<Longrightarrow>
   (abi_type_isstatic (abi_get_type v) \<longrightarrow>
   decode_static (abi_get_type v) (start, full_code) = Ok v)"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case
    apply(clarsimp)
    apply(drule_tac abi_encode_decode_static) apply(auto)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case 
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
*)

(* this isn't true - offsets will be shifted *)
(*
lemma can_encode_as_cons_static [rule_format]:
  "can_encode_as v code pre_len \<Longrightarrow>
   (\<forall> x xs ys . v = Vtuple (abi_get_type x # xs) (x#ys) \<longrightarrow>
      abi_type_isstatic (abi_get_type x) \<longrightarrow>
      can_encode_as (Vtuple xs ys) code (pre_len + abi_static_size (abi_get_type x)))
      "
  apply(induction rule:can_encode_as.induct)
       apply(simp_all)

  (* static *)
   apply(clarsimp)
   apply(simp split:sum.splits)
   apply(simp add:tuple_value_valid_aux_def)
   apply(case_tac "encode_static x"; clarsimp)
   apply(simp split:sum.splits) apply(clarsimp)
   apply(cut_tac v = "(Vtuple (map abi_get_type ys) ys)" and code = "concat x1a" and pre = "pre @ a" and post = post in  Estatic)
      apply(clarsimp)
     apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)
    apply(simp)
   apply(frule_tac encode_static_size) apply(simp) apply(simp)

  (* dynamic *)
  apply(clarsimp)
  apply(case_tac " t = abi_get_type x"; clarsimp)
  apply(rule_tac ?a1.0 = "x#ys" and ?a2.0 = heads and ?a3.0 = head_types and ?a4.0 = tails in is_head_and_tail.cases; simp)
  apply(clarsimp)
  apply(rule_tac heads = ysa and tails = tailsa and t = t  in Etuple_dyn; simp?)
   apply(simp add:tuple_value_valid_aux_def)
  apply(clarsimp)
   apply(simp add:tuple_value_valid_aux_def)

  apply(atomize)
  apply(drule_tac x = offset in spec)
   apply(case_tac "encode_static x"; clarsimp)
   apply(simp split:sum.splits) apply(clarsimp)
   apply(cut_tac v = "(Vtuple (map abi_get_type ys) ys)" and code = "concat x1a" and pre = "pre @ a" and post = post in  Estatic)
      apply(clarsimp)
     apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)
    apply(simp)
   apply(frule_tac encode_static_size) apply(simp) apply(simp)
*)
(* need to make this valid inductively over offset/l *)
(* need to stipulate that heads tuple encodes at beginning
of the code we are passing in to decoder
(as well as the fact that tails can all encode)
*)
(* need to generalize over prefix offsets *)

(* count vs offset. count needs to be less than offset (idea is that it is bytes read so far. *)
(* offset + count = length prefix?
remember, offset is absolute but count is relative (size of head so far) *)
(*
lemma abi_decode_dyn_tuple_heads_succeed :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> heads' tails' count count' offset prefix post l bytes.
decode'_dyn_tuple_heads (map abi_get_type vs) count (offset, (prefix @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
offset + count = int (length prefix) \<longrightarrow>
list_ex abi_type_isdynamic (map abi_get_type vs) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (l) (count) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (prefix @ l @ post) (int (length (prefix)) + offset)) \<longrightarrow>
somes heads' = heads \<and>
map fst tails = (somes tails') \<and>
count' = heads_length vs + count)"
*)

lemma is_head_and_tail_heads_elem :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   h \<in> set heads \<Longrightarrow>
   abi_type_isstatic (abi_get_type h)"
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

lemma is_head_and_tail_static_heads_eq :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   list_all abi_type_isstatic (map abi_get_type vs) \<Longrightarrow>
   heads = vs"
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

(*declare [[simp_trace_new]]*)

(* need? list_ex abi_type_isdynamic (map abi_get_type vs) \<longrightarrow> *)
(* idea: talk explicitly about a prefix of vs? *)
(* should we make the "can_encode_as" argument weaker? (full heads vs tail of heads) *)
(*
lemma abi_decode_dyn_tuple_heads_succeed :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> vs_pre vs' heads' tails' count' offset pre1 pre2 post l bytes.
vs = vs_pre @ vs' \<longrightarrow>
int (length pre2) = heads_length vs_pre \<longrightarrow>
decode'_dyn_tuple_heads (map abi_get_type vs') (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length (pre1)) + offset)) \<longrightarrow>
somes heads' = heads \<and>
map fst tails = (somes tails') \<and>
count' = heads_length vs)"
  sorry
*)

lemma abi_decode_dyn_tuple_heads_succeed :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> heads' tails' count' offset pre1 pre2 post l bytes.
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length (pre1)) + offset)) \<longrightarrow>
somes heads' = heads \<and>
map fst tails = (somes tails') \<and>
count' = heads_length vs + int (length pre2))"
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case
    apply(clarsimp)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case
    apply(clarsimp)
    apply(simp split:sum.splits prod.splits)
    apply(clarsimp)
    apply(simp split:add:abi_static_size_nonneg)

    apply(rule_tac ?a1.0 = "(Vtuple (abi_get_type x # ts) (x # ys))"
 and ?a2.0 = "pre1 @ pre2 @ l @ post"
and ?a3.0 = "int (length pre1) + int (length pre2)"
 in can_encode_as.cases; simp?)

    (* remaining heads tuple is static *)
      apply(clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
      apply(clarsimp)
      apply(case_tac "encode_static x"; clarsimp) apply(simp split:sum.splits)
      apply(clarsimp)

      apply(cut_tac v = "Vtuple(map abi_get_type ys) ys" and code = "concat x1a" and pre = "pre@a" and post = posta in Estatic; simp?)
       apply(simp add:tuple_value_valid_aux_def)

    apply(subgoal_tac "pre1 @ pre2 = pre")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre) ")
    apply(clarify) apply(simp)

      apply(drule_tac x = x1d in spec) apply(drule_tac x = x1e in spec)
    apply(rotate_tac -1)
      apply(drule_tac x = "count'" in spec)
      apply(rotate_tac -1)
      apply(drule_tac x = pre1 in spec) apply(drule_tac x = "pre2@a" in spec)
    apply(drule_tac x = "posta" in spec)
      (* i think this needs to be a suffix of l, not l (?) *)
      apply(drule_tac x = "concat x1a"    in spec)
      apply(clarsimp)
       apply(frule_tac v = x in encode_static_size; clarsimp)
       apply(subgoal_tac "int (length pre1) + (int (length pre2) + int (length a)) = (int (length pre1) + int (length pre2) + int (length a))")
    apply(clarsimp)
        apply(drule_tac prefix = "pre1 @ pre2" and post = "concat x1a @ posta" in abi_encode_decode_static)
         apply(simp) apply(clarsimp)
      apply(arith)
(* slow. *)

    apply(simp add:append_eq_conv_conj)
    
    (* remaining heads tuple is dynamic - contradiction*)
    apply(clarsimp)
    apply(case_tac "t = abi_get_type x"; clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
    apply(clarsimp)

    apply(frule_tac vs = xs and heads = ys and h = xa in is_head_and_tail_heads_elem)
     apply(simp)
    apply(clarsimp)
    done
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def split:sum.splits prod.splits if_split_asm)
    apply(clarsimp)
    apply(rule_tac ?a1.0 = "(Vtuple (Tuint (256::nat) # ts) (Vuint (256::nat) ptr # ys))"
 and ?a2.0 = "pre1 @ pre2 @ l @ post"
and ?a3.0 = "int (length pre1) + int (length pre2)"
 in can_encode_as.cases; simp?)
     apply(clarsimp)
     apply(simp add:tuple_value_valid_aux_def) apply(clarsimp)
    apply(simp add:Let_def split:sum.splits prod.splits if_split_asm)

     apply(drule_tac x = x1a in spec) apply(drule_tac x = x1b in spec)
     apply(rotate_tac -1) apply(drule_tac x = count' in spec) apply(drule_tac x = pre1 in spec)
     apply(rotate_tac -1)
     apply(drule_tac x = "pre2 @ word_rsplit (word_of_int ptr :: 256 word)" in spec)
    apply(rotate_tac -1)
     apply(drule_tac x = posta in spec) apply(drule_tac x = "concat x1c" in spec)
     apply(clarsimp)
      apply(subgoal_tac "pre1 @ pre2 = pre")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre) ")
    apply(clarify) apply(simp)
         apply(subgoal_tac "int (length (word_rsplit (word_of_int ptr :: 256 word) :: 8 word list)) = (32 :: int)") 
       apply(clarsimp)

      apply(cut_tac v = "Vtuple(map abi_get_type ys) ys" and code = "concat x1c" and pre = "pre1@pre2@word_rsplit (word_of_int ptr :: 256 word) :: 8 word list" and post = posta in Estatic; simp?)
        apply(simp add:tuple_value_valid_aux_def)
    apply(clarsimp)

         apply(subgoal_tac "int (length (word_rsplit (word_of_int ptr :: 256 word) :: 8 word list)) = (32 :: int)") 
       apply(clarsimp)

    sorry
qed
  sorry


lemma abi_decode_succeed2 [rule_format]:
  "\<forall> full_code start . 
   can_encode_as v full_code start \<longrightarrow>
   decode (abi_get_type v) (drop (nat start) full_code) = Ok v"
proof(induction v)
  case (Vtuple ts vs) thus ?case
    apply(clarsimp)
    apply(simp add:Let_def)
    apply(rule_tac conjI)
     defer (* static *)
     apply(clarsimp)
     apply(rule_tac conjI)
    defer (* static? *)

(*
      apply(clarsimp) apply(rule_tac conjI) apply(simp add:list_ex_iff) apply(fastforce)
*)
      apply(clarsimp)
    apply(rule_tac conjI)
      apply(case_tac "decode'_dyn_tuple_heads ts (0::int) (0::int, drop (nat start) full_code)") apply(clarsimp)

       apply(case_tac "decode'_dyn_tuple_tails aa ts a ab (0::int, drop (nat start) full_code)") apply(clarsimp)
         apply(rename_tac  newa2)
    apply(rule_tac ?a1.0 = "(Vtuple ts vs) " and
?a2.0 = full_code and
?a3.0 = start in can_encode_as.cases; clarsimp?)
         apply(simp add:tuple_value_valid_aux_def)

         apply(atomize)
         apply(subgoal_tac "\<exists> v . v \<in> set vs \<and> abi_get_type v = t") apply(clarsimp)
          apply(drule_tac x = v in  spec) apply(clarsimp)
          apply(frule_tac x = v in is_head_and_tail_vs_elem; simp?)
          apply(clarsimp)
          apply(drule_tac x = offset in spec) apply(drule_tac x = v in spec) apply(clarsimp)
          apply(drule_tac x = full_codea in spec) apply(drule_tac x = "offset + starta" in spec)
          apply(clarsimp)
          apply(simp add:Let_def del:decode'.simps split:if_splits sum.splits prod.splits) apply(clarify)
    apply(clarsimp)
*)
(* idea: decode_heads on head types will produce no tails
   decode_tails on that result will be a noop*)

(*
lemma. related output of decode'_dyn_tuple_heads to static head type Vtuple

is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<exists> heads' tails headlen .
heads = filter is_some heads' \<and>
tails = map (Vuint 256) (filter (is_some) tails) \<and>
headlen = list_sum (map (heads_length o abi_get_type) vs) \<and>
decode'_dyn_tuple_heads (map abi_get_type vs) headlen (offset, l) = Ok (heads', tails', headlen, bytes) \<Longrightarrow>
)



then what about decode'_dyn_tuple_tails?
is_head_and_tail vs heads head_types tails \<Longrightarrow>
heads = filter is_some heads'  \<Longrightarrow>
tails = map (Vuint 256) (filter (is_some) tails) \<Longrightarrow>
headlen = heads_length ts 

*)
    
(* if a valid encoding exists for our value,
   the decoder will give it to us *)
(*
lemma abi_decode_succeed  :
  "can_encode_as v full_code start \<Longrightarrow> 
   decode (abi_get_type v) (drop (nat start) full_code) = Ok v"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case 
    apply(clarsimp)
    apply(frule_tac prefix = "[]" and code = code and post = post in abi_encode_decode_static)
     apply(clarsimp)
    apply(clarsimp)
    apply(frule_tac encode_static_size) apply(clarsimp) apply(clarsimp)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def) apply(simp split:if_split_asm sum.split_asm)
    apply(simp add:Let_def)
    apply(case_tac "list_ex abi_type_isdynamic head_types") apply(clarsimp)
     apply(simp split:if_split_asm sum.split_asm prod.splits) apply(clarsimp)

     apply(rule_tac conjI)
      apply(clarsimp) apply(rule_tac conjI) apply(simp add:list_ex_iff) apply(fastforce)

      apply(clarsimp)
      apply(case_tac "decode'_dyn_tuple_heads ts (0::int) (0::int, drop (nat start) full_code)") apply(clarsimp)
    apply(rename_tac newa)
       apply(case_tac "decode'_dyn_tuple_tails aa ts a ab (0::int, drop (nat start) full_code)") apply(clarsimp)
        apply(rename_tac newa2)

(* idea: decode_heads on head types will produce no tails
   decode_tails on that result will be a noop*)
        apply(simp add:tuple_value_valid_aux_def)

(*
  is_head_and_tail vs heads head_types tails \<Longrightarrow>
  map abi_get_type vs = ts \<Longrightarrow>
  decode'_dyn_tuple_heads head_types (0::int) (0::int, drop (nat start) full_code) = Ok (x1a, x1b, x1c, x2b) \<Longrightarrow>
  decode'_dyn_tuple_heads head_types (0::int) (0::int, drop (nat start) full_code) = Ok (x1a, x1b, x1c, x2b)
  decode'_dyn_tuple_tails x1b head_types x1a x1c (0::int, drop (nat start) full_code) = Ok (heads, x2c) \<Longrightarrow>
decode'_dyn_tuple_heads ts (0::int) (0::int, drop (nat start) full_code) = Ok (a, aa, ab, newa) \<Longrightarrow>
decode'_dyn_tuple_tails aa ts a ab (0::int, drop (nat start) full_code) = Ok (ac, newa2) \<Longrightarrow>
  ac = vs
*)

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
*)
lemma abi_decode_succeed_converse :
  "\<And> v full_code .
    decode (abi_get_type v) full_code = Ok v \<Longrightarrow>
    can_encode_as v full_code 0 (length full_code)"
  sorry

end