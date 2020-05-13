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

lemma is_head_and_tail_head_types_elem :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   ht \<in> set head_types \<Longrightarrow>
   abi_type_isstatic (ht)"
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

(* combine returned values of decode'_dyn_tuple_heads *)
fun ht_combine :: "abi_value option \<Rightarrow> (int option) \<Rightarrow> abi_value option" where
"ht_combine (Some v) None = Some v"
| "ht_combine None (Some i) = Some (Vsint 256 i)"
| "ht_combine _ _ = None"

(* problem - we need to shift tails in order to deal with discrepancy between the offsets. (?) *)
(* almost there - now we need to fix heads *)
(*
lemma abi_decode_dyn_tuple_heads_succeed [rule_format]:
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> heads' tails' count' offset pre1 pre2 post l bytes.
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length pre1) + offset)) \<longrightarrow>
those (map2 ht_combine heads' 
       (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
count' = heads_length vs + int (length pre2))"
*)

fun ht_wellbehaved ::
  "(int option) list \<Rightarrow> abi_type list \<Rightarrow> abi_value option list \<Rightarrow> bool" where
"ht_wellbehaved [] [] [] = True"
| "ht_wellbehaved (Some i#ios) (t#ts) (None#vos) =
  (abi_type_isdynamic t \<and> ht_wellbehaved ios ts vos)"
| "ht_wellbehaved (None#ios) (t#ts) (vo#vos) =
  (abi_type_isstatic t \<and> ht_wellbehaved ios ts vos)"
| "ht_wellbehaved _ _ _ = False"

lemma abi_decode_dyn_tuple_heads_succeed [rule_format]:
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> heads' tails' count' offset pre1 pre2 post l bytes.
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length pre1) + offset)) \<longrightarrow>
those (map2 ht_combine heads' 
       (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
count' = heads_length vs + int (length pre2) \<and>
ht_wellbehaved tails' (map abi_get_type vs) heads')"
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
    apply(rule_tac ?a1.0 = "(Vtuple (Tsint (256::nat) # ts) (Vsint (256::nat) ptr # ys))"
 and ?a2.0 = "pre1 @ pre2 @ l @ post"
and ?a3.0 = "int (length pre1) + int (length pre2)"
 in can_encode_as.cases; simp?)
     apply(clarsimp)
     apply(simp add:tuple_value_valid_aux_def) apply(clarsimp)
    apply(simp add:Let_def split:sum.splits prod.splits if_split_asm)

     apply(case_tac x1; clarsimp)

      apply(cut_tac v = "Vtuple(map abi_get_type ys) ys" and code = "concat list" and pre = "pre @ word_rsplit (word_of_int ptr :: 256 word)" and post = posta in Estatic; simp?)
       apply(simp add:tuple_value_valid_aux_def)



     apply(drule_tac x = x1a in spec) apply(drule_tac x = x1b in spec)
     apply(rotate_tac -1) apply(drule_tac x = count' in spec) apply(drule_tac x = pre1 in spec)
     apply(rotate_tac -1)
     apply(drule_tac x = "pre2 @ word_rsplit (word_of_int ptr :: 256 word)" in spec)
    apply(rotate_tac -1)
     apply(drule_tac x = posta in spec) 
apply(drule_tac x = "concat list" in spec)

      apply(subgoal_tac "pre1 @ pre2 = pre")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre) ")
    apply(clarify) apply(simp)
         apply(subgoal_tac "int (length (word_rsplit (word_of_int ptr :: 256 word) :: 8 word list)) = (32 :: int)") 
       apply(clarsimp)

       apply(subgoal_tac "(int (length pre1) + int (length pre2) + (32::int)) = (int (length pre1) + (int (length pre2) + (32::int)))")
        apply(clarsimp)
        apply(simp add: List.append_eq_append_conv_if)
    apply(simp split:if_split_asm)
         apply(clarsimp)
         apply(frule_tac sint_reconstruct_valid; simp?)
         apply(drule_tac sint_reconstruct; simp?)

         apply(subgoal_tac "l @ drop (length l) (word_rsplit (word_of_int ptr :: 256 word) :: 8 word list) = word_rsplit (word_of_int ptr :: 256 word) ")
          apply(clarsimp)
    apply(cut_tac n = "length l" and xs = "(word_rsplit (word_of_int ptr :: 256 word) :: 8 word list)" in append_take_drop_id)
         apply(clarsimp)

        apply(clarsimp)
         apply(frule_tac sint_reconstruct_valid; simp?)
        apply(drule_tac sint_reconstruct; simp?)
       apply(arith)

      apply(drule_tac sint_valid_length;simp?)
     apply(simp add:append_eq_conv_conj)

    (* dynamic *)
    apply(clarsimp)
    apply(case_tac "t \<in> set ts"; clarsimp)
(* contradiction: t is dynamic but ts is head_types *)
    apply(frule_tac ht = t in is_head_and_tail_head_types_elem; simp?)
    done
qed

(* idea: our hypothesis for these lemmas
(corresponding to the inductive hypotheses we get while simplifying in the main theorem)
aren't right. We need something like the following as a hypothesis:
*)
lemma abi_decode_dyn_tuple_tails_succeed:
"(\<And>x2a::abi_value.
           x2a \<in> set vs \<Longrightarrow>
           \<forall>(full_code::8 word list) start::int.
              can_encode_as x2a full_code start \<longrightarrow>
              (\<exists>len::int. decode' (abi_get_type x2a) (start, full_code) = Ok (x2a, len)))"
  oops
(*

*)
(*
lemma abi_decode_dyn_tuple_heads_succeed :
"
 list_ex abi_type_isdynamic (map abi_get_type vs) \<Longrightarrow>
       can_encode_as (Vtuple (map abi_get_type vs) vs) full_codea starta \<Longrightarrow>
       decode'_dyn_tuple_heads (map abi_get_type vs) (0::int) (starta, full_codea) = Ok (a, aa, heads_length vs, b) \<Longrightarrow>
       decode'_dyn_tuple_tails aa (map abi_get_type vs) a (heads_length vs) (starta, full_codea) = Ok (ac, newa2) \<Longrightarrow>
       abi_type_isdynamic (abi_get_type x) \<Longrightarrow>
       is_head_and_tail vs heads head_types tails \<Longrightarrow>
       can_encode_as (Vtuple head_types heads) full_codea starta \<Longrightarrow>
       (\<And>(offset::int) v::abi_value. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_codea (offset + starta)) \<Longrightarrow>
       list_all abi_type_valid (map abi_get_type vs) \<Longrightarrow>
       list_all abi_value_valid_aux vs \<Longrightarrow>
       ts = map abi_get_type vs \<Longrightarrow>
       x \<in> set vs \<Longrightarrow>
       int (min (length full_codea) (nat starta)) = starta \<Longrightarrow>
       those (map2 ht_combine a (map (case_option None (\<lambda>t::int. Some (t - starta))) aa)) = Some heads \<Longrightarrow>
       map (\<lambda>x::int \<times> abi_value. fst x + starta) tails = somes aa \<Longrightarrow> ac = vs
"
*)

(*        decode'_dyn_tuple_heads (map abi_get_type vs) (0::int) (start, full_code) = Ok (heads', tails', heads_length vs, bytes) \<longrightarrow>
 *)

(*
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
*)

(* not sure if needed:
(* 
 *)
(*

*)
*)
(* need reasoning about prefix? *)
(* maybe need to strengthen lemma about encode_dyn_tuple_heads to state that
   heads will all be static. *)
(* might be able to get away with just adding can_encode_as premises.
(from previous theorem). just need to figure out how to generalize them
it seems like there is some kind of dependency on some of the other is_head_and_tail parameters
that are making is_head_and_tail induction not work.
*)
(* use arbitrary in the induction method *)
(* needed?        is_head_and_tail vs heads head_types tails \<longrightarrow>

*)
(* have a smaller lemma for a single head *)
(*
lemma abi_decode_dyn_tuple_tails_succeed [rule_format]:
"     
  (\<forall>  code pre1 pre2 post start heads' tails' offset bytes vs_out bytes'  heads head_types tails .
       decode'_dyn_tuple_tails tails' (map abi_get_type vs) heads' offset (int (length pre1), pre1@pre2@code@post) = Ok (vs_out, bytes') \<longrightarrow>
        can_encode_as (Vtuple (map abi_get_type vs) vs) (pre1@pre2@code@post) (int (length pre1)) \<longrightarrow>
        (\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1@pre2@code@post) (int (length pre1) + offset)) \<longrightarrow>
       those (map2 ht_combine heads' (map (case_option None (\<lambda>t::int. Some (t - int (length pre1)))) tails')) = Some heads \<longrightarrow>
       map (\<lambda>x::int \<times> abi_value. fst x + int (length pre1)) tails = somes (tails') \<longrightarrow>
       vs_out = vs)
"
proof(induction vs)
  case Nil
  then show ?case 
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
    apply(case_tac heads'; clarsimp)
    done
next
  case (Cons a vs)
  then show ?case
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
    apply(case_tac heads'; clarsimp)
    apply(simp split:sum.splits option.splits prod.splits if_splits)
(* second goal should be resolved by a lemma about how
decode'_dyn_tuple_tails only succeeds if the inputs have same length
and don't "collide" *)
     apply(clarsimp)
    apply(case_tac aa; clarsimp)
     apply(simp split:sum.splits option.splits prod.splits if_splits)

    apply(clarsimp)



    apply(rule_tac ?a1.0 = "(Vtuple (abi_get_type a # map abi_get_type vs) (a # vs))"
and ?a2.0 = "(pre1 @ pre2 @ code @ post)"
and ?a3.0 = "(int (length pre1)) "
in can_encode_as.cases; simp?)

      apply(clarsimp)
    apply(case_tac "encode_static a"; clarsimp)
      apply(simp split:sum.splits option.splits prod.splits if_splits)
      apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def)
      apply(drule_tac x = "concat x1b" in spec)
      apply(drule_tac x = pre in spec)
      apply(drule_tac x = "aa" in spec)
      apply(drule_tac x = "posta" in spec)
      apply(drule_tac x = "lista" in spec)
      apply(drule_tac x = list in spec)
    apply(rotate_tac -1)
      apply(drule_tac x = offset in spec) (* may need change*)
      apply(drule_tac x = x1a in spec) apply(clarsimp)
    apply(cut_tac v = "(Vtuple (map abi_get_type vs) vs)"  and code = "concat x1b" and pre = "pre @ aa" and post = posta in
Estatic; simp?)

    apply(simp add:tuple_value_valid_aux_def)
*)
(*

     apply(drule_tac x = code in spec)
     apply(drule_tac x = pre1 in spec)
     apply(drule_tac x = pre2 in spec)
apply(drule_tac x = post in spec)
     apply(drule_tac x = lista in spec)
apply(drule_tac x = list in spec)

    apply(rotate_tac -1)
apply(drule_tac x = offset in spec) apply(drule_tac x = x1a in spec) 
     apply(clarsimp)

      apply(clarsimp)
    apply(case_tac "encode_static x2"; clarsimp)
      apply(simp split:sum.splits option.splits prod.splits if_splits)
      apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def) apply(clarsimp)
    apply(drule_tac x = heads in
(*
    apply(case_tac aa; clarsimp)
      apply(simp add:Let_def split: if_split_asm sum.splits prod.splits)

    apply(case_tac "encode_static x"; clarsimp)


     apply(drule_tac x = code in spec)
apply(drule_tac x = "start" in spec) 
     apply(drule_tac x = lista in spec) apply(drule_tac x = list in spec) 
    apply(rotate_tac -1)
    apply(drule_tac x = "offset + 32" in spec) apply(drule_tac x = x1a in spec) 
    apply(rule_tac conjI)
     apply(clarsimp)

     defer
    apply(clarsimp)
*)
oops
*)

(* assumption used to basically state that
tails decoder is being called with "reasonable" inputs"
TODO: add this to the conclusion of correctness for heads.
*)

(* Based on looking at
encode_tuple_tails_correct, we probably need
to do list induction to avoid overconstraining *)  

lemma list_prefix_eq_length [rule_format]:
  "\<forall> l2 ltot lsuf lsuf' .
      int (length l1) + int (length l2) = int (length ltot) \<longrightarrow>
      l1 @ l2 @ lsuf = ltot @ lsuf' \<longrightarrow>
      l1 @ l2 = ltot"
proof(induction l1)
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case 
    apply(clarsimp)
    apply(case_tac ltot; clarsimp)
    apply(auto)
    done
qed

(* is_head_and_tail.induct version *)
(* need an extra assumption to distinguish static signed-int case
from "real" dynamic header? *)

lemma abi_decode_dyn_tuple_tails_succeed [rule_format]:
"     
  (\<forall> heads head_types tails code pre1 pre2 post heads' tails' offset bytes vs_out bytes'.
       decode'_dyn_tuple_tails tails' (map abi_get_type vs) heads' offset (int (length(pre1)), pre1@pre2@code@post) = Ok (vs_out, bytes') \<longrightarrow>
    is_head_and_tail vs heads head_types tails \<longrightarrow>
       ht_wellbehaved tails' (map abi_get_type vs) heads' \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ code @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ code @ post) (int (length pre1) + offset)) \<longrightarrow>
       those (map2 ht_combine heads' (map (case_option None (\<lambda>t::int. Some (t - int (length pre1)))) tails')) = Some heads \<longrightarrow>
       map (\<lambda>x::int \<times> abi_value. fst x + int (length pre1)) tails = somes (tails') \<longrightarrow>
      (\<forall>vd::abi_value.
           vd \<in> set vs \<longrightarrow>
            (\<forall>(full_code::8 word list) start::int.
              can_encode_as vd full_code start \<longrightarrow>
              (\<exists>len::int. decode' (abi_get_type vd) (start, full_code) = Ok (vd, len)))) \<longrightarrow>
       vs_out = vs)
"
proof(induction vs)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
    apply(case_tac heads'; clarsimp)
    done
next
  case (Cons v vs)
  then show ?case
    apply(clarify)
    apply(simp del: decode'.simps)
    apply(case_tac tails'; (simp del: decode'.simps)?)
    apply(case_tac heads'; (simp del: decode'.simps)?)

(* static head *)
    apply(simp del: decode'.simps split:sum.splits option.splits prod.splits if_splits)
    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
  
    apply(rule_tac ?a1.0 = "(v # vs)"
                and ?a2.0 = "(x2 # z)"
                and ?a3.0 = head_types
                and ?a4.0 = tails
in is_head_and_tail.cases; (simp del: decode'.simps)?)
    apply(clarify)
    apply(simp del: decode'.simps)
    apply(case_tac aa; (simp del: decode'.simps)?)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
     apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

    apply(rule_tac
?a1.0 = "Vtuple (abi_get_type v # ts) (v#ys)" and ?a2.0 = " (pre1 @ pre2 @ code @ post)"
and ?a3.0 = "(int (length pre1) + int (length pre2))" 
in can_encode_as.cases;  (simp del: decode'.simps)?)
    apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
      apply(case_tac "encode_static v"; (simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)?)
      apply(clarify)
      apply(simp del: decode'.simps add:Let_def tuple_value_valid_aux_def split: if_split_asm sum.splits prod.splits)

      apply(subgoal_tac "pre = pre1 @ pre2")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre)")

     apply(drule_tac x = ys in spec) apply(drule_tac x = ts in spec)
     apply(drule_tac x = tailsa in spec)
     apply(drule_tac x = "concat x1b" in spec) apply(drule_tac x = pre1 in spec)
     apply(drule_tac x = "pre2@a" in spec)
    apply(drule_tac x = posta in spec)
     apply(drule_tac x = lista in spec)
     apply(drule_tac x = list in spec) apply(rotate_tac -1)
     apply(drule_tac x = offset in spec)
     apply(drule_tac x = x1a in spec)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

       apply(cut_tac v = " (Vtuple ts ys) " and code = "concat x1b" 
and pre = "pre1 @ pre2 @ a" and post = posta
in Estatic;
(simp del: decode'.simps)?)
    apply(simp add:tuple_value_valid_aux_def)

    apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
    apply(drule_tac lsuf = "code @ post" and lsuf' = "a @ concat x1b @ posta"
in list_prefix_eq_length; (simp del: decode'.simps)?)


    apply(clarify)
     apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
     apply(clarify)

     apply(drule_tac x = ys in spec) apply(drule_tac x = ts in spec)
     apply(drule_tac x = tailsa in spec)
     apply(drule_tac x = "code" in spec) apply(drule_tac x = pre1 in spec)
     apply(drule_tac x = "pre2" in spec)
    apply(drule_tac x = post in spec)
     apply(drule_tac x = lista in spec)
     apply(drule_tac x = list in spec) apply(rotate_tac -1)
     apply(drule_tac x = offset in spec)
     apply(drule_tac x = x1a in spec)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

     apply(case_tac "  t = abi_get_type v")
    apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

     apply(frule_tac ht = t in is_head_and_tail_head_types_elem;
(simp del: decode'.simps)?)


(* dynamic head *)
    apply(clarify)
    apply(simp del: decode'.simps)
    apply(case_tac aa; (simp del: decode'.simps)?)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

    apply(rule_tac ?a1.0 = "(v # vs)"
                and ?a2.0 = "(Vsint (256::nat) ab # z)"
                and ?a3.0 = head_types
                and ?a4.0 = "((ab, b) # zs)"
in is_head_and_tail.cases; (simp del: decode'.simps)?)
    apply(clarify)
    apply(simp del: decode'.simps)

    apply(rule_tac
?a1.0 = "(Vtuple (Tsint (256::nat) # ts) (Vsint (256::nat) ptr # ys))" and ?a2.0 = " (pre1 @ pre2 @ code @ post)"
and ?a3.0 = "(int (length pre1) + int (length pre2))" 
in can_encode_as.cases;  (simp del: decode'.simps)?)

    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

      apply(subgoal_tac "pre = pre1 @ pre2")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre)")
    apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

     apply(drule_tac x = ys in spec) apply(drule_tac x = ts in spec)
     apply(drule_tac x = tails in spec)
     apply(drule_tac x = "concat x1b" in spec) apply(drule_tac x = pre1 in spec)
     apply(drule_tac x = "pre2 @ word_rsplit (word_of_int ptr :: 256 word)" in spec)
    apply(drule_tac x = posta in spec)
     apply(drule_tac x = lista in spec)
     apply(drule_tac x = list in spec) apply(rotate_tac -1)
      apply(drule_tac x = "offset + x2a" in spec)
    apply(rotate_tac -1)
      apply(drule_tac x = x1c in spec)

    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

       apply(cut_tac v = " (Vtuple ts ys) " and code = "concat x1b" 
and pre = "pre1 @ pre2 @ word_rsplit (word_of_int ptr :: 256 word)" and post = posta
in Estatic;
(simp del: decode'.simps)?)
    apply(simp add:tuple_value_valid_aux_def)

      apply(drule_tac x = ptr in spec) apply(rotate_tac -1)
    apply(drule_tac x = v in spec)
    apply(clarify)

      apply(simp del: decode'.simps add:Let_def tuple_value_valid_aux_def split: if_split_asm sum.splits prod.splits)

      apply(drule_tac x = v in spec)
    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
      apply(drule_tac x = "(pre1 @ pre2 @ word_rsplit (word_of_int ptr :: 256 word) @ concat x1b @ posta)" in spec)
      apply(drule_tac x = " (int (length pre1) + ptr)" in spec)
    apply(clarify)
    apply(case_tac "x1a = v")
    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

    apply(subgoal_tac "int (length pre1) + ptr = ptr + int (length pre1)")
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
    apply(arith)

    apply(drule_tac lsuf = "code @ post" and lsuf' = "codea @ posta"
in list_prefix_eq_length; (simp del: decode'.simps)?)


    apply(clarify)

     apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
     apply(clarify)

     apply(drule_tac x = ys in spec) apply(drule_tac x = ts in spec)
     apply(drule_tac x = tails in spec)
     apply(drule_tac x = "code" in spec) apply(drule_tac x = pre1 in spec)
     apply(drule_tac x = "pre2" in spec)
    apply(drule_tac x = post in spec)
     apply(drule_tac x = lista in spec)
     apply(drule_tac x = list in spec) apply(rotate_tac -1)
      apply(drule_tac x = "offset + x2a" in spec)
    apply(rotate_tac -1)
      apply(drule_tac x = x1c in spec)

    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

     apply(case_tac "t = Tsint (256::nat)")
    apply(clarify)
    apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)
    apply(clarify)
     apply(frule_tac ht = t in is_head_and_tail_head_types_elem;
(simp del: decode'.simps)?)
    done
qed
(* 
how do we get to ac = vs?

*)
(*
lemma abi_decode_dyn_tuple_tails_succeed [rule_format]:
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
(\<forall> heads' tails' count' offset pre1 pre2 post l bytes.
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<longrightarrow>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length pre1) + offset)) \<longrightarrow>
those (map2 ht_combine heads' 
       (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
count' = heads_length vs + int (length pre2))"
*)
lemma abi_decode_succeed2 [rule_format]:
  "\<forall> full_code start . 
   can_encode_as v full_code start \<longrightarrow>
   (\<exists> len . decode' (abi_get_type v) (start, full_code) = Ok (v, len))"
proof(induction v)
  case (Vtuple ts vs) thus ?case
    apply(clarify)
    apply(simp del: decode'.simps)
    apply(rule_tac ?a1.0 = "(Vtuple ts vs)" and ?a2.0 = full_code and ?a3.0 = start
in can_encode_as.cases; (simp del:decode'.simps)?)

     defer (* static *)
     apply(clarsimp)     apply(rule_tac conjI)
      apply(clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
      apply(clarsimp)

      apply(atomize)
(*
      apply(drule_tac x = x in spec)
    apply(clarsimp)

    apply(frule_tac vd = x  and v = "(Vtuple (map abi_get_type vs) vs)" in
can_encode_as_tuple_split; simp?)
      apply(clarsimp)
*)
(*
      apply(drule_tac x = coded in spec) apply(rotate_tac -1) apply(drule_tac x = xa in spec)
      apply(clarsimp)
*)
      apply(simp add:Let_def)
    apply(rule_tac conjI)
       apply(simp add:list_ex_iff) apply(fastforce)

    apply(clarsimp)

      apply(case_tac "decode'_dyn_tuple_heads (map abi_get_type vs) (0::int) (starta, full_codea) ") apply(clarsimp)
         apply(rename_tac  newa)
       apply(case_tac "decode'_dyn_tuple_tails aa (map abi_get_type vs) a ab (starta, full_codea)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac can_encode_as_start; simp?)

           apply(subgoal_tac "int (min (length full_codea) (nat starta)) = starta")
    apply(subgoal_tac "starta > 0")
        apply(frule_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?l = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and count' = ab
and bytes = newa in abi_decode_dyn_tuple_heads_succeed; (simp del:decode'.simps)?)

          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
            apply(arith) apply(arith)

          apply(clarsimp)
    apply(cut_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?code = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and offset = "heads_length vs"
and bytes' = newa2 in abi_decode_dyn_tuple_tails_succeed; (simp del:decode'.simps)?)
           apply(subgoal_tac "int (min (length full_codea) (nat starta)) = starta")

          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
             apply(arith) apply(arith)
    apply(arith)


    apply(drule_tac x = vd in spec)
          apply(simp del:decode'.simps)
    apply(drule_tac x = full_code in spec) apply(rotate_tac -1)
apply(drule_tac x = start in spec)
          apply(simp del:decode'.simps) apply(clarify)
           apply(rule_tac x = len in exI)
    apply(simp add:Let_def)

    apply(frule_tac v = "(Vtuple head_types heads)" in can_encode_as_start; simp?)
           apply(clarsimp)

           apply(rule_tac conjI; clarsimp)
    apply(rule_tac conjI; clarsimp)

    apply(clarsimp)

    apply(simp add:Let_def)
    apply(clarsimp)

(*
           apply(subgoal_tac "abi_type_isstatic (abi_get_type (Vtuple head_types heads))")
    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
    apply(cut_tac v = "( (Vtuple head_types heads))" and 
code = code and pre = "[]" and post = post in Estatic; simp)
            apply(simp add:list_ex_iff)
           apply(clarsimp)apply(simp add:list_ex_iff) apply(clarsimp)

           apply(frule_tac ht = xb in is_head_and_tail_head_types_elem; simp) 

    apply(simp)

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
*)
end