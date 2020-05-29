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
    apply(arith)

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
| "ht_wellbehaved (None#ios) (t#ts) (Some vo#vos) =
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

lemma abi_decode_dyn_tuple_tails_fail [rule_format]:
"\<forall> ts heads offset ix code err .
 decode'_dyn_tuple_tails tails ts heads offset (ix, code) = Err err \<longrightarrow>
  ht_wellbehaved tails ts heads \<longrightarrow>
 (\<exists> offset' t err' .
    (Some offset', t) \<in> set (zip tails ts) \<and>
    decode' t (offset', code) = Err err')
 "
proof(induction tails)
  case Nil
  then show ?case 
    apply(clarify)
    apply(case_tac ts; case_tac heads; clarsimp)
    done
next
  case (Cons a tails)
  then show ?case
    apply(clarify)
    apply(case_tac ts; case_tac heads; simp del:decode'.simps)
    apply(rename_tac newa)
    apply(case_tac a; simp del:decode'.simps) apply(clarify)
     apply(case_tac aaa; simp del:decode'.simps) apply(clarify)
     apply(simp split:sum.splits prod.splits del:decode'.simps) apply(clarify)
     apply(blast)

    apply(clarify)
     apply(case_tac aaa; simp del:decode'.simps) apply(clarify)
    apply(simp split:sum.splits prod.splits del:decode'.simps) apply(clarify)
     apply(metis)

    apply(clarify)
    apply(metis)
    done
qed

lemma can_encode_as_start_nonneg :
  "can_encode_as v full_code offset \<Longrightarrow> 0 \<le> offset"
proof(induction rule:can_encode_as.induct; auto)
qed

fun ty_heads_length :: "(abi_type) list \<Rightarrow> int" where
"ty_heads_length [] = 0"
| "ty_heads_length (tyh#t) = 
    (if abi_type_isstatic tyh
        then abi_static_size tyh + ty_heads_length t
        else 32 + ty_heads_length t)"

lemma ty_heads_length_nonneg :
"0 \<le> ty_heads_length ts"
proof(induction ts)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case by (auto simp add:abi_static_size_nonneg)
qed

(* 2 failure cases
1. too few bytes to decode header
2. failure to decode some element *)
lemma abi_decode_dyn_tuple_heads_fail [rule_format]:
"\<forall>  heads_len ix code err .
 decode'_dyn_tuple_heads (ts) heads_len (ix, code) = Err err \<longrightarrow>
 0 \<le> ix \<longrightarrow>
 0 \<le> heads_len \<longrightarrow>
 nat ix + nat heads_len + ty_heads_length ts \<le> int (length code) \<longrightarrow>
 (\<exists> tpre tbad tpost err .
    ts = tpre @ [tbad] @ tpost \<and>
    (abi_type_isstatic tbad) \<and>
    (decode' tbad (nat ix + nat heads_len + ty_heads_length tpre, code) = Err err))
 "
proof(induction ts)
  case Nil
  then show ?case 
    apply(clarsimp)
    done
next
  case (Cons a tails)
  then show ?case
    apply(clarify)
    apply(simp del:decode'.simps add:Let_def )
      apply(case_tac "abi_type_isdynamic a"; simp del:decode'.simps)
    apply(case_tac "length code - nat (ix + heads_len) < (32::nat)"; simp del:decode'.simps)
       apply(clarify)
       apply(case_tac "0 \<le> ix"; simp del:decode'.simps)
       apply(cut_tac ts = tails in ty_heads_length_nonneg)
       apply(arith)

          apply(simp del:decode'.simps add:Let_def split:sum.splits prod.splits ; clarify?)
      apply(drule_tac x = "heads_len + 32" in spec)
      apply(drule_tac x = ix in spec)
    apply(drule_tac x = code in spec)
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps) 
      apply(clarify)
      apply(rule_tac x = "a#tpre" in exI)
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps)
      apply(rule_tac x = erra in exI)
      apply(subgoal_tac "(ix + (heads_len + (32::int)) + ty_heads_length tpre) =
(ix + heads_len + ((32::int) + ty_heads_length tpre))")
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps) 
      apply(arith)

          apply(simp del:decode'.simps add:Let_def split:sum.splits prod.splits ; clarify?)
    apply(case_tac "(0::int) \<le> abi_static_size a"; simp del:decode'.simps)
      apply(drule_tac x = "heads_len + abi_static_size a" in spec)
      apply(drule_tac x = ix in spec)
    apply(drule_tac x = code in spec)
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps) 
      apply(clarify)
      apply(rule_tac x = "a#tpre" in exI)
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps)
      apply(rule_tac x = erra in exI)
      apply(subgoal_tac "(ix + (heads_len + (abi_static_size a)) + ty_heads_length tpre) =
(ix + heads_len + ((abi_static_size a) + ty_heads_length tpre))")
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps) 
      apply(arith)

     apply(simp add:abi_static_size_nonneg)
    apply(rule_tac x = "[]" in exI) apply(rule_tac x = a in exI) 
      apply(simp add:nat_less_iff split:sum.splits prod.splits  del:decode'.simps) 
    done
  qed

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
    apply(clarify)
      apply(simp del: decode'.simps add:Let_def split: if_split_asm sum.splits prod.splits)

    apply(case_tac aa; (simp del: decode'.simps)?)
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

lemma is_head_and_tail_wellbehaved [rule_format]:
"is_head_and_tail vs heads head_types tails  \<Longrightarrow>
  (\<forall> aa a starta offset' t . 
       ht_wellbehaved aa (map abi_get_type vs) a \<longrightarrow>
  those (map2 ht_combine a (map (case_option None (\<lambda>t::int. Some (t - starta))) aa)) = Some heads \<longrightarrow>
       map (\<lambda>x::int \<times> abi_value. fst x + starta) tails = somes aa \<longrightarrow>
       ht_wellbehaved aa (map abi_get_type vs) a \<longrightarrow>
       (Some offset', t) \<in> set (zip aa (map abi_get_type vs)) \<longrightarrow>
       (\<exists> v . abi_get_type v = t \<and> (offset' - starta, v) \<in> set tails)) "
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case
    apply(auto)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case
    apply(clarsimp)
    apply(case_tac aa; clarsimp)
    apply(simp split:option.splits)
    apply(case_tac a; clarsimp)
    apply(simp split:option.splits)

     apply(case_tac aa; clarsimp)

    apply(case_tac a; clarsimp)
    apply(simp split:option.splits)
     apply(case_tac aa; clarsimp)
    done
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarsimp)
    apply(case_tac aa; clarsimp)
    apply(simp split:option.splits)
    apply(case_tac a; clarsimp)
    apply(simp split:option.splits)

     apply(case_tac aa; clarsimp)

    apply(case_tac a; clarsimp)
    apply(simp split:option.splits)
    apply(case_tac aa; clarsimp)

    apply(drule_tac x = list in spec)
    apply(drule_tac x = lista in spec)
    apply(clarsimp)
    apply(drule_tac x = starta in spec)
    apply(clarsimp)

    apply(case_tac "(Some offset', t) \<in> set (zip list (map abi_get_type xs))")
    apply(clarsimp)
     apply(drule_tac x = offset' in spec) apply(drule_tac x = t in spec) apply(clarsimp)
     apply(fastforce)

    apply(clarsimp)
    apply(rule_tac x = x in exI) apply(clarsimp)

    done
qed

lemma ty_heads_length_heads_length :
"ty_heads_length (map abi_get_type vs) =
  heads_length vs"
proof(induction vs; auto)
qed

lemma heads_length_heads [rule_format]:
  "\<forall> heads head_types tails .
  is_head_and_tail vs heads head_types tails \<longrightarrow>
   (\<forall> start code . can_encode_as (Vtuple head_types heads) code start \<longrightarrow>
      0 \<le> start \<longrightarrow>
      heads_length vs + start \<le> length code)"
proof(induction vs)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(rule_tac ?a1.0 = "[]" and ?a2.0 = heads and ?a3.0 = head_types and ?a4.0 = tails in is_head_and_tail.cases; simp?)
    apply(frule_tac can_encode_as_start; simp)
    done
next
  case (Cons v vs)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def)

    apply(rule_tac
?a1.0 = "(v # vs)"
and ?a2.0 = heads
and ?a3.0 = head_types
and ?a4.0 =tails
in is_head_and_tail.cases; clarsimp?)

     apply(drule_tac x = ys in spec)
     apply(drule_tac x = ts in spec)
    apply(subgoal_tac "Ex (is_head_and_tail vs ys ts)"; clarsimp?)

    apply(rule_tac
?a1.0 = "(Vtuple (abi_get_type v # ts) (v # ys))" and ?a2.0 = code and ?a3.0 = start
in can_encode_as.cases; simp?)
     apply(clarsimp)
     apply(case_tac "encode_static v"; clarsimp)
     apply(case_tac "those_err (map encode_static ys) "; clarsimp)
    apply(cut_tac v = "Vtuple ts ys" and code = "concat aa" and pre = "[]" and post = post
in Estatic; simp?)
      apply(simp add:tuple_value_valid_aux_def)
    apply(drule_tac x = "0" in spec)
    apply(drule_tac x = "(concat aa @ post)" in spec)
     apply(clarsimp)
     apply(frule_tac encode_static_size; simp?)

    apply(clarsimp)
    apply(case_tac "t = abi_get_type v"; clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
      apply(frule_tac head_types = ts and ht = t in is_head_and_tail_head_types_elem; simp?)

    apply(fastforce)
    apply(rule_tac
?a1.0 = "(Vtuple (Tsint (256::nat) # ts) (Vsint (256::nat) ptr # ys))"
and ?a2.0 = code and ?a3.0 = start
in can_encode_as.cases; simp?)
     apply(clarsimp)
      apply(simp add:tuple_value_valid_aux_def)
     apply(case_tac "those_err (map encode_static ys) "; clarsimp)
     apply(subgoal_tac "(int (length (word_rsplit (word_of_int ptr :: 256 word) :: 8 word list))) = 32")
      apply(clarsimp)
      apply(drule_tac x = ys in spec) apply(drule_tac x = "map abi_get_type ys" in spec)
      apply(subgoal_tac "Ex (is_head_and_tail vs ys (map abi_get_type ys))")
       apply(clarsimp)
    apply(cut_tac v = "Vtuple (map abi_get_type ys) ys" and code = "concat a" and pre = "[]" and post = post
in Estatic; simp?)
      apply(simp add:tuple_value_valid_aux_def)
    apply(drule_tac x = "0" in spec)
    apply(drule_tac x = "(concat a @ post)" in spec)
       apply(clarsimp)

      apply(fastforce)
     apply(simp add:sint_valid_length)

    apply(clarsimp)
    apply(case_tac " t = Tsint (256::nat)"; clarsimp)
      apply(frule_tac head_types = ts and ht = t in is_head_and_tail_head_types_elem; simp?)
    done
qed
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

lemma some_somes [rule_format]:
"\<forall> x . Some x \<in> set optl \<longrightarrow>
    x \<in> set (somes optl)"
proof(induction optl)
  case Nil
  then show ?case by auto
next
  case (Cons a optl)
  then show ?case 
    apply(clarsimp)
    apply(case_tac a; clarsimp)
    done
qed

lemma map_elem' [rule_format]:
  "\<forall> f x . x \<in> set (map f l) \<longrightarrow>
     (\<exists> x' . x' \<in> set l \<and> f x' = x)"
proof(induction l; auto)
qed

lemma encode_static_split_precise [rule_format]:
  "\<forall> v vs vpost full_code .
     vs = vpre @ [v] @ vpost \<longrightarrow>
    those_err (map encode_static vs) = Ok full_code \<longrightarrow>
    (\<exists> cpre cv cpost .
       those_err (map encode_static vpre) = Ok cpre \<and>
       encode_static v = Ok cv \<and>
       those_err (map encode_static vpost) = Ok cpost \<and>
       full_code = cpre @ [cv] @ cpost)"
proof(induction vpre)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(case_tac "encode_static v"; clarsimp)
    apply(case_tac "map encode_static vpost"; clarsimp)
    apply(simp split:sum.splits)
    done
next
  case (Cons a vs)
  then show ?case
    apply(clarsimp)
    apply(case_tac "encode_static a"; clarsimp)
apply(simp split:sum.splits)
    apply(clarsimp)
    apply(drule_tac x = v in spec) apply(drule_tac x = vpost in spec)
    apply(clarsimp)
    done
qed

lemma is_head_and_tail_heads_static_split_precise [rule_format] :
"is_head_and_tail (vs) heads head_types tails \<Longrightarrow> 
 (\<forall> vpre v vpost . vs = vpre @ v # vpost \<longrightarrow>
    list_all abi_value_valid vs \<longrightarrow>
    abi_type_isstatic (abi_get_type v) \<longrightarrow>
    (\<exists> hpre hpost .
       heads = hpre @ v # hpost \<and>
       length hpre = length vpre \<and>
       (\<forall> codes . those_err (map encode_static hpre) = Ok codes \<longrightarrow>
                  list_all abi_value_valid_aux heads \<longrightarrow>
                  length (concat codes) = heads_length vpre)))
"
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case
    apply(clarsimp)
    apply(case_tac vpre; clarsimp)
    apply(drule_tac x = list in spec)
    apply(auto)
    apply(rule_tac x = "x#hpre" in exI) apply(clarsimp)
    apply(case_tac "encode_static x"; clarsimp)
    apply(simp split:sum.splits)
    apply(clarsimp)
    apply(simp add:encode_static_size)
    done
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarsimp)
    apply(case_tac vpre; clarsimp)
    apply(drule_tac x = list in spec)
    apply(auto)
    apply(rule_tac x = "Vsint (256::nat) ptr#hpre" in exI) apply(clarsimp)
    apply(simp split:sum.splits)
    apply(clarsimp)
    apply(simp add:sint_valid_length)
    done
qed

lemma those_err_split [rule_format]:
  "\<forall> vs' out . those_err (vs @ vs') = Ok out \<longrightarrow>
    (\<exists> tvs tvs' . those_err vs = Ok tvs \<and> those_err vs' = Ok tvs' \<and>
       tvs @ tvs' = out)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
    apply(clarsimp)
    apply(case_tac a; clarsimp)
    apply(auto split:sum.splits)
    done
qed

lemma map_split_precise [rule_format] :
"\<forall> f xpre x xpost . map f xs = xpre @ x # xpost \<longrightarrow>
(\<exists> x'pre x' x'post .
    xs = x'pre @ x' # x'post \<and>
    length x'pre = length xpre \<and>
    length x'post = length xpost)"
proof(induction xs)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    apply(clarsimp)
    apply(case_tac xpre; clarsimp)
    apply(drule_tac x = f in spec)
    apply(drule_tac x =list in spec)
apply(drule_tac x =x in spec)
    apply(drule_tac x = xpost in spec)
    apply(clarsimp)
    apply(rule_tac x = "a#x'pre" in exI)
    apply(auto)
    done
qed

lemma my_replicate_map [rule_format]:
  "list_all (\<lambda> x . f x = y) l \<longrightarrow>
   map f l = replicate (length l) y"
proof(induction l; auto) qed


declare decode'.simps [simp del]
lemma abi_decode_succeed2 [rule_format]:
  "\<forall> full_code start . 
   can_encode_as v full_code start \<longrightarrow>
   (\<exists> len . decode' (abi_get_type v) (start, full_code) = Ok (v, len))"
proof(induction v)
  case (Vuint x1 x2)
  then show ?case 
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vsint x1 x2)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vaddr x)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vbool x)
  then show ?case 
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vfixed x1 x2 x3a)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
case (Vufixed x1 x2 x3a)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vfbytes x1 x2)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vfunction x1 x2)
  then show ?case
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps)
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
    done
next
  case (Vfarray x1 x2 x3a)
  then show ?case
  proof(cases "abi_type_isstatic x1")
    case True
    then show ?thesis using Vfarray
    apply(clarify)
    apply(drule_tac can_encode_as.cases; simp)
    apply(frule_tac prefix = pre and post = post in abi_encode_decode_static; simp del:decode_static.simps)
    apply(simp add:decode'.simps) 
    apply(clarify)
    apply(frule_tac encode_static_size) apply(simp)
    apply(simp)
      done
  next
    case False
    then show ?thesis using Vfarray
    apply(clarify)
    apply(simp)
    apply(rule_tac ?a1.0 = "(Vfarray x1 x2 x3a)" and ?a2.0 = full_code and ?a3.0 = start
in can_encode_as.cases; simp?)
       apply(clarsimp)


    
     apply(clarsimp)    
     apply(simp (no_asm_simp) add:decode'.simps)
      apply(simp add:farray_value_valid_aux_def)
      apply(clarsimp)

      apply(atomize)
      apply(simp add:Let_def)

      apply(case_tac "decode'_dyn_tuple_heads (replicate (length x3a) x1) (0::int) (starta, full_codea) ") apply(clarsimp)
         apply(rename_tac  newa)

           apply(subgoal_tac "int (min (length full_codea) (nat starta)) = starta")
    apply(subgoal_tac "starta \<ge> 0")
        apply(frule_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?l = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and count' = ab
and bytes = newa in abi_decode_dyn_tuple_heads_succeed; (simp)?)

      apply(simp add:my_replicate_map)


          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
            apply(arith) apply(arith)

       apply(case_tac "decode'_dyn_tuple_tails aa (replicate (length x3a) x1) a ab (starta, full_codea)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac can_encode_as_start; simp?)

    apply(cut_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?code = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and offset = "heads_length x3a"
and bytes' = newa2 in abi_decode_dyn_tuple_tails_succeed; (simp)?)

      apply(simp add:my_replicate_map)

          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
           apply(arith) apply(arith)

       apply(case_tac "decode'_dyn_tuple_tails aa (replicate (length x3a) x1) a ab (starta, full_codea)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac can_encode_as_start; simp?)


    apply(clarsimp)

         apply(frule_tac abi_decode_dyn_tuple_tails_fail) 
      apply(simp add:my_replicate_map)
          apply(clarsimp)
    apply(frule_tac offset' = offset' and t = t and aa = aa and a = a and starta = starta in
is_head_and_tail_wellbehaved; simp?) apply(simp add:my_replicate_map)
         apply(clarsimp)
         apply(drule_tac x = "offset' - starta" in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
         apply(frule_tac offset = "offset' - starta" and x = v in is_head_and_tail_tails_elem; simp?)
         apply(clarsimp)
         apply(drule_tac x = v in spec) apply(clarsimp)
         apply(drule_tac x = full_codea in spec) apply(drule_tac x = offset' in spec)
    apply(clarsimp)

        apply(simp add:can_encode_as_start_nonneg)
    apply(frule_tac can_encode_as_start)
       apply(frule_tac can_encode_as_start_nonneg)
       apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map (abi_static_size \<circ> abi_get_type) x3a)")
        apply(arith)
       apply(cut_tac l = "(map (abi_static_size \<circ> abi_get_type) x3a)" in list_nonneg_sum)
        apply(simp add:list_nonneg_def)
        apply(simp add:list_all_iff abi_static_size_nonneg) apply(simp add:list_sum_def)


    apply(frule_tac abi_decode_dyn_tuple_heads_fail; simp?)
        apply(simp add:can_encode_as_start_nonneg)
       apply(simp add:can_encode_as_start_nonneg)

      apply(subgoal_tac "replicate (length x3a) x1 = map abi_get_type x3a")

       apply(simp add:ty_heads_length_heads_length)

           apply(subgoal_tac "abi_type_isstatic (abi_get_type (Vtuple head_types heads))")
    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
         apply(clarsimp)
         apply(frule_tac heads_length_heads; simp?) apply(simp)
         apply(simp)
        apply(frule_tac heads_length_heads; simp?)
    apply(simp add:can_encode_as_start_nonneg)
        apply(simp)

       apply(clarsimp) apply(simp add:list_ex_iff) apply(clarsimp)

       apply(frule_tac ht = x in is_head_and_tail_head_types_elem; simp) 

      apply(simp add:my_replicate_map)

      apply(clarsimp)

      apply(simp add: can_encode_as_start_nonneg)

     apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
        apply(clarsimp)

       apply(simp split:sum.splits)

      apply(subgoal_tac "tbad = x1"; clarsimp)
       apply(simp add:list_all_iff)

       apply(subgoal_tac "set (replicate (length x3a) x1) = set (tpre @ tbad # tpost)")
      apply(thin_tac "replicate (length x3a) x1 = tpre @ tbad # tpost")
        apply(clarsimp) apply(simp add:set_replicate_conv_if)
      apply(case_tac x3a; clarsimp)

       apply(simp)

      apply(subgoal_tac "tbad = x1"; clarsimp)
       apply(simp add:list_all_iff)

       apply(subgoal_tac "set (replicate (length x3a) x1) = set (tpre @ tbad # tpost)")
      apply(thin_tac "replicate (length x3a) x1 = tpre @ tbad # tpost")
        apply(clarsimp) apply(simp add:set_replicate_conv_if)
      apply(case_tac x3a; clarsimp)

       apply(simp)
      done
  qed
next

  case (Vtuple ts vs) thus ?case
    apply(clarify)
    apply(simp)
    apply(rule_tac ?a1.0 = "(Vtuple ts vs)" and ?a2.0 = full_code and ?a3.0 = start
in can_encode_as.cases; simp?)

     (* static *)
     apply(clarsimp)

     apply(simp split:sum.splits)

    apply(cut_tac v = "(Vtuple ts vs)"
and code = code
in encode_static_size; simp)


    apply(cut_tac v = "(Vtuple ts vs)"
and code = code
and prefix = pre and post = post
in abi_encode_decode_static; simp del:decode_static.simps)

     apply(simp (no_asm_simp) add:decode'.simps del:decode_static.simps)

    (* dynamic *)
     apply(clarsimp)    
     apply(simp (no_asm_simp) add:decode'.simps)
      apply(simp add:tuple_value_valid_aux_def)
      apply(clarsimp)

      apply(atomize)
      apply(simp add:Let_def)
    apply(rule_tac conjI)
       apply(simp add:list_ex_iff) apply(fastforce)

    apply(clarsimp)

      apply(case_tac "decode'_dyn_tuple_heads (map abi_get_type vs) (0::int) (starta, full_codea) ") apply(clarsimp)
         apply(rename_tac  newa)

           apply(subgoal_tac "int (min (length full_codea) (nat starta)) = starta")
    apply(subgoal_tac "starta \<ge> 0")
        apply(frule_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?l = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and count' = ab
and bytes = newa in abi_decode_dyn_tuple_heads_succeed; (simp)?)

          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
            apply(arith) apply(arith)

       apply(case_tac "decode'_dyn_tuple_tails aa (map abi_get_type vs) a ab (starta, full_codea)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac can_encode_as_start; simp?)

    apply(cut_tac
?pre1.0 = "take(nat starta) full_codea" and ?pre2.0 = "[]"
and ?code = "drop (nat starta) full_codea"
and post = "[]"
and heads' = a
and tails' = aa
and offset = "heads_length vs"
and bytes' = newa2 in abi_decode_dyn_tuple_tails_succeed; (simp)?)

          apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
           apply(subgoal_tac "starta + offset = offset + starta")
           apply(arith) apply(arith)

       apply(case_tac "decode'_dyn_tuple_tails aa (map abi_get_type vs) a ab (starta, full_codea)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac can_encode_as_start; simp?)


    apply(clarsimp)

         apply(frule_tac abi_decode_dyn_tuple_tails_fail) apply(clarsimp)
         apply(clarsimp)
    apply(frule_tac offset' = offset' and t = t and aa = aa and a = a and starta = starta in
is_head_and_tail_wellbehaved; simp?)
         apply(clarsimp)
         apply(drule_tac x = "offset' - starta" in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec) apply(clarsimp)
         apply(frule_tac offset = "offset' - starta" and x = v in is_head_and_tail_tails_elem; simp?)
         apply(clarsimp)
         apply(drule_tac x = v in spec) apply(clarsimp)
         apply(drule_tac x = full_codea in spec) apply(drule_tac x = offset' in spec)
    apply(clarsimp)

        apply(simp add:can_encode_as_start_nonneg)
    apply(frule_tac can_encode_as_start)
       apply(frule_tac can_encode_as_start_nonneg)
       apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map (abi_static_size \<circ> abi_get_type) vs)")
        apply(arith)
       apply(cut_tac l = "(map (abi_static_size \<circ> abi_get_type) vs)" in list_nonneg_sum)
        apply(simp add:list_nonneg_def)
        apply(simp add:list_all_iff abi_static_size_nonneg) apply(simp add:list_sum_def)


    apply(frule_tac abi_decode_dyn_tuple_heads_fail; simp?)
        apply(simp add:can_encode_as_start_nonneg)
       apply(simp add:can_encode_as_start_nonneg)

       apply(simp add:ty_heads_length_heads_length)

           apply(subgoal_tac "abi_type_isstatic (abi_get_type (Vtuple head_types heads))")
    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
         apply(clarsimp)
         apply(frule_tac heads_length_heads; simp?) apply(simp)
         apply(simp)
        apply(frule_tac heads_length_heads; simp?)
    apply(simp add:can_encode_as_start_nonneg)
        apply(simp)

       apply(clarsimp) apply(simp add:list_ex_iff) apply(clarsimp)

       apply(frule_tac ht = xb in is_head_and_tail_head_types_elem; simp) 

      apply(clarsimp)

      apply(simp add: can_encode_as_start_nonneg)

     apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
        apply(clarsimp)

       apply(simp split:sum.splits)

    apply(subgoal_tac 
"\<exists> vpre vbad vpost .
vs = vpre @ vbad # vpost \<and>
length tpre = length vpre \<and>
length tpost = length vpost")
        apply(clarsimp)

    apply(drule_tac x = vbad in spec; clarsimp)

        apply(drule_tac
vpre = vpre
and v = vbad 
and vpost = vpost in is_head_and_tail_heads_static_split_precise; simp?)
         apply(simp add:tuple_value_valid_aux_def)
         apply(clarsimp)
         apply(simp add:list_all_iff)
        apply(clarsimp)
        apply(drule_tac those_err_split; clarsimp)
        apply(case_tac "encode_static vbad"; clarsimp)
        apply(simp split:sum.splits)
    apply(clarsimp)
    apply(cut_tac  v = vbad and code = a
and pre = "pre @ concat tvs"
and post = "concat x1 @ post"

in Estatic; simp)

        apply(drule_tac x = "(pre @ concat tvs @ a @ concat x1 @ post)" in spec)
    apply(rotate_tac -1)
        apply(drule_tac x = "(int (length pre) + heads_length vpre)" in spec)
        apply(clarsimp)
        apply(simp add:ty_heads_length_heads_length)

       apply(clarsimp)
       apply(drule_tac map_split_precise; clarsimp)
       apply(metis)

     apply(drule_tac ht = t in is_head_and_tail_head_types_elem; clarsimp)

    done
next
  (* problem with count in
bytes case

need to make sure that count is not empty
and actually contains the encoding
of the offset


*)
  case (Vbytes x)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; simp del:pad_bytes.simps)
     apply(clarify) apply(simp)

    apply(frule_tac can_encode_as.cases; simp del:pad_bytes.simps)

    apply(clarify)

    apply(simp add:bytes_value_valid_def del:pad_bytes.simps)
    apply(simp add:decode'.simps Let_def
del:pad_bytes.simps skip_padding.simps decode_uint.simps take_append
)

(*
    apply(subgoal_tac "int (length codea) + int (length posta) < decode_uint (take (32::nat) (codea @ posta)) + (32::int)")
*)

     apply(clarify)
    apply(frule_tac uint_valid_length)
     apply(simp del:decode_uint.simps)
    apply(frule_tac uint_reconstruct_valid; simp)
     apply(frule_tac uint_reconstruct; simp)
     apply(rotate_tac -1)
    apply(frule_tac uint_valid_length)
     apply(simp del:decode_uint.simps)
     apply(simp add:uint_valid_length)
    apply(simp split:prod.splits option.splits)
    apply(clarsimp)
    apply(case_tac x2; clarsimp)
    apply(arith)
    done
  next
case (Vstring x)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; simp del:pad_bytes.simps)
     apply(clarify) apply(simp)

    apply(drule_tac can_encode_as.cases; simp del:pad_bytes.simps)
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; simp del:pad_bytes.simps)

    apply(clarify)

    apply(simp add:string_value_valid_def bytes_value_valid_def del:pad_bytes.simps)
    apply(simp add:decode'.simps Let_def
del:pad_bytes.simps skip_padding.simps decode_uint.simps take_append
)

     apply(clarify)
    apply(frule_tac uint_valid_length)
     apply(simp del:decode_uint.simps)
    apply(frule_tac uint_reconstruct_valid; simp)
     apply(frule_tac uint_reconstruct; simp)
     apply(rotate_tac -1)
    apply(frule_tac uint_valid_length)
     apply(simp del:decode_uint.simps)
     apply(simp add:uint_valid_length)
    apply(simp split:prod.splits option.splits)
    apply(clarsimp)


    apply(subgoal_tac
"((\<lambda>b::8 word. char_of_integer (of_int (uint b))) \<circ>
            (\<lambda>c::char. word_of_int (int_of_integer (integer_of_char c)))) =
id")

     apply(case_tac x2; clarsimp)
    apply(arith)

    apply(subgoal_tac "\<forall> c .
char_of_integer (of_int (uint (word_of_int (int_of_integer (integer_of_char c)) :: 8 word)))
= c") 
    apply(rule_tac funext)
      apply(clarsimp)


    apply(clarsimp)
      apply(simp add:word_of_int char_of_integer_def integer_of_char_def
uint_word_of_int)
      apply(cut_tac x = "of_char c" and xa = 256 in modulo_integer.rep_eq)
    apply(clarsimp)
    done
next
  case (Varray x1 x2)
  then show ?case
    apply(clarify)
    apply(simp)
    apply(rule_tac ?a1.0 = "(Varray x1 x2)" and ?a2.0 = full_code and ?a3.0 = start
in can_encode_as.cases; simp?)
       apply(clarsimp)


    
     apply(clarsimp)    
     apply(simp (no_asm_simp) add:decode'.simps)
      apply(simp add:array_value_valid_aux_def)
      apply(clarsimp)

      apply(atomize)
    apply(simp add:Let_def)

    apply(drule_tac ?a1.0 = " (Vuint (256::nat) (int (length x2)))" in can_encode_as.cases; simp?)
         apply(clarsimp)
         apply(simp add:uint_valid_length)


    apply(subgoal_tac
"nat (uint (word_rcat (word_rsplit (word_of_int (int (length x2)) :: 256 word) :: 8 word list) :: 256 word)) = length x2")
          apply(rotate_tac -1)

      apply(case_tac "decode'_dyn_tuple_heads (replicate (nat (uint (word_rcat (word_rsplit (word_of_int (int (length x2)) :: 256 word) :: 8 word list) :: 256 word))) x1) (0::int)
                 (int (length pre) + (32::int), pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word) @ post)")
      apply(clarify)
    apply(clarsimp)
     apply(rename_tac  newa)

    apply(simp add:uint_valid_length)


        apply(frule_tac
?pre1.0 = " pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word)" and ?pre2.0 = "[]"
and ?l = "post"
and post = "[]"
and heads' = a
and tails' = aa
and count' = ab
and bytes = newa in abi_decode_dyn_tuple_heads_succeed; (simp)?)

         apply(simp add:my_replicate_map)
         apply(simp add:uint_valid_length)
         apply(simp add:uint_valid_length)


        apply(drule_tac x = offset in spec)
        apply(rotate_tac -1)
        apply(drule_tac x = v in spec)
       apply(clarsimp)
         apply(simp add:uint_valid_length)
    
       apply(subgoal_tac "(offset + int (length pre) + (32::int)) = (int (length pre) + (32::int) + offset)" )
    apply(clarsimp)
        apply(arith)

       apply(case_tac "decode'_dyn_tuple_tails aa
                   (replicate (length x2) x1) a (heads_length x2)
                   (int (length pre) + (32::int), pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word) @ post)") apply(clarsimp)
        apply(rename_tac  newa2)
    apply(frule_tac v = "(Vtuple head_types heads)" in can_encode_as_start; simp?)
         apply(simp add:uint_valid_length)


    apply(cut_tac
?pre1.0 = "pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word)" and ?pre2.0 = "[]"
and ?code = "post"
and post = "[]"
and heads' = a
and tails' = aa
and offset = "heads_length x2"
and bytes' = newa2 in abi_decode_dyn_tuple_tails_succeed; (simp add:uint_valid_length my_replicate_map)?)

        apply(drule_tac x = offset in spec)
        apply(rotate_tac -1)
        apply(drule_tac x = v in spec)
       apply(subgoal_tac "(offset + int (length pre) + (32::int)) = (int (length pre) + (32::int) + offset)" )
    apply(clarsimp)
        apply(arith)

          apply(simp add:my_replicate_map)

 
         apply(frule_tac abi_decode_dyn_tuple_tails_fail) 
       apply(simp add:my_replicate_map)
         apply(simp add:uint_valid_length)
          apply(clarsimp)
    apply(frule_tac offset' = offset' and t = t and aa = aa and a = a and starta = "(int (length pre) + (32::int))" in
is_head_and_tail_wellbehaved; (simp add:my_replicate_map uint_valid_length)?)

         apply(clarsimp)
      apply(drule_tac x = "offset' - (int (length pre) + (32::int))" in spec) apply(rotate_tac -1) 
      apply(drule_tac x = v in spec) apply(clarsimp)
         apply(frule_tac offset = "offset' - (int (length pre) + (32::int))" and x = v in is_head_and_tail_tails_elem; simp?)
         apply(clarsimp)
         apply(drule_tac x = v in spec) apply(clarsimp)
         apply(drule_tac x = "(pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word) @ post)" in spec) apply(drule_tac x = offset' in spec)
    apply(clarsimp)

(*
        apply(simp add:can_encode_as_start_nonneg)
    apply(frule_tac can_encode_as_start)
       apply(frule_tac can_encode_as_start_nonneg)
       apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map (abi_static_size \<circ> abi_get_type) x3a)")
        apply(arith)
       apply(cut_tac l = "(map (abi_static_size \<circ> abi_get_type) x3a)" in list_nonneg_sum)
        apply(simp add:list_nonneg_def)
        apply(simp add:list_all_iff abi_static_size_nonneg) apply(simp add:list_sum_def)
*)

     apply(frule_tac abi_decode_dyn_tuple_heads_fail; simp?)
      apply(simp add:my_replicate_map uint_valid_length)
      apply(cut_tac f = "abi_get_type" and l = x2 and y = x1 in my_replicate_map) apply(simp)
    apply(rotate_tac -1) apply(drule_tac sym) apply(simp)
       apply(simp add:ty_heads_length_heads_length)


(*
           apply(subgoal_tac "abi_type_isstatic (abi_get_type (Vtuple head_types heads))")
    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = full_codea and ?a3.0 = starta
in can_encode_as.cases; simp)
         apply(clarsimp)
         apply(frule_tac heads_length_heads; simp?) apply(simp)
         apply(simp)
        apply(frule_tac heads_length_heads; simp?)
    apply(simp add:can_encode_as_start_nonneg)
        apply(simp)
*)

           apply(subgoal_tac "abi_type_isstatic (abi_get_type (Vtuple head_types heads))")
    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = "(pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word) @ post)"
 and ?a3.0 = "(int (length pre) + (32::int))"
in can_encode_as.cases; simp)
         apply(clarsimp)
         apply(frule_tac heads_length_heads; simp?) apply(simp)
         apply(simp)
        apply(frule_tac heads_length_heads; simp?)
    apply(simp add:can_encode_as_start_nonneg)
        apply(simp add: uint_valid_length)
        apply(subgoal_tac "code  @ posta = post") apply(clarsimp)
    apply(simp add: append_eq_append_conv_if) apply(clarsimp)
        apply(simp add: uint_valid_length)

    apply(clarsimp)
       apply(simp add:list_ex_iff) apply(clarsimp)
apply(simp add:list_ex_iff) apply(clarsimp)

       apply(frule_tac ht = x in is_head_and_tail_head_types_elem; simp) 


     apply(clarsimp)


    apply(rule_tac ?a1.0 = "(Vtuple head_types heads)"
and ?a2.0 = "(pre @ word_rsplit (word_of_int (int (length x2)) :: 256 word) @ post)"
 and ?a3.0 = "(int (length pre) + (32::int))"
in can_encode_as.cases; simp)
    apply(clarsimp)
      apply(simp split:sum.splits)

      apply(cut_tac f = "abi_get_type" and l = x2 and y = x1 in my_replicate_map) apply(simp)
    apply(rotate_tac -1) apply(drule_tac sym) apply(simp)

    apply(subgoal_tac 
"\<exists> vpre vbad vpost .
x2 = vpre @ vbad # vpost \<and>
length tpre = length vpre \<and>
length tpost = length vpost")
        apply(clarsimp)

    apply(drule_tac x = vbad in spec; clarsimp)

        apply(drule_tac
vpre = vpre
and v = vbad 
and vpost = vpost in is_head_and_tail_heads_static_split_precise; simp?)
         apply(simp add:tuple_value_valid_aux_def)
    apply(clarsimp)
        apply(simp add:list_all_iff)
    apply(clarsimp)

        apply(drule_tac those_err_split; clarsimp)
        apply(case_tac "encode_static vbad"; clarsimp)
        apply(simp split:sum.splits)
    apply(clarsimp)
    apply(cut_tac  v = vbad and code = a
and pre = "prea @ concat tvs"
and post = "concat x1a @ posta"

in Estatic; simp)

        apply(drule_tac x = "(prea @ concat tvs @ a @ concat x1a @ posta)" in spec)
    apply(rotate_tac -1)
        apply(drule_tac x = "(int (length prea) + heads_length vpre)" in spec)
        apply(clarsimp)
         apply(simp add:ty_heads_length_heads_length)



       apply(clarsimp)
       apply(drule_tac map_split_precise; clarsimp)
       apply(metis)

     apply(drule_tac ht = t in is_head_and_tail_head_types_elem; clarsimp)

    apply(frule_tac uint_reconstruct_valid; simp?)
    apply(frule_tac uint_reconstruct; simp?)
    apply(simp add:uint_valid_length)
    done
qed

(* should be easy to prove, decode just checks if abi_type_valid. *)
lemma abi_decode_correct :
  "can_encode_as v full_code 0 \<Longrightarrow>
   decode (abi_get_type v) full_code = Ok v"
  apply(frule_tac encode_correct_converse_valid)
  apply(simp)
  apply(clarify)
  apply(frule_tac abi_decode_succeed2)
  apply(clarsimp)
  done

(*
lemma my_abi_type_induct :
  assumes Huint : "(\<And> n . P1 (Tuint n))"
  and Hsint : "(\<And> n . P1 (Tsint n))"
  and Haddr : "(P1 (Taddr))"
  and Hbool : "(P1 (Tbool))"
  and Hfixed : "(\<And> m n . P1 (Tfixed m n))"
  and Hufixed : "(\<And> m n . P1 (Tufixed m n))"
  and Hfbytes : "(\<And> n . P1 (Tfbytes n))"
  and Hfunction : "(P1 (Tfunction))"
  and Hfarray : "(\<And> t n . P2 (replicate n t) \<Longrightarrow> P1 (Tfarray t n))"
  and Htuple : "(\<And> ts . P2 ts \<Longrightarrow> P1 (Ttuple ts))"
  and Hbytes : "(P1 (Tbytes))"
  and Hstring : "(P1 (Tstring))"
  and Harray : "(\<And> t n . P2 (replicate n t)  \<Longrightarrow> P1 (Tarray t))"
  and Hln : "P2 []"
  and Hlc : "(\<And> t l . P1 t \<Longrightarrow> P2 l \<Longrightarrow>  P2 (t # l))"
shows "P1 v \<and> P2 l"
proof-
  {fix v :: abi_type
    have "P1 v \<and> (\<forall> t n . v = Tfarray t n \<longrightarrow> P2 (replicate n t))
               \<and> (\<forall> ts . v = Ttuple ts \<longrightarrow> P2 ts)
               \<and> (\<forall> t n . v = Tarray t \<longrightarrow> P2 (replicate n t))"
    proof(induction v)
      case (Tuint x)
      then show ?case using Huint by auto next
    next
      case (Tsint x)
      then show ?case using Hsint by auto next
    next
      case Taddr
      then show ?case using Haddr by auto next
    next
      case Tbool
      then show ?case using Hbool by auto next
    next
      case (Tfixed x1a x2a)
      then show ?case using Hfixed by auto next
    next
      case (Tufixed x1a x2a)
      then show ?case using Hufixed by auto next
    next
      case (Tfbytes x)
      then show ?case using Hfbytes by auto next
    next
      case Tfunction
      then show ?case using Hfunction by auto next
next
  case (Tfarray x1 x2)
  then show ?case using Hfarray
    apply(clarsimp)
  proof(induct x1)
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
*)

lemma abi_decode_static_type_ok [rule_format]:
  "\<forall> index (full_code :: 8 word list) v .
      decode_static t (index, full_code) = Ok v \<longrightarrow>
      abi_get_type v = t"
proof(induction t)
case (Tuint x)
  then show ?case 
    apply(simp add:Let_def split:if_splits)
    done
next
  case (Tsint x)
  then show ?case
    apply(simp add:Let_def split:if_splits)
    done
next
  case Taddr
  then show ?case 
    apply(simp add:Let_def split:if_splits)
    done
next
  case Tbool
  then show ?case
    apply(simp add:Let_def split:if_splits)
    done
next
  case (Tfixed x1a x2a)
  then show ?case
    apply(simp add:Let_def split:if_splits)
    done
next
  case (Tufixed x1a x2a)
  then show ?case 
    apply(simp add:Let_def split:if_splits)
    done
next
  case (Tfbytes x)
  then show ?case
    apply(simp add:Let_def split:if_splits)
    done
next
  case Tfunction
  then show ?case
    apply(simp add:Let_def split:if_splits)
    done
next
  case (Tfarray t x2a)
  then show ?case
    apply(simp add:Let_def split:if_splits sum.splits)
    done
next
  case (Ttuple x)
  then show ?case 
    apply(simp add:Let_def split:if_splits sum.splits)
    done
next
  case Tbytes
  then show ?case 
    apply(simp add:Let_def split:if_splits sum.splits)
    done
next
  case Tstring
  then show ?case
    apply(simp add:Let_def split:if_splits sum.splits)
    done
next
  case (Tarray t)
  then show ?case
    apply(simp add:Let_def split:if_splits sum.splits)
    done
qed

lemma abi_decode'_type_ok [rule_format]:
  "\<forall> index (full_code :: 8 word list) v sz.
      decode' t (index, full_code) = Ok (v, sz) \<longrightarrow>
      abi_get_type v = t"
proof(induction t)
case (Tuint x)
  then show ?case 
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case (Tsint x)
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case Taddr
  then show ?case 
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case Tbool
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case (Tfixed x1a x2a)
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case (Tufixed x1a x2a)
  then show ?case 
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case (Tfbytes x)
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case Tfunction
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits)
    done
next
  case (Tfarray t x2a)
  then show ?case
     apply(simp add:Let_def decode'.simps split:if_splits sum.splits)
    done
next
  case (Ttuple x)
  then show ?case 
    apply(simp add:Let_def decode'.simps split:if_splits sum.splits)
    done
next
  case Tbytes
  then show ?case 
    apply(simp add:Let_def decode'.simps split:if_splits sum.splits)
    done
next
  case Tstring
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits sum.splits)
    done
next
  case (Tarray t)
  then show ?case
    apply(simp add:Let_def decode'.simps split:if_splits sum.splits)
    done
qed


lemma abi_decode_encode_static' [rule_format]:
  "(\<forall> t index (full_code :: 8 word list) . 
    abi_type_valid t \<longrightarrow>
    0 \<le> index \<longrightarrow>
    nat index + nat (abi_static_size t) \<le> length full_code \<longrightarrow>
    decode_static t (index, full_code) = Ok v \<longrightarrow>
    abi_get_type v = t \<longrightarrow>
   (abi_value_valid v \<and>
   (\<exists> (code :: 8 word list) . encode_static v = Ok code \<and>
       take (nat (abi_static_size t)) (drop (nat index) full_code) = code))) \<and>
    (
      (\<forall> v t n index full_code  .
          v = (Vfarray t n vs) \<longrightarrow>
                  abi_type_valid t \<longrightarrow>
                  0 \<le>  index \<longrightarrow>
                  nat index + nat (n * abi_static_size t) \<le> length full_code \<longrightarrow>
                  decode_static_tup (replicate n t) (index, full_code) = Ok vs \<longrightarrow>
                  map abi_get_type vs = replicate n t \<longrightarrow>
                  (list_all abi_value_valid vs \<and>
                  (\<exists> (codes :: 8 word list list) . those_err (map encode_static vs) = Ok codes \<and>
                           take (nat (n * (abi_static_size t))) (drop (nat index) full_code) = concat codes))) \<and>
      (\<forall> v ts  index full_code  .
          v = (Vtuple ts vs) \<longrightarrow>
                  list_all abi_type_valid ts \<longrightarrow>
                  0 \<le> index \<longrightarrow>
                  nat index + nat (list_sum (map abi_static_size ts)) \<le> length full_code \<longrightarrow>
                  decode_static_tup (ts) (index, full_code) = Ok vs \<longrightarrow>
                  map abi_get_type vs = ts \<longrightarrow>
                  (list_all abi_value_valid vs \<and>
                  (\<exists> (codes :: 8 word list list) . those_err (map encode_static vs) = Ok codes \<and>
                           take (nat (list_sum (map abi_static_size ts))) (drop (nat index) full_code) = concat codes)))
    )"
proof(induction rule:my_abi_value_induct)
(* Vuint *)
case (1 x1 x2)
  then show ?case
    apply(clarsimp)
    apply(simp add: Let_def split: if_split_asm)
    apply(clarsimp)
    apply(rule_tac sym)
    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
(* Vsint *)
  case (2 x1 x2)
  then show ?case 
    apply(clarsimp)
    apply(simp add: Let_def split: if_split_asm)
    apply(clarsimp)

    apply(rule_tac sym)
    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
(* Vaddr *)
  case (3 x)
  then show ?case
    apply(clarsimp)
    apply(simp add: Let_def split: if_split_asm)
    apply(clarsimp)

    apply(rule_tac sym)
    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
  case (4 x)
  then show ?case
    apply(clarsimp)
    apply(simp add: bool_value_valid_def Let_def split: if_split_asm)

     apply(drule_tac word_uint.Rep_inverse')
    apply(simp)
    apply(subgoal_tac
" word_rsplit (word_rcat (take (32::nat) (drop (nat index) full_code))::256 word) = take (32::nat) (drop (nat index) full_code)")

    apply(simp)

    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    

     apply(drule_tac word_uint.Rep_inverse')
    apply(simp)
    apply(subgoal_tac
" word_rsplit (word_rcat (take (32::nat) (drop (nat index) full_code))::256 word) = take (32::nat) (drop (nat index) full_code)")

    apply(simp)

    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
(* Vfixed *)
  case (5 m n r)
  then show ?case 
    apply(clarsimp)
    apply(simp add: Let_def split: if_split_asm)
    apply(clarsimp)
    apply(simp add:Rat.quotient_of_int)
    apply(rule_tac sym)
    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
(* Vufixed *)
  case (6 m n r)
  then show ?case 
    apply(clarsimp)
    apply(simp add: Let_def split: if_split_asm)
    apply(clarsimp)
    apply(simp add:Rat.quotient_of_int)
    apply(rule_tac sym)
    apply(rule_tac word_rsplit_rcat_size)
    apply(simp)
    apply(simp add:min_absorb2)
    apply(simp add:word_size)    
    done
next
(* Fbytes *)
  case (7 n bs)
  then show ?case
    apply(clarsimp)
    apply(simp add: Let_def fbytes_value_valid_def split: if_split_asm)
    apply(clarify)
    apply(simp del:pad_bytes.simps)

    apply(simp split:prod.splits del:pad_bytes.simps)
    apply(case_tac x2) 
     apply(subgoal_tac "n = 32") apply(clarsimp)
    apply(simp add:divmod_nat_def; clarsimp)
     apply(fastforce)

    apply(clarsimp)
    apply(rule_tac sym)
    apply(simp add: append_eq_conv_conj) 
    apply(rule_tac conjI) 
     apply(subgoal_tac "min n (32 :: nat) = n") apply(clarsimp)
     apply(arith)
    apply(simp add:divmod_nat_def; clarsimp)

    apply(subgoal_tac "n = Suc nata")
     apply(simp)

    apply(cut_tac k = n and l = 32 in int_mod_eq')
      apply(simp)
    apply(case_tac "n = 32"; clarsimp)
    apply(simp)
    done
next
  (* function *)
  case 8
  then show ?case sorry
next
  (* Farray *)
  case (9 t n l)
  then show ?case
    apply(clarsimp)
    apply(rotate_tac 1) apply(drule_tac mythin) apply(clarsimp)
    apply(simp split:sum.splits if_split_asm)
    apply(clarsimp)
    apply(simp add:farray_value_valid_aux_def; clarsimp)
    apply(drule_tac x = t in spec)
    apply(clarsimp)
    apply(drule_tac x = "length l" in spec)
    apply(drule_tac x = index in spec) apply(clarsimp)
    apply(drule_tac x = full_code in spec)
    apply(clarsimp)
    apply(simp add:list_all_iff)
    apply(subgoal_tac " map abi_get_type l = replicate (length l) t")
     apply(clarsimp)

    apply(simp add:my_replicate_map list_all_iff)
    done
next
(* Tuple *)
  case (10 ts vs)
  then show ?case
    apply(clarsimp)
    apply(drule_tac mythin) apply(clarsimp)
    apply(simp split:sum.splits if_split_asm)
    apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def; clarsimp)
    apply(drule_tac x = ts in spec)
    apply(clarsimp)
    apply(drule_tac x = index in spec) apply(clarsimp)
    apply(drule_tac x = full_code in spec)
    apply(clarsimp)
    apply(simp add:list_all_iff list_sum_def)
     apply(clarsimp)
    done
next
(* Bytes *)
  case (11)
  then show ?case apply(clarsimp)
    done
next
(* String *)
  case (12)
  then show ?case by clarsimp
next
(* Array *)
  case (13 t vs)
  then show ?case by clarsimp
next

(* Nil *)
  case 14
  then show ?case
    apply(clarsimp) apply(simp add:list_sum_def)
    done
(* Cons *)
  case (15 v vs)
  then show ?case
    apply(clarsimp)
    apply(rule_tac conjI)

    (* Farray *)
     apply(rotate_tac 2) apply(drule_tac mythin) apply(clarsimp)
     apply(case_tac n; clarsimp)
     apply(simp split:sum.splits) apply(clarsimp)
    apply(drule_tac x = "(abi_get_type v)" in spec) apply(rotate_tac -1) apply(clarsimp)
     apply(drule_tac x = index in spec) apply(clarsimp)
    apply(rotate_tac -1)
    apply(drule_tac x = full_code in spec)
     apply(clarsimp)

    apply(cut_tac v = "abi_get_type v" in abi_static_size_nonneg)

     apply(subgoal_tac "nat index + nat (abi_static_size (abi_get_type v)) \<le> length full_code") apply(clarsimp)
      apply(drule_tac x = "(abi_get_type v)" in spec) apply(clarsimp)

    apply(drule_tac x = nata in spec)
      apply(drule_tac x = "index +  abi_static_size (abi_get_type v)" in spec)
    apply(subgoal_tac "(0::int) \<le> index + abi_static_size (abi_get_type v)") apply(clarsimp)
      apply(drule_tac x = full_code in spec)
      apply(clarsimp)

      apply(subgoal_tac "nat (index + abi_static_size (abi_get_type v)) + nat (int nata * abi_static_size (abi_get_type v))
\<le> length full_code") apply(clarsimp)

    apply(subgoal_tac "nat (((1::int) + int nata) * abi_static_size (abi_get_type v)) =
nat (abi_static_size (abi_get_type v)) + nat ((int nata) * abi_static_size (abi_get_type v))")

    apply(clarsimp)
        apply(simp add:take_add)
    apply(subgoal_tac "(nat (abi_static_size (abi_get_type v)) + nat index) = (nat (index + nat (abi_static_size (abi_get_type v))))")
         apply(clarsimp)
         apply(clarsimp)
    apply(arith)

    apply(simp add:Int.nat_mult_distrib)
    apply(simp add:Int.nat_add_distrib)

    apply(simp add:Int.nat_mult_distrib)
    apply(simp add:Int.nat_add_distrib)

      apply(arith)

    apply(simp add:Int.nat_mult_distrib)
        apply(simp add:Int.nat_add_distrib)

    (* Tuple *)
    apply(rotate_tac 1) apply(drule_tac mythin) apply(clarsimp)
    apply(simp split:sum.splits) apply(clarsimp)

    apply(drule_tac x = "(abi_get_type v)" in spec) apply(rotate_tac -1) apply(clarsimp)
     apply(drule_tac x = index in spec) apply(clarsimp)
    apply(rotate_tac -1)
    apply(drule_tac x = full_code in spec)
     apply(clarsimp)

    apply(drule_tac x = "(map abi_get_type vs)" in spec) apply(rotate_tac -1) apply(clarsimp)
     apply(drule_tac x = "index + abi_static_size (abi_get_type v)" in spec) 

    apply(cut_tac v = "abi_get_type v" in abi_static_size_nonneg)

    apply(subgoal_tac "(0::int) \<le> index + abi_static_size (abi_get_type v)"; clarsimp)
    apply(subgoal_tac "nat index + nat (abi_static_size (abi_get_type v)) \<le> length full_code") apply(clarsimp)
    apply(drule_tac x = full_code in spec) apply(clarsimp)

     apply(subgoal_tac " nat (index + abi_static_size (abi_get_type v)) + nat (list_sum (map (abi_static_size \<circ> abi_get_type) vs)) \<le> length full_code")
      apply(clarsimp)

      apply(simp add:list_sum_def)
    apply(cut_tac x = "(abi_static_size (abi_get_type v))" and i = 0
and xs = "(map (abi_static_size \<circ> abi_get_type) vs)" in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
      apply(clarsimp)

    apply(subgoal_tac
"nat (abi_static_size (abi_get_type v) + foldl (+) (0::int) (map (abi_static_size \<circ> abi_get_type) vs)) =
nat (abi_static_size (abi_get_type v)) + nat (foldl (+) (0::int) (map (abi_static_size \<circ> abi_get_type) vs))"  )
      apply(simp add:take_add)

    apply(subgoal_tac "(nat (abi_static_size (abi_get_type v)) + nat index) = (nat (index + nat (abi_static_size (abi_get_type v))))")
        apply(clarsimp)

    apply(clarsimp)
    apply(arith)

      apply(cut_tac l = " (map (abi_static_size \<circ> abi_get_type) vs)" in list_nonneg_sum)
       apply(simp add:list_nonneg_def list_all_iff) apply(clarsimp)
    apply(simp add:abi_static_size_nonneg)
    apply(simp add:Int.nat_add_distrib list_sum_def)

      apply(cut_tac l = " (map (abi_static_size \<circ> abi_get_type) vs)" in list_nonneg_sum)
       apply(simp add:list_nonneg_def list_all_iff) apply(clarsimp)
    apply(simp add:abi_static_size_nonneg)
     apply(simp add:Int.nat_add_distrib list_sum_def)

    apply(cut_tac x = "(abi_static_size (abi_get_type v))" and i = 0
and xs = "(map (abi_static_size \<circ> abi_get_type) vs)" in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
      apply(clarsimp)
    apply(simp add:Int.nat_add_distrib)

    apply(simp add:Int.nat_add_distrib)
    apply(simp add:list_sum_def)
      apply(cut_tac l = " (map (abi_static_size \<circ> abi_get_type) vs)" in list_nonneg_sum)
       apply(simp add:list_nonneg_def list_all_iff) apply(clarsimp)
    apply(simp add:abi_static_size_nonneg)
    apply(simp add:Int.nat_add_distrib list_sum_def)
    apply(cut_tac x = "(abi_static_size (abi_get_type v))" and i = 0
and xs = "(map (abi_static_size \<circ> abi_get_type) vs)" in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
      apply(clarsimp)
    apply(simp add:Int.nat_add_distrib)
    done

qed

lemma abi_decode_encode_static [rule_format]:
"(\<forall> t index (full_code :: 8 word list) . 
    decode_static t (index, full_code) = Ok v \<longrightarrow>
    abi_type_valid t \<longrightarrow>
    0 \<le> index \<longrightarrow>
    nat index + nat (abi_static_size t) \<le> length full_code \<longrightarrow>
   (abi_value_valid v \<and>
   (\<exists> (code :: 8 word list) . encode_static v = Ok code \<and>
       take (nat (abi_static_size t)) (drop (nat index) full_code) = code)))"
  apply(clarsimp)
  apply(cut_tac t = t in abi_decode_static_type_ok; simp?)
  apply(cut_tac v = v in abi_decode_encode_static'; simp?)
  apply(clarsimp)
  done


lemma Estatic_easier :
  "abi_type_isstatic (abi_get_type v) \<Longrightarrow>
   abi_value_valid v \<Longrightarrow>
   encode_static v = Ok code \<Longrightarrow>
   0 \<le> start \<Longrightarrow>
   nat start + nat (abi_static_size (abi_get_type v))  \<le> length full_code \<Longrightarrow>
   code = take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) \<Longrightarrow>
   can_encode_as v full_code start"
  apply(clarsimp)
    apply(cut_tac v = "v"
and code = "take (nat (abi_static_size (abi_get_type v)) ) (drop (nat start) full_code)"
and pre = "take (nat start) full_code"
and post = "drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code)"
in Estatic; (simp del:encode_static.simps)?)
  apply(subgoal_tac "(int (min (length full_code) (nat start))) = nat start")
   apply(clarsimp)
   apply(subgoal_tac "take (nat start) full_code @ take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) @ drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code)
= full_code")
    apply(clarsimp)
  apply(subgoal_tac 
" take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) @ drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) =
drop (nat start) full_code")
    apply(clarsimp)
   apply(simp only:append_take_drop_id)

  apply(arith)
  done

(*
lemma check_padding_pad_bytes [rule_format] :
  "(\<forall> sz . 
    check_padding sz l \<longrightarrow>
    (\<exists> code  . length code = sz \<and> code  = pad_bytes l))"
  apply(clarsimp)
      apply(simp add:Let_def split:prod.splits)
    apply(clarsimp)
   apply(simp add:divmod_nat_def)
   apply(clarsimp)
  apply(case_tac sz; clarsimp)
   apply(case_tac "length l"; clarsimp)
  *)
(*
  case Nil
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def split:prod.splits nat.splits)
    apply(clarsimp)
    apply(simp add:divmod_nat_def) apply(arith)
    done
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(simp add:Let_def divmod_nat_def split:prod.splits)
    apply(clarsimp)
    apply(case_tac sz; clarsimp)
    apply(case_tac "Suc (length l) mod (32::nat)"; clarsimp)
qed
*)

lemma decode_uint_valid :
  "uint_value_valid 256 (decode_uint l)"
  apply(clarsimp)
  apply(cut_tac x = "(word_rcat (take (32::nat) l))"
in decode_uint_max)
  apply(simp add:uint_value_valid_def max_u256_def)
  done

lemma pad_bytes_skip_padding :
"length (pad_bytes l) =
 skip_padding (length l)"
  apply(simp split:prod.splits)
  apply(clarsimp)
  apply(case_tac x2; clarsimp)
  apply(simp add:divmod_nat_def)
  apply(clarsimp)
  apply(arith)
  done


lemma take_min :
"take (min (length l) n) l = take n l"
proof(induction l arbitrary: n)
  case Nil
  then show ?case apply(clarsimp) done
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac n; clarsimp)
    done
qed

lemma skip_padding_gt :
  "n \<le> skip_padding n"
  apply(clarsimp)
  apply(simp add:divmod_nat_def)
  apply(case_tac "n mod 32"; clarsimp)
  apply(arith)
  done

lemma check_padding_pad_bytes :
"check_padding n l \<Longrightarrow>
pad_bytes (take n l) = take (length (pad_bytes (take n l))) l"
  apply(simp split:prod.splits)
  apply(clarsimp) apply(simp add:Let_def)
  apply(case_tac x2; clarsimp)
   apply(case_tac x2a; clarsimp)
    apply(simp only:take_min)

  apply(subgoal_tac "min (length l) n = n")
    apply(clarsimp)
  apply(arith)

  apply(case_tac x2a; clarsimp)
  apply(subgoal_tac "min (length l) n = n")
    apply(clarsimp)
  apply(simp add:divmod_nat_def; clarsimp)
  apply(arith)

  apply(subgoal_tac "min (length l) n = n")
   apply(clarsimp)
   apply(simp add:List.drop_take)

  apply(simp add:List.take_add)

  apply(simp add:divmod_nat_def; clarsimp)
  apply(arith)
  done

lemma bytes_to_string_to_bytes :
  "bytes_to_string (string_to_bytes l) = l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(simp add: uint_word_of_int)
      apply(simp add:word_of_int char_of_integer_def integer_of_char_def
uint_word_of_int)
      apply(cut_tac x = "of_char a" and xa = 256 in modulo_integer.rep_eq)
    apply(clarsimp)
    done
qed

lemma string_to_bytes_to_string :
  "(string_to_bytes (bytes_to_string l)) = l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(simp add:word_of_int char_of_integer_def integer_of_char_def uint_idem)
      apply(cut_tac w = a in uint_idem)
    apply(clarsimp)
    done
qed

(*
lemma abi_decode_dyn_tuple_heads_succeed_strong :
"
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
decode'_dyn_tuple_tails (?tails'::int option list) (map abi_get_type (?vs::abi_value list)) (?heads'::abi_value option list) (?offset::int) \<longrightarrow>
(\<exists>
heads head_types tails .
is_head_and_tail vs heads head_types htails
those (map2 ht_combine heads' (map (case_option None (\<lambda> t . Some (t - int (length pre1)))) tails')) = Some heads \<and>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ l @ post) (int (length (pre1)) + int (length pre2)) \<and>
"
*)


(* one option (?) - prove this lemma
   another: use custom induction rule and see if we can inline it
   into the induction hypotheses *)
(*
lemma abi_decode_dyn_tuple_heads_succeed_converse :
"
\<forall> heads' tails' count' offset pre1 pre2 post l bytes heads head_types tails.
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<longrightarrow>
decode'_dyn_tuple_tails (?tails'::int option list) (map abi_get_type (?vs::abi_value list)) (?heads'::abi_value option list) (?offset::int)
     (int (length (?pre1.0::8 word list)), ?pre1.0 @ (?pre2.0::8 word list) @ (?code::8 word list) @ (?post::8 word list))
those (map2 ht_combine heads' 
       (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<longrightarrow>
map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<longrightarrow>
(is_head_and_tail vs heads head_types tails \<and>
 can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post) (int (length pre1) + int (length pre2)) \<and>
(\<forall> (offset::int) v::abi_value.
           (offset, v) \<in> set tails \<longrightarrow> can_encode_as v (pre1 @ pre2 @ l @ post) (int (length pre1) + offset)))
"
*)

(* ok, so i think we need to revisit the idea of "vs_pre"
basically as an inductive assumption we have a "head" that already has is_head_and_tail proven about it
then we just need to "extend"
*)

lemma decode'_index_positive :
"decode' t (start, full_code) = Ok (v, len) \<Longrightarrow>
 0 \<le> start"
  apply(simp add:decode'.simps)
  apply(case_tac "start < 0"; clarsimp)
  done

lemma list_sum_concat :
  "list_sum (map length xss) = length (concat xss)"
proof(induction xss)
  case Nil
  then show ?case by (auto simp add:list_sum_def)
next
  case (Cons a xss)
  then show ?case
    apply(clarsimp) apply(simp add:list_sum_def)
    apply(cut_tac x = "int (length a)" and i = 0 and xs = "map (int \<circ> length) xss" in foldl_plus)
    apply(simp)
    done
qed

lemma list_partition3 :
"  l1 @ l2 @ post = l @ post' \<Longrightarrow>
length l1 + length l2 + n = length l \<Longrightarrow>
       l = l1 @ l2 @ drop (length l1 + length l2) l"
  apply(subgoal_tac "l1 @ l2 @ drop (length l1 + length l2) l = (l1 @ l2) @ drop (length l1 + length l2) l")
  apply(simp only:)
   apply(subgoal_tac "l1 @ l2 = take (length l1 + length l2) l")
    apply(simp only:)
    apply(simp only: List.append_take_drop_id)
  apply(thin_tac "l1 @ l2 @ drop (length l1 + length l2) l = (l1 @ l2) @ drop (length l1 + length l2) l")
   apply(simp add:append_eq_conv_conj)
   apply(clarsimp) apply(simp add: min_absorb1 min_absorb2)
   apply(simp add:List.drop_take)
  apply(simp)
  done

lemma decode'_tuple_tails_length :
  "decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) = Ok (vs, bytes) \<Longrightarrow>
    length vs = length ts"
proof(induction ts arbitrary: idxs vs vos byteoffset ix l bytes)
  case Nil
  then show ?case
    apply(simp split:sum.splits prod.splits)
    apply(case_tac idxs; clarsimp)
    apply(case_tac vos; clarsimp)
    done
next
  case (Cons a ts)
  then show ?case
    apply(simp split:sum.splits prod.splits)
    apply(case_tac idxs; clarsimp)
    apply(case_tac vos; clarsimp)
    apply(case_tac aa; clarsimp)
     apply(case_tac aa; clarsimp)
    apply(simp split:sum.splits prod.splits)
     apply(clarsimp)
     apply(case_tac aa; clarsimp)
    apply(simp split:sum.splits prod.splits)
     apply(clarsimp)
    done
qed

(* Vtuple and Varray cases are under construction *)
lemma abi_decode_succeed_converse_gen [rule_format]:
  "(\<forall> t len start full_code .
    decode' t (start, full_code) = Ok (v, len) \<longrightarrow>
    abi_type_valid t \<longrightarrow>
    abi_get_type v = t \<longrightarrow>
    can_encode_as v full_code (start)) \<and>
   (
    (\<forall> v t n pre1 pre2 code heads' tails' count' count'' bytes bytes'.
          v = (Vfarray t n vs) \<longrightarrow> 
          abi_type_isdynamic t \<longrightarrow>
          abi_type_valid t \<longrightarrow>
          decode'_dyn_tuple_heads (replicate n t) (int (length pre2)) (int (length pre1), pre1@pre2@code) = Ok (heads', tails', count', bytes) \<longrightarrow>
          decode'_dyn_tuple_tails tails' (replicate n t) heads' count'' (int (length pre1), pre1@pre2@code) = Ok (vs, bytes') \<longrightarrow>
          (abi_value_valid v \<and>
          (\<exists> heads head_types tails . 
            is_head_and_tail vs heads head_types tails \<and>
            can_encode_as (Vtuple head_types heads) ( pre1@pre2@code) (int (length pre1) + int (length pre2)) \<and>
            (\<forall> (offset::int) v::abi_value.
             (offset, v) \<in> set tails \<longrightarrow> can_encode_as v ( pre1@pre2@code) (int (length pre1) + offset)) \<and>
             those (map2 ht_combine heads' 
               (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
                map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
                ht_wellbehaved tails' (map abi_get_type vs) heads'))
          ) \<and>
    (\<forall> v ts n pre1 pre2 code heads' tails' count' count'' bytes bytes'.
          v = (Vtuple ts vs) \<longrightarrow> 
          list_all abi_type_valid ts \<longrightarrow>
          decode'_dyn_tuple_heads (ts) (int (length pre2)) (int (length pre1), pre1@pre2@code) = Ok (heads', tails', count', bytes) \<longrightarrow>
          decode'_dyn_tuple_tails tails' (ts) heads' count'' (int (length pre1), pre1@pre2@code) = Ok (vs, bytes') \<longrightarrow>
          (abi_value_valid v \<and>
          (\<exists> heads head_types tails . 
            is_head_and_tail vs heads head_types tails \<and>
            can_encode_as (Vtuple head_types heads) ( pre1@pre2@code) (int (length pre1) + int (length pre2)) \<and>
            (\<forall> (offset::int) v::abi_value.
             (offset, v) \<in> set tails \<longrightarrow> can_encode_as v ( pre1@pre2@code) (int (length pre1) + offset)) \<and>
             those (map2 ht_combine heads' 
               (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
                map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
                ht_wellbehaved tails' (map abi_get_type vs) heads'))
          ) \<and>
    (\<forall> v t n n' pre1 pre2 count code heads' tails' count' count'' bytes bytes'.
          v = (Varray t vs) \<longrightarrow> 
          abi_type_valid t \<longrightarrow>
          length count = 32 \<longrightarrow>
          uint_value_valid 256 n \<longrightarrow>
          uint_value_valid 256 n' \<longrightarrow>
          n = length vs \<longrightarrow>
          n \<le> n' \<longrightarrow>
          count = encode_int (int n') \<longrightarrow>
          decode'_dyn_tuple_heads (replicate n t) (int (length pre2)) (int (length (pre1 @ count)), pre1@count@pre2@code) = Ok (heads', tails', count', bytes) \<longrightarrow>
          decode'_dyn_tuple_tails tails' (replicate n t) heads' count'' (int (length (pre1 @ count)), pre1@count@pre2@code) = Ok (vs, bytes') \<longrightarrow>
          (abi_value_valid v \<and>
          (\<exists> heads head_types tails . 
            is_head_and_tail vs heads head_types tails \<and>
            can_encode_as (Vtuple head_types heads) ( pre1@count@pre2@code) (int (length pre1) + 32 + int (length pre2)) \<and>
            (\<forall> (offset::int) v::abi_value.
             (offset, v) \<in> set tails \<longrightarrow> can_encode_as v ( pre1@count@pre2@code) (int (length pre1) + 32 + offset)) \<and>
             those (map2 ht_combine heads' 
               (map (\<lambda> to . (case to of None \<Rightarrow> None | Some t \<Rightarrow> Some (t - int (length pre1) - 32))) tails')) = Some heads \<and>
                map (\<lambda> x . fst x + int (length pre1) + 32) tails = (somes tails') \<and>
                ht_wellbehaved tails' (map abi_get_type vs) heads'))
          )
   )"
(*             
from array case... need as premise? as conclusion?
generalizing... "length vs - length pre2?" *)
proof(induction rule:my_abi_value_induct)
(* Vuint *)
  case (1 x1 x2)
  then show ?case 
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Vsint *)
  case (2 x1 x2)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Addr *)
  case (3 x)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Bool *)
  case (4 x)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Vfixed *)
  case (5 x1 x2 x3a)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Vufixed *)
  case (6 x1 x2 x3a)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Vfbytes *)
  case (7 x1 x2)
  then show ?case
    apply(clarify)
    apply(simp add:decode'.simps del: decode_static.simps split:if_splits sum.splits)
    apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
    apply(clarify)
    apply(rule_tac Estatic_easier; simp?)
    done
next
(* Vfunction *)
  case (8 x1 x2)
  then show ?case sorry
next
  (* Vfarray *)
  case (9 t n l) then show ?case

    apply(clarsimp)
    apply(rotate_tac 1) apply(drule_tac mythin) apply(drule_tac mythin)
    apply(clarsimp)
      apply(simp add:decode'.simps Let_def del: decode_static.simps split:if_splits sum.splits prod.splits)

(* static *)
    apply(rotate_tac 1) apply(drule_tac mythin) (* don't need inductive hypothesis *)
          apply(clarify)
        apply(simp add:Let_def decode'.simps del: decode_static.simps split:if_splits sum.splits)
        apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
        apply(clarify)
       apply(simp add:abi_static_size_nonneg)
       apply(simp add:Int.nat_mult_distrib)   
     apply(cut_tac v = t in abi_static_size_nonneg) 
    apply(simp split:sum.splits)

      apply(rule_tac Estatic_easier; (simp del:encode_static.simps)?)

      apply(simp add:Int.nat_add_distrib)
       apply(cut_tac v = t in abi_static_size_nonneg) 
      apply(clarsimp)
     apply(simp add:abi_static_size_nonneg)
       apply(simp add:Int.nat_mult_distrib)   

(* dynamic *)
     apply(drule_tac x = t in spec)
     apply(clarsimp) apply(drule_tac x = n in spec)
     apply(drule_tac x = "take (nat start) full_code" in spec)
    apply(drule_tac x = "[]" in spec) apply(clarsimp)
     apply(drule_tac x = "drop (nat start) full_code" in spec) apply(clarsimp)
     apply(drule_tac x = x1a in spec)
     apply(drule_tac x = x1b in spec)

    apply(subgoal_tac "int (min (length full_code) (nat start)) = start")

      apply(clarsimp)
      apply(subgoal_tac "(\<exists>(count''::int) bytes'::int. decode'_dyn_tuple_tails x1b (replicate n t) x1a count'' (start, full_code) = Ok (l, bytes'))")
    apply(clarsimp)

     apply(rule_tac Efarray_dyn; simp?)
      apply(drule_tac x = "offset" in spec) apply(drule_tac x = v in spec) apply(clarsimp)
       apply(simp add:add.commute)

      apply(fastforce)

    apply(arith)
    done
next
(* Vtuple *)
  case (10 ts vs)
  then show ?case
        apply(clarsimp)
    apply(drule_tac mythin) apply(rotate_tac 1) apply(drule_tac mythin)
    apply(clarsimp)
    apply(simp add:decode'.simps Let_def del: decode_static.simps split:if_splits sum.splits prod.splits)

(* static *)
        apply(clarify)
        apply(simp add:Let_def decode'.simps del: decode_static.simps split:if_splits sum.splits)
        apply(drule_tac abi_decode_encode_static; (simp del:encode_static.simps)?)
        apply(clarify)
        apply(simp add:abi_static_size_nonneg)
        apply(cut_tac l = "(map abi_static_size ts)" in list_nonneg_sum)
         apply(simp add:list_nonneg_def) apply(simp add:list_all_iff) apply(clarsimp)
         apply(simp add:abi_static_size_nonneg)

      apply(simp add:list_sum_def)

      apply(rule_tac Estatic_easier; (simp del:encode_static.simps)?)
       apply(simp add:Int.nat_add_distrib)


(* dynamic *)
     apply(drule_tac x = ts in spec)
     apply(clarsimp) 
     apply(drule_tac x = "take (nat start) full_code" in spec)
    apply(drule_tac x = "[]" in spec) apply(clarsimp)
     apply(drule_tac x = "drop (nat start) full_code" in spec) apply(clarsimp)
     apply(drule_tac x = x1a in spec)
     apply(drule_tac x = x1b in spec)

    apply(subgoal_tac "int (min (length full_code) (nat start)) = start")

      apply(clarsimp)
      apply(subgoal_tac "\<exists>(count'::int) bytes::int. decode'_dyn_tuple_heads ts (0::int) (int (min (length full_code) (nat start)), full_code) = Ok (x1a, x1b, count', bytes)")
    apply(clarsimp)

       apply(subgoal_tac "(\<exists>(count''::int) bytes'::int. decode'_dyn_tuple_tails x1b ts x1a count'' (start, full_code) = Ok (vs, bytes'))")
    apply(clarsimp)

    apply(simp add:list_ex_iff) apply(clarsimp)
     apply(rule_tac t = x in Etuple_dyn; simp?)
      apply(drule_tac x = "offset" in spec) apply(drule_tac x = v in spec) apply(clarsimp)
       apply(simp add:add.commute)

       apply(fastforce)

apply(fastforce)

    apply(arith)

    
    done
next
(* Vbytes *)
  case (11 x)

  thus ?case
    apply(clarsimp)
    apply(simp add:decode'.simps Let_def)
    apply(simp add:split:if_splits del:decode_uint.simps)
    apply(simp add:Let_def del:decode_uint.simps)
    apply(simp add: Let_def split:if_splits del:check_padding.simps skip_padding.simps decode_uint.simps)
    apply(clarify)

    apply(subgoal_tac
"(int (min (length full_code - ((32::nat) + nat start)) (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))))
= int (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))")
       apply(simp del:check_padding.simps decode_uint.simps skip_padding.simps)
    apply(simp add: Let_def split:if_splits del:check_padding.simps skip_padding.simps decode_uint.simps)

    apply(cut_tac
l = "(take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))"
and pre = "take (nat start) full_code"
and post = "(drop (nat start) (drop 32 (drop (skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) full_code)))"
and count = "take 32 (drop (nat start) full_code)"
in Ebytes)

    apply(simp del:check_padding.simps pad_bytes.simps skip_padding.simps decode_uint.simps)
    apply(simp add:bytes_value_valid_def Let_def del:skip_padding.simps decode_uint.simps)


    apply(simp add: decode_uint_valid del:decode_uint.simps)
         apply(simp add:uint_value_valid_def del:pad_bytes.simps)

    apply(simp (no_asm_simp))

       apply(arith)

       apply(rule_tac Estatic_easier)
    apply(simp (no_asm))
    apply(simp (no_asm))

    apply(cut_tac l = "(take (32::nat) (drop (nat start) full_code))"
in decode_uint_valid)
    apply(simp)

    apply(rotate_tac 1)
          apply(drule_tac mythin) apply(drule_tac mythin)
    apply(rotate_tac 1)
    apply(drule_tac mythin) apply(drule_tac mythin)
          apply(drule_tac mythin) 

    apply(simp)

         apply(simp only: encode_static.simps)

        apply(simp)


       apply(subgoal_tac "min (length full_code - nat start) 32 = 32")
        apply(arith)
       apply(arith)

      apply(simp (no_asm) del:decode_uint.simps split:prod.split)
    apply(clarify)

    apply(simp del: decode_uint.simps add:uint_value_valid_def)
       apply(subgoal_tac "min (length full_code - nat start) 32 = 32")

    apply(simp del:decode_uint.simps)

    apply(cut_tac l = "(take (32::nat) (drop (nat start) full_code))"
in decode_uint_valid)

    apply(simp)

        apply(rule_tac "word_rsplit_rcat_size")
        apply(simp (no_asm_simp) add:word_size)    

       apply(clarsimp)
    apply(subgoal_tac
"0 \<le> decode_uint (take (32::nat) (drop (nat start) full_code))")
       apply(arith)
    apply(simp only:decode_uint.simps uint_0)

    apply(subgoal_tac
"(take (nat start) full_code @
         take (32::nat) (drop (nat start) full_code) @
pad_bytes (take (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) (drop ((32::nat) + nat start) full_code)) @
         drop (nat start) (drop (32::nat) (drop (skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) full_code)))
=
full_code") apply(simp only:)


    apply(subgoal_tac
"(skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) =
length (pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)))")
    apply(simp only: split:prod.splits nat.split_asm)

(*
    apply(simp del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps split:prod.splits)
         apply(simp only:List.append_eq_conv_conj)
*)
        apply(subgoal_tac "(int (length (take (nat start) full_code))) = start")
         apply(simp only:)


         apply(subgoal_tac "(min (length full_code) (nat start)) = nat start")
         apply(simp (no_asm_simp))

         apply(simp del:pad_bytes.simps skip_padding.simps check_padding.simps decode_uint.simps split:prod.splits)


    apply(subgoal_tac
"0 \<le> decode_uint (take (32::nat) (drop (nat start) full_code))")
    apply(rotate_tac 1) apply(rotate_tac 1)
       apply(arith)
    apply(simp only:decode_uint.simps uint_0)



    apply(simp only:pad_bytes_skip_padding)
    apply(simp (no_asm_simp) del:skip_padding.simps)
       apply(frule_tac check_padding_pad_bytes) 
          apply(subgoal_tac "min (length full_code - nat start) (32::nat) = 32")

    apply(subgoal_tac "min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))
= (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))")
    apply(simp only: decode_uint.simps)
            apply(simp del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps)


        apply(simp only:decode_uint.simps)
(*
    apply(subgoal_tac
"(nat start + ((32::nat) + length (pad_bytes (take (nat (uint (word_rcat ( (take (32::nat) (drop (nat start) full_code)))))) (drop ((32::nat) + nat start) full_code)))))
= (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)) + ((32::nat) + nat start))")
             apply(rotate_tac -1)
*)

    apply(drule_tac x = "int (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word))))"
and f = nat
in arg_cong)
    apply(simp only: nat_int)

    apply(subgoal_tac
"(take (32::nat) (take (32::nat) (drop (nat start) full_code)) =
(take (32 :: nat) (drop (nat start) full_code)))")
    apply(simp only:)

        apply(simp (no_asm_simp))
    apply(subgoal_tac
"0 \<le> decode_uint (take (32::nat) (drop (nat start) full_code))")
            apply(simp only: decode_uint.simps)
            apply(rotate_tac -3)
        apply(drule_tac f = nat in arg_cong) apply(simp only:nat_int)

    apply(rotate_tac 1)
        apply(drule_tac mythin)
    apply(rotate_tac 3)
        apply(drule_tac mythin)
    apply(drule_tac mythin) apply(drule_tac mythin)
          apply(drule_tac mythin) 
    apply(arith)

    apply(simp (no_asm_simp))

    apply(simp (no_asm_simp) del:skip_padding.simps pad_bytes.simps )

    apply(frule_tac check_padding_pad_bytes)
    apply(simp only: pad_bytes_skip_padding)

    apply(frule_tac s =
"pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))"
and t = 
"take (skip_padding (length (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))))
        (drop ((32::nat) + nat start) full_code)"
and P = "(\<lambda> pb . 
take (nat start) full_code @
       take (32::nat) (drop (nat start) full_code) @
       pb @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code =
       full_code)"
in subst)

    apply(subgoal_tac
"take (32::nat) (drop (nat start) full_code) @
       pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)) @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code
= drop (nat start) full_code")

    apply(simp only: decode_uint.simps)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(subgoal_tac
" pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)) @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))))  full_code
=
drop (32 :: nat) (drop (nat start) full_code)")
    apply(simp only: decode_uint.simps)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(simp only: decode_uint.simps)

       apply(subgoal_tac "drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code
=drop (skip_padding  (length (take (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word)))
(drop ((32::nat) + nat start) full_code)))) (drop ((32::nat) + nat start) full_code)")

    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)
    apply(simp only:List.drop_drop)
       apply(simp only:List.drop_drop)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(rule_tac arg_cong)

    apply(subgoal_tac
"(nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))))
=
(skip_padding (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))) + ((32::nat) + nat start)) ")
        apply(simp only:)

    apply(subgoal_tac
" (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))) = 
(nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))")
        apply(simp only:)

       apply(subgoal_tac "
length full_code - ((32::nat) + nat start) \<ge> (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))"
)
        apply(simp only: decode_uint.simps )
        apply(rotate_tac -1)
        apply(drule_tac min_absorb2)


    apply(subgoal_tac "(take (32::nat) (take (32::nat) (drop (nat start) full_code))) = ((take (32::nat) (drop (nat start) full_code)))")
    apply(simp only:)
        apply(simp (no_asm_simp))


       apply(rotate_tac 2)
      apply(drule_tac mythin)
    apply(drule_tac mythin)
      apply(drule_tac mythin)
       apply(drule_tac mythin)
apply(drule_tac mythin)

       apply(subgoal_tac "0 \<le> uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))))")
        apply(fastforce)
    apply(simp)


    apply(subgoal_tac
"take (skip_padding (length (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)))) (drop ((32::nat) + nat start) full_code)
=
pad_bytes (take (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) (drop ((32::nat) + nat start) full_code))")

    apply(simp only: decode_uint.simps)
      apply(simp only: decode_uint.simps)

    apply(subgoal_tac "(take (32::nat) (take (32::nat) (drop (nat start) full_code))) = ((take (32::nat) (drop (nat start) full_code)))")
    apply(simp only:)
        apply(simp (no_asm_simp))

    apply(simp )

     apply(arith)
    done
next
(* Vstring *)
  case (12 x)
  then show ?case

    apply(clarsimp)
    apply(simp add:decode'.simps Let_def)
    apply(simp add:split:if_splits del:decode_uint.simps)
    apply(simp add:Let_def del:decode_uint.simps)
    apply(simp add:split:if_splits del:check_padding.simps bytes_to_string.simps skip_padding.simps decode_uint.simps)
    apply(simp add:Let_def del:decode_uint.simps)
    apply(simp add:split:if_splits del:check_padding.simps bytes_to_string.simps skip_padding.simps decode_uint.simps)

(*    apply(clarify) *)

    apply(subgoal_tac
"(int (min (length full_code - ((32::nat) + nat start)) (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))))
= int (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))")
       apply(simp del:check_padding.simps decode_uint.simps skip_padding.simps bytes_to_string.simps split:if_splits)

    apply(rule_tac Estring; (simp (no_asm) del:decode_uint.simps string_to_bytes.simps bytes_to_string.simps)?)

    apply(simp only: string_value_valid_def)
         apply(drule_tac mythin) apply(drule_tac mythin)
       apply(drule_tac mythin)
       (*apply(drule_tac mythin)
      apply(drule_tac mythin) apply(drule_tac mythin)
apply(drule_tac mythin)  *)
    apply(simp  add: decode_uint_valid string_value_valid_def del:decode_uint.simps)
    apply(simp  add:uint_value_valid_def)

    apply(subgoal_tac
"length x =
length ((take (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) (drop ((32::nat) + nat start) full_code)))")
    apply(simp only:)
    apply(simp add: string_to_bytes_to_string del: check_padding.simps bytes_to_string.simps string_to_bytes.simps skip_padding.simps decode_uint.simps)
    apply(cut_tac x = "(word_rcat (take (32::nat) (drop (nat start) full_code)))"
in decode_uint_max) apply(simp add:max_u256_def)
       apply(drule_tac f = length in arg_cong)
    apply(simp)

    apply(subgoal_tac "(min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))) =
nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))")


    apply(simp del:string_to_bytes.simps check_padding.simps pad_bytes.simps skip_padding.simps decode_uint.simps)

    apply(cut_tac
l = "(take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))"
and pre = "take (nat start) full_code"
and post = "(drop (nat start) (drop 32 (drop (skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) full_code)))"
and count = "take 32 (drop (nat start) full_code)"
in Ebytes)


    apply(simp del:check_padding.simps pad_bytes.simps skip_padding.simps decode_uint.simps)
    apply(simp add:bytes_value_valid_def Let_def del:skip_padding.simps decode_uint.simps)


           apply(simp only: decode_uint_valid )
          apply(simp only:)
         apply(simp (no_asm_simp))

    apply(subgoal_tac
"0 \<le> decode_uint (take (32::nat) (drop (nat start) full_code))")

         apply(simp only:decode_uint.simps)

    apply(rule_tac min_absorb2)
         apply(rotate_tac 2)
         apply(drule_tac mythin)
    apply(drule_tac mythin)
         apply(drule_tac mythin)
apply(drule_tac mythin)

         apply(arith)
    apply(simp only:decode_uint.simps)


       apply(rule_tac Estatic_easier)
    apply(simp (no_asm))
    apply(simp (no_asm))

    apply(cut_tac l = "(take (32::nat) (drop (nat start) full_code))"
in decode_uint_valid)
    apply(simp (no_asm_simp))

    apply(rotate_tac 1)
          apply(drule_tac mythin) apply(drule_tac mythin)
    apply(rotate_tac 1)
    apply(drule_tac mythin) apply(drule_tac mythin)
          apply(drule_tac mythin) 

    apply(simp)

         apply(simp only: encode_static.simps)

    apply(simp only:decode_uint.simps)

    apply(simp (no_asm_simp))

         apply(subgoal_tac "min (length full_code - nat start) 32 = 32")
    apply(drule_tac mythin) apply(drule_tac mythin)
          apply(drule_tac mythin) 

          apply(arith)

    apply(rotate_tac 2)
    apply(drule_tac mythin) apply(drule_tac mythin)
         apply(drule_tac mythin) apply(drule_tac mythin) 
         apply(rule_tac min_absorb2)
         apply(simp only: decode_uint.simps)
    apply(subgoal_tac "uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word) \<ge> 0")
       apply(arith)

    apply(simp only:uint_0)

      apply(simp (no_asm) del:decode_uint.simps split:prod.split)
    apply(clarify)

    apply(simp del: decode_uint.simps add:uint_value_valid_def)
       apply(subgoal_tac "min (length full_code - nat start) 32 = 32")

    apply(simp del:decode_uint.simps)

    apply(cut_tac l = "(take (32::nat) (drop (nat start) full_code))"
in decode_uint_valid)

    apply(simp (no_asm_simp))

        apply(rule_tac "word_rsplit_rcat_size")
        apply(simp (no_asm_simp) add:word_size)    

        apply(clarsimp)
    apply(rotate_tac 2)
    apply(drule_tac mythin) apply(drule_tac mythin)
         apply(drule_tac mythin) apply(drule_tac mythin) 
         apply(rule_tac min_absorb2)
    apply(subgoal_tac "uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) \<ge> 0")
       apply(arith)
    apply(simp only:decode_uint.simps uint_0)


    apply(subgoal_tac
"
(take (nat start) full_code @
         take (32::nat) (drop (nat start) full_code) @
         pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)) @
         drop (nat start) (drop (32::nat) (drop (skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) full_code)))
=
full_code")

    apply(simp only:decode_uint.simps)

    apply(subgoal_tac
"(skip_padding (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))) =
length (pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)))")
    apply(simp only: decode_uint.simps split:prod.splits nat.split_asm)

    apply(subgoal_tac
"(take (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256  word))) (drop (32 + nat start) full_code))
= string_to_bytes x")

    apply(simp only:)

(*
    apply(simp del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps split:prod.splits)
         apply(simp only:List.append_eq_conv_conj)
*)
        apply(subgoal_tac "(int (length (take (nat start) full_code))) = start")
         apply(simp only:)


         apply(subgoal_tac "(min (length full_code) (nat start)) = nat start")
         apply(simp (no_asm_simp))

          apply(simp del:pad_bytes.simps skip_padding.simps check_padding.simps decode_uint.simps split:prod.splits)

    apply(rotate_tac 2)
    apply(drule_tac mythin) apply(drule_tac mythin)
           apply(drule_tac mythin) apply(drule_tac mythin)
           apply(drule_tac mythin) apply(drule_tac mythin)
          apply(rule_tac min_absorb2)
    apply(subgoal_tac "uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) \<ge> 0")
       apply(arith)
    apply(simp only:decode_uint.simps uint_0)

    apply(subgoal_tac
" map (\<lambda>b::8 word. char_of_integer (of_int (uint b)))
        (take (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word))) (drop ((32::nat) + nat start) full_code)) 
       = bytes_to_string(take (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word))) (drop ((32::nat) + nat start) full_code)) 
")
          apply(clarify)
          apply(simp only:)
          apply(simp only:string_to_bytes_to_string)
    apply(simp (no_asm_simp) )

    apply(simp only:pad_bytes_skip_padding)
    apply(simp (no_asm_simp) del:bytes_to_string.simps skip_padding.simps)
       apply(frule_tac check_padding_pad_bytes) 
          apply(subgoal_tac "min (length full_code - nat start) (32::nat) = 32")

    apply(subgoal_tac "min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))
= (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))")
    apply(simp only: decode_uint.simps)
            apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps)

(*
    apply(subgoal_tac
"(nat start + ((32::nat) + length (pad_bytes (take (nat (uint (word_rcat ( (take (32::nat) (drop (nat start) full_code)))))) (drop ((32::nat) + nat start) full_code)))))
= (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)) + ((32::nat) + nat start))")
             apply(rotate_tac -1)
*)

    apply(drule_tac x = "int (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word))))"
and f = nat
in arg_cong)
    apply(simp only: nat_int)

    apply(subgoal_tac
"(take (32::nat) (take (32::nat) (drop (nat start) full_code)) =
(take (32 :: nat) (drop (nat start) full_code)))")
    apply(simp only:)
(*
        apply(simp (no_asm_simp))
    apply(subgoal_tac
"0 \<le> decode_uint (take (32::nat) (drop (nat start) full_code))")
            apply(simp only: decode_uint.simps)
            apply(rotate_tac -3)
        apply(drule_tac f = nat in arg_cong) apply(simp only:nat_int)

    apply(rotate_tac 1)
        apply(drule_tac mythin)
    apply(rotate_tac 3)
        apply(drule_tac mythin)
    apply(drule_tac mythin) apply(drule_tac mythin)
          apply(drule_tac mythin) 
    apply(arith)
*)

    apply(frule_tac check_padding_pad_bytes)
    apply(simp only: pad_bytes_skip_padding decode_uint.simps)

    apply(cut_tac s =
"pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))"
and t = 
"take (skip_padding (length (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code))))
        (drop ((32::nat) + nat start) full_code)"
and P = "(\<lambda> pb . 
take (nat start) full_code @
       take (32::nat) (drop (nat start) full_code) @
       pb @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code =
       full_code)"
in subst)
    apply(simp only:decode_uint.simps)

    apply(subgoal_tac
"take (32::nat) (drop (nat start) full_code) @
       pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)) @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code
= drop (nat start) full_code")

    apply(simp only: decode_uint.simps)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(subgoal_tac
" pad_bytes (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)) @
       drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))))  full_code
=
drop (32 :: nat) (drop (nat start) full_code)")
    apply(simp only: decode_uint.simps)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(simp only: decode_uint.simps)

       apply(subgoal_tac "drop (nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))))) full_code
=drop (skip_padding  (length (take (nat (uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word)))
(drop ((32::nat) + nat start) full_code)))) (drop ((32::nat) + nat start) full_code)")

    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)
    apply(simp only:List.drop_drop)
       apply(simp only:List.drop_drop)
    apply(simp (no_asm_simp) del:pad_bytes.simps skip_padding.simps decode_uint.simps check_padding.simps List.drop_drop)

    apply(rule_tac arg_cong)

    apply(subgoal_tac
"(nat start + ((32::nat) + skip_padding (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))))
=
(skip_padding (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))) + ((32::nat) + nat start)) ")
        apply(simp only:)

    apply(subgoal_tac
" (min (length full_code - ((32::nat) + nat start)) (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))) = 
(nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)))")
        apply(simp only:)

       apply(subgoal_tac "
length full_code - ((32::nat) + nat start) \<ge> (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))"
)
        apply(simp only: decode_uint.simps )
        apply(rotate_tac -1)
(*        apply(drule_tac min_absorb2)   *)


(*
    apply(subgoal_tac "(take (32::nat) (take (32::nat) (drop (nat start) full_code))) = ((take (32::nat) (drop (nat start) full_code)))")
    apply(simp only:)
        apply(simp (no_asm_simp))
*)

       apply(rotate_tac 3)
      apply(drule_tac mythin)
    apply(drule_tac mythin)
      apply(drule_tac mythin)
       apply(drule_tac mythin)
           apply(drule_tac mythin)
       apply(drule_tac mythin)
           apply(drule_tac mythin)
       apply(drule_tac mythin)
apply(drule_tac mythin)

       apply(subgoal_tac "0 \<le> uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))))")
            apply(simp only: decode_uint.simps)
    apply(fastforce)
    apply(simp)


    apply(subgoal_tac
"take (skip_padding (length (take (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))) (drop ((32::nat) + nat start) full_code)))) (drop ((32::nat) + nat start) full_code)
=
pad_bytes (take (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) (drop ((32::nat) + nat start) full_code))")

    apply(simp only: decode_uint.simps)
          apply(simp only: decode_uint.simps)

         apply(simp (no_asm_simp))

       apply(subgoal_tac "
length full_code - ((32::nat) + nat start) \<ge> (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))"
)
        apply(simp only: decode_uint.simps )
        apply(rotate_tac -1)

       apply(rotate_tac 3)
      apply(drule_tac mythin)
    apply(drule_tac mythin)
      apply(drule_tac mythin)
       apply(drule_tac mythin)
           apply(drule_tac mythin)
           apply(drule_tac mythin)

       apply(subgoal_tac "0 \<le> uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word)")
            apply(simp only: decode_uint.simps)
    apply(fastforce)
    apply(simp)


    apply(rotate_tac 3)
        apply(rule_tac min_absorb2)
      apply(drule_tac mythin)
    apply(drule_tac mythin)
      apply(drule_tac mythin)
       apply(drule_tac mythin)
       apply(drule_tac mythin)
apply(drule_tac mythin)

       apply(subgoal_tac "0 \<le> uint (word_rcat (take (32::nat) (take (32::nat) (drop (nat start) full_code))) :: 256 word)")
            apply(simp only: decode_uint.simps)
       apply(fastforce)

    apply(rotate_tac 3)
      apply(rule_tac min_absorb2)
      apply(drule_tac mythin)
    apply(drule_tac mythin)
      apply(drule_tac mythin)
      apply(simp)

    apply(simp )

     apply(arith)
    done
next
(* Varray *)
  case (13 t vs)
  then show ?case 

    apply(clarsimp)
    apply(drule_tac mythin) apply(drule_tac mythin)
    apply(clarsimp)
    apply(simp add:decode'.simps Let_def del: decode_static.simps split:if_splits sum.splits prod.splits)
     apply(drule_tac x = t in spec)
    apply(clarsimp)

     apply(subgoal_tac "uint_value_valid (256::nat) (int (length vs))") apply(clarsimp)
     apply(subgoal_tac "length (word_rsplit (word_of_int (int (length vs)) :: 256 word) :: 8 word list) = (32::nat) ")
    apply(drule_tac x = "length vs" in spec)
      apply(clarsimp)

    apply(frule_tac decode'_tuple_tails_length; clarsimp)

     apply(drule_tac x = "take (nat start) full_code" in spec)
    apply(drule_tac x = "[]" in spec) apply(clarsimp)
    apply(drule_tac x = "(drop (32::nat) (drop (nat start) full_code))" in spec)
    apply(subgoal_tac "min (length full_code - nat start) (32::nat) = (32::nat)") 
(* need lemma that decode'_dyn_tuple_tails preserves length. this should not be hard. *)
     apply(drule_tac x = x1a in spec)
     apply(drule_tac x = x1b in spec)

    apply(subgoal_tac "int (min (length full_code) (nat start) + 32) = start + 32")

      apply(clarsimp)
      apply(subgoal_tac "(\<exists>(count'::int) bytes::int.
           decode'_dyn_tuple_heads (replicate (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) t) (0::int)
            (int (min (length full_code) (nat start)) + (32::int),
             take (nat start) full_code @
             word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) @ drop (32::nat) (drop (nat start) full_code)) =
           Ok (x1a, x1b, count', bytes))")
        apply(clarsimp)
    apply(subgoal_tac "
   (\<exists>(count''::int) bytes'::int.
           decode'_dyn_tuple_tails x1b (replicate (nat (uint (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word))) t) x1a count''
            (start + (32::int),
             take (nat start) full_code @ word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) @ drop ((32::nat) + nat start) full_code) =
           Ok (vs, bytes'))")
    apply(clarsimp)


    apply(subgoal_tac
"(take (nat start) full_code @ word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) @ drop (32::nat) (drop (nat start) full_code))
= full_code")

         apply(rule_tac Earray; (simp (no_asm_simp))?)

    apply(subgoal_tac "take (32::nat) (drop (nat start) full_code) @   drop (32::nat) (drop (nat start) full_code) = drop (nat start) full_code")
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
           apply(rotate_tac -1) apply(drule_tac sym) apply( simp only: List.append_take_drop_id)

            apply(rule_tac Estatic_easier; (simp (no_asm_simp))?)

         apply(rule_tac word_rsplit_rcat_size)
               apply(simp (no_asm_simp) add:word_size)
    apply(arith)

              apply( simp (no_asm_simp) only: List.append_take_drop_id)

    apply(clarsimp)

(*
    apply(drule_tac 
x = " take (nat start) full_code @ word_rsplit (word_of_int (int (length vs)) :: 256 word) @  drop (32::nat) (drop (nat start) full_code)"
and y = full_code
and f = "(\<lambda> x. take 32 (drop (nat start) x))"
in arg_cong)
              apply(clarsimp)
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
              apply(rotate_tac -1) apply(drule_tac sym)

              apply( simp (no_asm_simp) only: List.append_take_drop_id)

    apply(clarsimp)
*)

           apply(drule_tac x = offset in spec) apply(drule_tac x = v in spec) apply(clarsimp)

    apply(subgoal_tac
"(offset + start + (32::int)) = (start + (32::int) + offset) ")
            apply(simp (no_asm_simp))
           apply(arith)

    apply(subgoal_tac "word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)
= take (32 :: nat) (drop (nat start) full_code)")
    apply(simp)
    apply(subgoal_tac
"(take (nat start) full_code @ take (32::nat) (drop (nat start) full_code) @ drop ((32::nat) + nat start) full_code)
= full_code") 
          apply(assumption)

    apply(subgoal_tac "take (32::nat) (drop (nat start) full_code) @  drop ((32::nat) + nat start) full_code = drop (nat start) full_code")
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
              apply(rotate_tac -1) apply(drule_tac sym)

              apply( simp (no_asm_simp) only: List.append_take_drop_id)
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
             apply(rotate_tac -1) apply(drule_tac sym)
             apply( simp (no_asm_simp) only: List.append_take_drop_id)

(* leftover subgoals *)
         apply(rule_tac word_rsplit_rcat_size)
               apply(simp (no_asm_simp) add:word_size)

    apply(subgoal_tac "word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)
= take (32 :: nat) (drop (nat start) full_code)")
    apply(simp)
    apply(subgoal_tac
"(take (nat start) full_code @ take (32::nat) (drop (nat start) full_code) @ drop ((32::nat) + nat start) full_code)
= full_code") apply(simp)
    apply(fastforce)

         apply(subgoal_tac "take (32::nat) (drop (nat start) full_code) @  drop ((32::nat) + nat start) full_code = drop (nat start) full_code")
          apply(clarsimp)


           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)

         apply(rotate_tac -1) apply(drule_tac sym) apply( simp only: List.append_take_drop_id)

         apply(rule_tac word_rsplit_rcat_size)
               apply(simp (no_asm_simp) add:word_size)

        apply(frule_tac decode'_tuple_tails_length)
        apply(clarsimp)

        apply(drule_tac s = "length vs" in HOL.sym)
    apply(simp )

    apply(subgoal_tac
"(take (nat start) full_code @ word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word) @ drop (32::nat) (drop (nat start) full_code))
= full_code")
         apply(simp)

    apply(subgoal_tac
"word_rsplit (word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)
= (take (32::nat) (drop (nat start) full_code))")
apply(simp)
    apply(subgoal_tac "take (32::nat) (drop (nat start) full_code) @  drop ((32::nat) + nat start) full_code = drop (nat start) full_code")
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
              apply(rotate_tac -1) apply(drule_tac sym)

              apply( simp (no_asm_simp) only: List.append_take_drop_id)
           apply(cut_tac n = 32 and m = "nat start" and xs = full_code in List.drop_drop)
             apply(rotate_tac -1) apply(drule_tac sym)
             apply( simp (no_asm_simp) only: List.append_take_drop_id)

        apply(rule_tac word_rsplit_rcat_size) apply(simp)
          apply(simp (no_asm_simp) add: word_size)

    apply(arith)

          apply(simp (no_asm_simp) only:)
    apply(frule_tac uint_valid_length)
      apply(arith)

        apply(frule_tac decode'_tuple_tails_length)
        apply(clarsimp)

     apply(cut_tac w = "(word_rcat (take (32::nat) (drop (nat start) full_code)) :: 256 word)"
in uint_range_size) apply(simp add:word_size)
    apply(simp  add: uint_value_valid_def)

    done
next
  case 14
  then show ?case
    apply(clarsimp)

    (* Vfarray *)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(simp add:farray_value_valid_aux_def)
     apply(case_tac n; clarsimp)
      apply(rule_tac x = "[]" in exI)  apply(rule_tac conjI)
       apply(rule_tac iht_nil)
      apply(rule_tac Estatic_easier; simp)
      apply(simp add:tuple_value_valid_aux_def)
    apply(case_tac tails'; clarsimp)
     apply(case_tac heads'; clarsimp)
     apply(case_tac a; clarsimp) apply(case_tac aa; clarsimp)
      apply(simp split:sum.splits prod.splits)
     apply(case_tac aa; clarsimp)
 apply(simp split:sum.splits prod.splits)

    (* Vtuple *)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(simp add:tuple_value_valid_aux_def)
     apply(case_tac ts; clarsimp)
      apply(rule_tac x = "[]" in exI)  apply(rule_tac conjI)
       apply(rule_tac iht_nil)
      apply(rule_tac Estatic_easier; simp)
      apply(simp add:tuple_value_valid_aux_def)
    apply(case_tac tails'; clarsimp)
     apply(case_tac heads'; clarsimp)
     apply(case_tac aa; clarsimp) apply(case_tac ab; clarsimp)
      apply(simp split:sum.splits prod.splits)
     apply(case_tac ab; clarsimp)
 apply(simp split:sum.splits prod.splits)


    (* Varray *)
     apply(clarsimp)
     apply(simp add:array_value_valid_aux_def) apply(clarsimp)
      apply(rule_tac x = "[]" in exI)  apply(rule_tac conjI)
       apply(rule_tac iht_nil)
      apply(rule_tac Estatic_easier; simp)
      apply(simp add:tuple_value_valid_aux_def)
    done

next
  case (15 t l)
  then show ?case

    apply(rule_tac conjI)
    (* Vfarray *)
    (* tails did something, let's figure out what. *)
     apply(clarsimp)
     apply(rotate_tac 2) apply(drule_tac mythin) apply(drule_tac mythin)
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
     apply(case_tac n; clarsimp)
     apply(case_tac n; clarsimp)
    apply(case_tac heads'; clarsimp)
    apply(simp add:Let_def split:if_splits sum.splits prod.splits)
    apply(clarsimp)
    apply(simp split:if_splits sum.splits prod.splits)
    apply(clarsimp)
    apply(drule_tac x = ta in spec) apply(clarsimp)
    apply(drule_tac x = nat in spec) apply(rotate_tac -1)
    apply(drule_tac x = pre1 in spec)
    apply(drule_tac x = "pre2@(take 32 (code))" in spec)
    apply(drule_tac x = "(drop 32 (code))" in spec)
    apply(drule_tac x = lista in spec) apply(drule_tac x = list in spec)
    apply(rotate_tac -1)
    apply(clarsimp)

    apply(subgoal_tac "int (min (length code) (32::nat)) = 32")
     apply(clarsimp)

    apply(subgoal_tac
"(\<exists>(count''::int) bytes'::int. decode'_dyn_tuple_tails list (replicate nat ta) lista count'' (int (length pre1), pre1 @ pre2 @ code) = Ok (l, bytes'))")
      apply(clarsimp)
(*      defer apply(fastforce) *)

    (* validity *)
       apply(frule_tac abi_decode'_type_ok)
      apply(simp add: farray_value_valid_aux_def)
      apply(rule_tac conjI)
    apply(drule_tac x = x2 in spec) apply(rotate_tac -1)
       apply(drule_tac x = "(int (length pre1) + sint (word_rcat (take (32::nat) code) :: 256 word))" in spec)
       apply(rotate_tac -1)
       apply(drule_tac x = "pre1 @ pre2 @ code" in spec) apply(clarsimp)
       apply(rotate_tac -2)
    apply(frule_tac "encode_correct_converse_valid"; simp)
(* end validity piece of proof *)

      apply(rule_tac x = "(Tsint 256) # head_types" in exI)
      apply(rule_tac x = "((sint (word_rcat (take (32::nat) code) :: 256 word)), t)#tails" in exI) 
      apply(clarsimp)

      apply(rule_tac conjI)
       apply(rule_tac iht_dynamic; simp?)
       apply(frule_tac abi_decode'_type_ok; clarsimp)

    apply(frule_tac ?a1.0 = "(Vtuple head_types heads)" in can_encode_as.cases; simp?)
           apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)

        apply(clarsimp)
    apply(cut_tac
v = "(Vtuple (Tsint (256::nat) # map abi_get_type heads) (Vsint (256::nat) (sint (word_rcat (take (32::nat) code) :: 256 word)) # heads))"
and pre = "take (length pre1 + length pre2) pre"
and code = "drop (length pre1 + length pre2) pre @ codea"
and post = post in
Estatic; simp?)
       
           apply(simp add:tuple_value_valid_aux_def)
           apply(cut_tac w= "(word_rcat (take (32::nat) code) :: 256 word)" in sint_range_size)
    apply(simp add:word_size)
          apply(simp add:sint_value_valid_def)

         apply(simp split:sum.splits)
         apply(clarsimp)

    apply(subgoal_tac
"word_rsplit (word_rcat (take (32::nat) code) :: 256 word) = take 32 code")
          apply(simp)
          apply(simp add: append_eq_conv_conj)
          apply(simp add:add.commute)

         apply(rule_tac word_rsplit_rcat_size)
         apply(simp add:word_size)

    apply(subgoal_tac
"(min (length pre) (length pre1 + length pre2)) = (length pre1 + length pre2)")
         apply(clarsimp)

    apply(subgoal_tac
"(take (length pre1 + length pre2) pre @ drop (length pre1 + length pre2) pre @ codea @ post)
=
pre @ codea @ post")
          apply(clarsimp)
         apply(clarsimp)
        apply(arith)


       apply(clarsimp)
      apply(frule_tac ht = ta in is_head_and_tail_head_types_elem; clarsimp)

     apply(fastforce)

     apply(arith)


    apply(rule_tac conjI)

    (* 
      Tuple
    *)
     apply(clarsimp)
     apply(rotate_tac 1) apply(drule_tac mythin) apply(rotate_tac 1) apply(drule_tac mythin)
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
     apply(case_tac ts; clarsimp)
     apply(case_tac ts; clarsimp)
    apply(case_tac heads'; clarsimp)
     apply(simp add:Let_def split:if_splits sum.splits prod.splits)

(* static head *)
    apply(clarsimp)
    apply(simp split:if_splits sum.splits prod.splits)
    apply(clarsimp)
    apply(drule_tac x = lista in spec) apply(clarsimp)
    apply(rotate_tac -1)
    apply(drule_tac x = pre1 in spec)
    apply(drule_tac x = "pre2 @ take (nat (abi_static_size aa)) code" in spec)
    apply(drule_tac x = "(drop (nat (abi_static_size aa)) (code))" in spec)
    apply(drule_tac x = listb in spec) apply(drule_tac x = list in spec)
    apply(rotate_tac -1)
    apply(clarsimp)

    apply(subgoal_tac
"int (min (length code) (nat (abi_static_size aa))) = abi_static_size aa") apply(clarsimp)

    apply(subgoal_tac
"(\<exists>(count'::int) bytes::int.
           decode'_dyn_tuple_heads lista (int (length pre2) + (abi_static_size aa)) (int (length pre1), pre1 @ pre2 @ code) =
           Ok (listb, list, count', bytes))")
         apply(clarsimp)

    apply(subgoal_tac
"(\<exists>(count''::int) bytes'::int.
           decode'_dyn_tuple_tails list lista listb count'' (int (length pre1), pre1 @ pre2 @ code) = Ok (l, bytes'))")
    apply(clarsimp)

(* validity *)
       apply(frule_tac abi_decode'_type_ok)
      apply(simp add: tuple_value_valid_aux_def)
      apply(rule_tac conjI)
    apply(drule_tac x = x2 in spec) apply(rotate_tac -1)
       apply(drule_tac x = "int (length pre1) + int (length pre2)" in spec)
       apply(rotate_tac -1)
       apply(drule_tac x = "pre1 @ pre2 @ code" in spec) apply(clarsimp)
       apply(rotate_tac -1)
    apply(frule_tac "encode_correct_converse_valid"; simp)
(* end validity piece of proof *)

    apply(frule_tac ?a1.0 = "(Vtuple head_types heads)" in can_encode_as.cases; simp?)
           apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)

      apply(rule_tac x = "(abi_get_type t) # head_types" in exI)
      apply(rule_tac x = "tails" in exI) 
      apply(clarsimp)

          apply(rule_tac conjI)
           apply(rule_tac iht_static; simp?)

  apply(frule_tac abi_decode'_type_ok; clarsimp)

    apply(cut_tac
v = "(Vtuple (abi_get_type t # map abi_get_type heads) (t # heads))"
and pre = "take (length pre1 + length pre2) pre"
and code = "drop (length pre1 + length pre2) pre @ codea"
and post = post in
Estatic; simp?)
       
             apply(simp add:tuple_value_valid_aux_def)
             apply(drule_tac x= x2 in spec)
    apply(rotate_tac -1)
             apply(drule_tac x = "int (length pre1) + int (length pre2)" in spec)
             apply(drule_tac x= "pre @ codea @ post" in spec)
    apply(subgoal_tac "decode' (abi_get_type t) (int (length pre1) + int (length pre2), pre @ codea @ post) = Ok (t, x2)") apply(clarsimp)
    apply(rotate_tac -2)
    apply(frule_tac encode_correct_converse_valid; clarsimp)
             apply(clarsimp)

         apply(simp split:sum.splits)
            apply(clarsimp)

    apply(subgoal_tac
"(length pre1) + ((length pre2) + nat (abi_static_size (abi_get_type t))) = length pre")

             apply(drule_tac x= x2 in spec)
    apply(rotate_tac -1)
             apply(drule_tac x = "int (length pre1) + int (length pre2)" in spec)
             apply(drule_tac x= "pre @ concat x1 @ post" in spec)
            apply(subgoal_tac "decode' (abi_get_type t) (int (length pre1) + int (length pre2), pre @ concat x1 @ post) = Ok (t, x2)")
             apply(clarsimp) apply(rotate_tac -2)
             apply(drule_tac
pre = "pre1 @ pre2"
and code = "drop (length (pre1 @ pre2)) pre"
and post = "concat x1 @ post" in
 encode_static_correct_converse; simp?)
    apply(rule_tac n = "nat (abi_static_size (abi_get_type t))" and post = code and post' = "concat x1 @ post" in list_partition3)
    apply(simp)
    apply(simp)

    apply(clarsimp)
            apply(arith)

           apply(subgoal_tac "(int (min (length pre) (length pre1 + length pre2))) = (length pre1 + length pre2)")
            apply(clarsimp)
    apply(subgoal_tac "
take (length pre1 + length pre2) pre @ drop (length pre1 + length pre2) pre @ codea @ post
= pre @ codea @ post")
    apply(simp only: append.simps)
            apply(clarsimp)
    apply(simp add: min_absorb2)
          apply(clarsimp)

          apply(frule_tac ht = ta in is_head_and_tail_head_types_elem; simp)

         apply(fastforce)
        apply(fastforce)

       apply(drule_tac x = x2 in spec)
       apply(drule_tac x = "(int (length pre1) + int (length pre2))" in spec)
       apply(drule_tac x = " pre1 @ pre2 @ code" in spec)
  apply(frule_tac abi_decode'_type_ok; clarsimp)
       apply(rotate_tac -1)
       apply(drule_tac can_encode_as.cases; simp?) apply(clarsimp)
        apply(subgoal_tac "code = codea @ post")
         apply(thin_tac "pre1 @ pre2 @ code = pre @ codea @ post")
    apply(thin_tac "int (length pre1) + int (length pre2) = int (length pre)")
         apply(clarsimp)
         apply(frule_tac encode_static_size; simp)
    apply(subgoal_tac
"(length pre1) +  (length pre2) =  (length pre)")
         apply(clarsimp)
    apply(cut_tac xs = "pre1 @ pre2"
and ys = pre
and us = "code"
and vs = "codea @ post"
in append_eq_append_conv) apply(clarsimp)
    apply(clarsimp)

    apply(arith)

       apply(simp add:list_ex_iff)

      apply(simp add:abi_static_size_nonneg)

(* dynamic head *)
    apply(clarsimp)


    apply(subgoal_tac "int (min (length code) (32::nat)) = 32")
     apply(clarsimp)

      apply(simp add:tuple_value_valid_aux_def)
    apply(simp split:sum.splits prod.splits) apply(clarsimp)
     apply(frule_tac abi_decode'_type_ok) apply(clarsimp)
     apply(drule_tac x =lista in spec) apply(clarsimp)
     apply(drule_tac x = pre1 in spec) 
apply(drule_tac x = "pre2 @ (take (32::nat) code)" in spec) apply(clarsimp)
    apply(drule_tac x = "(drop 32 (code))" in spec)
    apply(drule_tac x = listb in spec) apply(drule_tac x = list in spec)
    apply(rotate_tac -1)
     apply(clarsimp)

    apply(subgoal_tac "(\<exists>(count'::int) bytes::int. decode'_dyn_tuple_heads lista (int (length pre2) + int (min (length code) (32::nat))) (int (length pre1), pre1 @ pre2 @ code) = Ok (listb, list, count', bytes))")
    apply(clarsimp)
      apply(subgoal_tac " (\<exists>(count''::int) bytes'::int. decode'_dyn_tuple_tails list lista listb count'' (int (length pre1), pre1 @ pre2 @ code) = Ok (l, bytes'))")
       apply(clarsimp)


    (* validity *)
       apply(frule_tac abi_decode'_type_ok)
      apply(simp add: farray_value_valid_aux_def)
      apply(rule_tac conjI)
    apply(drule_tac x = x2 in spec) apply(rotate_tac -1)
       apply(drule_tac x = "(int (length pre1) + sint (word_rcat (take (32::nat) code) :: 256 word))" in spec)
       apply(rotate_tac -1)
       apply(drule_tac x = "pre1 @ pre2 @ code" in spec) apply(clarsimp)
       apply(rotate_tac -2)
    apply(frule_tac "encode_correct_converse_valid"; simp)
(* end validity piece of proof *)

      apply(rule_tac x = "(Tsint 256) # head_types" in exI)
      apply(rule_tac x = "((sint (word_rcat (take (32::nat) code) :: 256 word)), t)#tails" in exI) 
      apply(clarsimp)

      apply(rule_tac conjI)
       apply(rule_tac iht_dynamic; simp?)
       apply(frule_tac abi_decode'_type_ok; clarsimp)

    apply(frule_tac ?a1.0 = "(Vtuple head_types heads)" in can_encode_as.cases; simp?)
           apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)

        apply(clarsimp)
    apply(cut_tac
v = "(Vtuple (Tsint (256::nat) # map abi_get_type heads) (Vsint (256::nat) (sint (word_rcat (take (32::nat) code) :: 256 word)) # heads))"
and pre = "take (length pre1 + length pre2) pre"
and code = "drop (length pre1 + length pre2) pre @ codea"
and post = post in
Estatic; simp?)
       
           apply(simp add:tuple_value_valid_aux_def)
           apply(cut_tac w= "(word_rcat (take (32::nat) code) :: 256 word)" in sint_range_size)
    apply(simp add:word_size)
          apply(simp add:sint_value_valid_def)

         apply(simp split:sum.splits)
         apply(clarsimp)

    apply(subgoal_tac
"word_rsplit (word_rcat (take (32::nat) code) :: 256 word) = take 32 code")
          apply(simp)
          apply(simp add: append_eq_conv_conj)
          apply(simp add:add.commute)

         apply(rule_tac word_rsplit_rcat_size)
         apply(simp add:word_size)

    apply(subgoal_tac
"(min (length pre) (length pre1 + length pre2)) = (length pre1 + length pre2)")
         apply(clarsimp)

    apply(subgoal_tac
"(take (length pre1 + length pre2) pre @ drop (length pre1 + length pre2) pre @ codea @ post)
=
pre @ codea @ post")
          apply(clarsimp)
         apply(clarsimp)
        apply(arith)


       apply(clarsimp)
      apply(frule_tac ht = ta in is_head_and_tail_head_types_elem; clarsimp)

     apply(fastforce)

      apply(clarsimp)
apply(clarsimp)

     apply(arith)


(* Array *)
    apply(clarify)
     apply(rotate_tac 1) apply(drule_tac mythin) apply(drule_tac mythin)
    apply(clarsimp)
    apply(case_tac tails'; clarsimp)
    apply(case_tac heads'; clarsimp)

    apply(subgoal_tac " uint_value_valid (256::nat) (int (length l))")
    apply(subgoal_tac "length (word_rsplit (word_of_int (int (length l)) :: 256 word) :: 8 word list) = (32::nat)")
     apply(simp add:Let_def split:if_splits sum.splits prod.splits)

(* static elements *)
    apply(clarsimp)
    apply(simp split:if_splits sum.splits prod.splits)
    apply(clarsimp)
      apply(drule_tac x = ta in spec) apply(clarsimp)
        apply(rotate_tac -1)
    apply(drule_tac x = "n'" in spec) apply(clarsimp)
    apply(drule_tac x = pre1 in spec)
      apply(drule_tac x = "pre2 @ take (nat (abi_static_size ta)) code" in spec)

      apply(drule_tac x = "(drop (nat (abi_static_size ta)) (code))" in spec)
    apply(clarsimp)
    apply(drule_tac x = lista in spec) apply(drule_tac x = list in spec)
    apply(rotate_tac -1)

    apply(subgoal_tac
"int (min (length code) (nat (abi_static_size ta))) = abi_static_size ta") apply(clarsimp)

(*
    apply(frule_tac decode'_tuple_tails_length; clarsimp)
*)
    apply(subgoal_tac
" (\<exists>(count''::int) bytes'::int.
           decode'_dyn_tuple_tails list (replicate (length l) ta) lista count''
            (int (length pre1) + (32::int), pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2 @ code) =
           Ok (l, bytes'))")            apply(clarsimp)



(* validity *)
       apply(frule_tac abi_decode'_type_ok)
      apply(simp add: array_value_valid_aux_def)
      apply(rule_tac conjI)
    apply(drule_tac x = x2 in spec) apply(rotate_tac -1)
       apply(drule_tac x = "int (length pre1) + 32 + int (length pre2)" in spec)
       apply(rotate_tac -1)
       apply(drule_tac x = " pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2 @ code" in spec) apply(clarsimp)
       apply(rotate_tac -1)
    apply(frule_tac "encode_correct_converse_valid"; simp)
(* end validity piece of proof *)


    apply(frule_tac ?a1.0 = "(Vtuple head_types heads)" in can_encode_as.cases; simp?)
           apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)


      apply(rule_tac x = "(abi_get_type t) # head_types" in exI)
      apply(rule_tac x = "tails" in exI) 
      apply(clarsimp)

          apply(rule_tac conjI)
           apply(rule_tac iht_static; simp?)

  apply(frule_tac abi_decode'_type_ok; clarsimp)

    apply(cut_tac
v = "(Vtuple (abi_get_type t # map abi_get_type heads) (t # heads))"
and pre = "take (length pre1 + 32 + length pre2) pre"
and code = "drop (length pre1 + 32 + length pre2) pre @ codea"
and post = post in
Estatic; simp?)
       
             apply(simp add:tuple_value_valid_aux_def)
             apply(drule_tac x= x2 in spec)
    apply(rotate_tac -1)
             apply(drule_tac x = "int (length pre1) + int 32 + int (length pre2)" in spec)
             apply(drule_tac x= "pre @ codea @ post" in spec)
    apply(subgoal_tac "decode' (abi_get_type t) (int (length pre1) + int 32 + int (length pre2), pre @ codea @ post) = Ok (t, x2)") apply(clarsimp)
    apply(rotate_tac -2)
    apply(frule_tac encode_correct_converse_valid; clarsimp)
             apply(clarsimp)

         apply(simp split:sum.splits)
            apply(clarsimp)

    apply(subgoal_tac
"(length pre1) + 32 + ((length pre2) + nat (abi_static_size (abi_get_type t))) = length pre")

             apply(drule_tac x= x2 in spec)
    apply(rotate_tac -1)
             apply(drule_tac x = "int (length pre1) + 32 + int (length pre2)" in spec)
             apply(drule_tac x= "pre @ concat x1 @ post" in spec)
            apply(subgoal_tac "decode' (abi_get_type t) (int (length pre1) + 32 + int (length pre2), pre @ concat x1 @ post) = Ok (t, x2)")
             apply(clarsimp) apply(rotate_tac -2)
             apply(drule_tac
pre = "pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2"
and code = "drop (length (pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @  pre2)) pre"
and post = "concat x1 @ post" in
 encode_static_correct_converse; simp?)

    apply(cut_tac ?l1.0 = "pre1 @ word_rsplit (word_of_int (int n') :: 256 word)"
and ?l2.0 = "pre2"
and l = pre
and post = code
and post' = "concat x1 @ post"
and n = "nat (abi_static_size (abi_get_type t))"
in list_partition3)

    apply(simp)
               apply(simp)
              apply(simp)
    apply(subgoal_tac "length pre1 + (32::nat) + length pre2 =
length pre1 + ((32::nat) + length pre2)")
    apply(clarsimp)
            apply(arith)
    apply(subgoal_tac "length pre1 + (32::nat) + length pre2 =
length pre1 + ((32::nat) + length pre2)")
              apply(clarsimp)


    apply(cut_tac ?l1.0 = "pre1 @ word_rsplit (word_of_int (int n') :: 256 word)"
and ?l2.0 = "pre2"
and l = pre
and post = code
and post' = "concat x1 @ post"
and n = "nat (abi_static_size (abi_get_type t))"
in list_partition3)

    apply(simp)
               apply(simp)
              apply(simp)
    apply(subgoal_tac " 
length pre1 + ((32::nat) + length pre2) = length pre1 + (32::nat) + length pre2")
    apply(simp only:)
            apply(arith)
    apply(subgoal_tac "length pre1 + (32::nat) + length pre2 =
length pre1 + ((32::nat) + length pre2)")
    apply(clarsimp)
            apply(arith)

            apply(clarsimp)

           apply(arith)

           apply(subgoal_tac "(int (min (length pre) (length pre1 + length pre2))) = (length pre1 + length pre2)")
            apply(clarsimp)
    apply(subgoal_tac "
take (length pre1 + 32 + length pre2) pre @ drop (length pre1 + 32 + length pre2) pre @ codea @ post
= pre @ codea @ post")
    apply(simp only: append.simps)
            apply(clarsimp)
    apply(simp add: min_absorb2)
          apply(clarsimp)
          apply(arith)

    apply(clarsimp)
          apply(frule_tac ht = ta in is_head_and_tail_head_types_elem; simp)

         apply(fastforce)

       apply(drule_tac x = x2 in spec)
       apply(drule_tac x = "(int (length pre1) + 32 + int (length pre2))" in spec)
       apply(drule_tac x = " pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2 @ code" in spec)
  apply(frule_tac abi_decode'_type_ok; clarsimp)
       apply(rotate_tac -1)
       apply(drule_tac can_encode_as.cases; simp?) apply(clarsimp)
        apply(subgoal_tac "code = codea @ post")
         apply(thin_tac "pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @  pre2 @ code = pre @ codea @ post")
    apply(thin_tac "int (length pre1) + 32 + int (length pre2) = int (length pre)")
         apply(clarsimp)
         apply(frule_tac encode_static_size; simp)
    apply(subgoal_tac
"(length pre1) + 32 +  (length pre2) =  (length pre)")
         apply(clarsimp)
    apply(cut_tac xs = "pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2"
and ys = pre
and us = "code"
and vs = "codea @ post"
in append_eq_append_conv) apply(clarsimp)
    apply(clarsimp)

    apply(arith)

       apply(simp add:list_ex_iff)

      apply(simp add:abi_static_size_nonneg)


(*
    apply(simp add: uint_value_valid_def)

      apply(simp add:abi_static_size_nonneg)
*)

(* dynamic *)
    apply(clarsimp)


    apply(subgoal_tac "int (min (length code) (32::nat)) = 32")
     apply(clarsimp)

      apply(simp add:array_value_valid_aux_def)
    apply(simp split:sum.splits prod.splits) apply(clarsimp)
     apply(frule_tac abi_decode'_type_ok) apply(clarsimp)
       apply(drule_tac x ="abi_get_type t" in spec) apply(clarsimp)
    apply(drule_tac x = n' in spec) apply(clarsimp)
     apply(drule_tac x = "pre1" in spec) 
     apply(drule_tac x = "pre2 @ (take (32::nat) code)" in spec) apply(clarsimp)
(*     apply(drule_tac x = count in spec) apply(clarsimp)
    apply(subgoal_tac "uint_value_valid (256::nat) (int (length l))") apply(clarsimp) *)
    apply(drule_tac x = "(drop 32 (code))" in spec) apply(clarsimp)


    apply(subgoal_tac "(\<exists>(count''::int) bytes'::int.
           decode'_dyn_tuple_tails list (replicate (length l) (abi_get_type t)) lista count''
            (int (length pre1) + (32::int), pre1 @ word_rsplit (word_of_int (int n') :: 256 word) @ pre2 @ code) =
           Ok (l, bytes'))")     apply(clarsimp)

    (* validity *)
       apply(frule_tac abi_decode'_type_ok)
      apply(simp add: farray_value_valid_aux_def)
      apply(rule_tac conjI)
    apply(drule_tac x = x2 in spec) apply(rotate_tac -1)
       apply(drule_tac x = "(int (length pre1) + 32 + sint (word_rcat (take (32::nat) code) :: 256 word))" in spec)
       apply(rotate_tac -1)
       apply(drule_tac x = "pre1 @ (word_rsplit (word_of_int (int n') :: 256 word)) @ pre2 @ code" in spec) apply(clarsimp)
       apply(rotate_tac -2)
    apply(frule_tac "encode_correct_converse_valid"; simp)
(* end validity piece of proof *)

      apply(rule_tac x = "(Tsint 256) # head_types" in exI)
      apply(rule_tac x = "((sint (word_rcat (take (32::nat) code) :: 256 word)), t)#tails" in exI) 
      apply(clarsimp)

      apply(rule_tac conjI)
       apply(rule_tac iht_dynamic; simp?)
       apply(frule_tac abi_decode'_type_ok; clarsimp)

    apply(frule_tac ?a1.0 = "(Vtuple head_types heads)" in can_encode_as.cases; simp?)
           apply(clarsimp) apply(simp add:tuple_value_valid_aux_def)

        apply(clarsimp)
    apply(cut_tac
v = "(Vtuple (Tsint (256::nat) # map abi_get_type heads) (Vsint (256::nat) (sint (word_rcat (take (32::nat) code) :: 256 word)) # heads))"
and pre = "take (length pre1 + 32 + length pre2) pre"
and code = "drop (length pre1 + 32 + length pre2) pre @ codea"
and post = post in
Estatic; simp?)
       
          apply(simp add:tuple_value_valid_aux_def)
           apply(cut_tac w= "(word_rcat (take (32::nat) code) :: 256 word)" in sint_range_size)
    apply(simp add:word_size)
          apply(simp add:sint_value_valid_def)

         apply(simp split:sum.splits)
         apply(clarsimp)

    apply(subgoal_tac
"word_rsplit (word_rcat (take (32::nat) code) :: 256 word) = take 32 code")
          apply(simp)
          apply(simp add: append_eq_conv_conj)
          apply(simp add:add.commute)

         apply(rule_tac word_rsplit_rcat_size)
         apply(simp add:word_size)

    apply(subgoal_tac
"(min (length pre) (length pre1 + 32 + length pre2)) = (length pre1 + 32 + length pre2)")
         apply(clarsimp)

    apply(subgoal_tac
"(take (length pre1 + 32 + length pre2) pre @ drop (length pre1 + 32 + length pre2) pre @ codea @ post)
=
pre @ codea @ post")
          apply(clarsimp)
         apply(clarsimp)
        apply(arith)


       apply(clarsimp)
      apply(frule_tac ht = ta in is_head_and_tail_head_types_elem; clarsimp)

      apply(fastforce)

    apply(simp add:uint_value_valid_def)

     apply(clarsimp)


     apply(simp add:uint_valid_length)

    apply(simp add:uint_value_valid_def)
    done
qed

lemma abi_decode_succeed_converse_clause1 :
  assumes H1 : "decode' t (start, full_code) = Ok (v, len)"
  assumes H2 : "abi_type_valid t"
  assumes H3 : "abi_get_type v = t"
  shows  "can_encode_as v full_code (start)"
proof(-)

  have "decode' t (start, full_code) = Ok (v::abi_value, len) \<Longrightarrow> abi_type_valid t \<Longrightarrow> abi_get_type v = t \<Longrightarrow> can_encode_as v full_code start"
    using conjE[OF abi_decode_succeed_converse_gen[of v "[]"]] by(clarify; fast)

  thus ?thesis using H1 H2 H3 by auto
qed


(* idea here is that we need to discharge the premises of
the inductive version. but we have other lemmas that can do it. *)
lemma abi_decode_correct_converse :
  assumes H : "decode t full_code = Ok v"
  shows "can_encode_as v full_code (0)"
proof(-)

  have 0 : "abi_type_valid t" using H by(simp split:if_splits)

  have 1 : "\<exists> len . decode' t (0, full_code) = Ok (v, len)" using H 
    by(simp split:if_splits sum.splits prod.splits)

  then obtain len where 2 : "decode' t (0, full_code) = Ok (v, len)" ..

  have 3 : "abi_get_type v = t" using abi_decode'_type_ok[OF 2] by auto

  show ?thesis using abi_decode_succeed_converse_clause1[OF 2 0 3] by assumption
qed

end