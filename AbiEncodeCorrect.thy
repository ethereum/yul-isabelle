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
lemma abi_encode_succeed_gen_new :
  "(\<forall>  code pre post . encode v = Ok code \<longrightarrow>
          (can_encode_as v (pre @ code @ post) (int (length pre)) (int (length (pre @ code))))) \<and>
   (
    (
     (\<forall> t n code pre post . 
          abi_type_isstatic t \<longrightarrow>
          encode (Vfarray t n vs) = Ok code \<longrightarrow>
          (can_encode_as_list vs (pre @ code @ post) (int (length pre)) (int (length (pre @ code))))) \<and>
     (\<forall> ts code pre post .
          (\<forall> t . t \<in> set ts \<longrightarrow> abi_type_isstatic t) \<longrightarrow>
          encode (Vtuple ts vs) = Ok code \<longrightarrow>
          (can_encode_as_list vs (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))))) \<and>
    (
     (\<forall> t n code pre post .
          abi_type_isdynamic t \<longrightarrow>
          encode (Vfarray t n vs) = Ok code \<longrightarrow>
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
proof(induction rule: my_abi_value_induct)
case (1 n i)
  then show ?case 
    apply(clarify)
    apply(rule_tac Euint)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (2 n i)
  then show ?case
    apply(clarify)
    apply(rule_tac Esint)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (3 i)
  then show ?case
    apply(clarify)
    apply(rule_tac Eaddr)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (4 b)
  then show ?case
    apply(clarify)
    apply(rule_tac Ebool)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (5 m n r)
  then show ?case
    apply(clarify)
    apply(rule_tac Efixed)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (6 m n r)
  then show ?case 
    apply(clarify)
    apply(rule_tac Eufixed)
     apply(auto simp add:encode_def split:if_split_asm)
    done
next
  case (7 n bs)
  then show ?case 
    apply(clarify)
    apply(rule_tac Efbytes)
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
    apply(clarify)
      apply(case_tac "abi_type_isdynamic t"; clarsimp)
    apply(rule_tac Efarray_dyn)
      defer defer
       apply(simp add:encode_def)
      apply(rule_tac Efarray_static)
        defer
        apply(simp)
       apply(simp)
    sorry
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
  then show ?case apply(simp add:encode_def)
    apply(auto intro:Elnil_static Elnil_dyn)
    sorry
next
  case (15 t l)
  then show ?case
    apply(auto)
    apply(rule_tac pre_and_v_code_len = "int (length pre + length code)" in Elcons_static)

         apply(simp add:encode_def)
         apply(simp only: split:if_split_asm sum.split_asm)
           apply(clarsimp)
         apply(case_tac "those_err (encode_static t # map encode_static l)") apply(clarsimp)

    sorry
qed



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