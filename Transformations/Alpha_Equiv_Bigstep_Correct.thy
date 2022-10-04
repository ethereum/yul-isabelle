theory Alpha_Equiv_Bigstep_Correct 
  imports Alpha_Equiv_Bigstep
begin

(*
 * we need a way of relating contexts.
 * we need an equivalent of MiniYul's varmap/varmap'
*)

fun alpha_equiv_Result ::
  "Result \<Rightarrow> Result \<Rightarrow> bool" where
"alpha_equiv_Result Sucess Success = True"
| "alpha_equiv_Result (Error _) (Error _) = True"
| "alpha_equiv_Result OutOfGas OutOfGas = True"
| "alpha_equiv_Result _ _ = False"

(*
 * 
 *)

(* TODO: should we care about the order of locals?
 * should we make sure all variables in l1 and l2 are accounted for? *)

fun alpha_equiv_local_variables'l ::
  "(name * name) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool" where
"alpha_equiv_local_variables'l [] vm1 vm2 = True"
| "alpha_equiv_local_variables'l ((nh1, nh2) # nt) vm1 vm2 =
  (case map_of vm1 nh1 of
   None \<Rightarrow> False
   | Some val1 \<Rightarrow>
    (case map_of vm2 nh2 of
     None \<Rightarrow> False
     | Some val2 \<Rightarrow>
      (val1 = val2 \<and> alpha_equiv_local_variables'l nt vm1 vm2)))"

lift_definition alpha_equiv_local_variables' ::
  "(name, name) oalist \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool"
is alpha_equiv_local_variables'l
  .

fun alpha_equiv_local_variables ::
  "subst \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool" where
"alpha_equiv_local_variables [] [] [] = True"
| "alpha_equiv_local_variables (sh#st) (v1h#v1t) (v2h#v2t) =
   (alpha_equiv_local_variables' sh v1h v2h \<and>
    \<comment> \<open>oalist_len sh = oalist_len v1h \<and> \<close>
    oalist_keys sh = oalist_keys v1h \<and>
    \<comment> \<open> oalist_len sh = oalist_len v2h \<and> \<close>
    oalist_one_one sh \<and>
    oalist_keys (oalist_flip sh) = oalist_keys v2h \<and>
    alpha_equiv_local_variables st v1t v2t)"
| "alpha_equiv_local_variables _ _ _ = False"


(* TODO: ignoring builtins for now *)
definition alpha_equiv_yulcontext ::
  "subst \<Rightarrow> subst \<Rightarrow> 'g yulcontext \<Rightarrow> 'g yulcontext \<Rightarrow> bool" where
"alpha_equiv_yulcontext fsubst vsubst c1 c2 =
 (GlobalState c1 = GlobalState c2 \<and>
  alpha_equiv_Result (Status c1) (Status c2)
  \<comment> \<open>alpha_equiv_local_variables subst (LocalVariables c1) (LocalVariables c2)\<and>
      alpha_equiv_functions fvusbst vsubst (Functions c1) (Functions c2)\<close>)"
  

end