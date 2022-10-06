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

(* NB: this works only because we disallow shadowing.
 *)
(*
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
*)

definition alpha_equiv_local_variables' ::
  "(name, name) oalist \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool" where
"alpha_equiv_local_variables' subst vm1 vm2 =
  (oalist_all (\<lambda> (n1, n2) .
    (case map_of vm1 n1 of
      None \<Rightarrow> False
      | Some val1 \<Rightarrow>
        (case map_of vm2 n2 of
          None \<Rightarrow> False
          | Some val2 \<Rightarrow> val1 = val2))) subst)"

(* make sure that our oalist substitution captures all the local variables. *)

definition alpha_equiv_local_variables ::
  "subst \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool" where
"alpha_equiv_local_variables subst vm1 vm2 =
  (list_all (\<lambda> subst' . alpha_equiv_local_variables' subst' vm1 vm2) subst \<and>
   list_all oalist_one_one subst \<and>
   list_all (\<lambda> (k, v) . 
    (case subst_get subst k of
      Some _ \<Rightarrow> True
      | _ \<Rightarrow> False)) vm1 \<and>
   list_all (\<lambda> (k, v) . 
    (case subst_get (map oalist_flip subst) k of
      Some _ \<Rightarrow> True
      | _ \<Rightarrow> False)) vm2)"

(* function equivalence
*)

type_synonym FunctionContext =
  \<open>(Identifier\<times> (Statement \<times> Identifier list)) list\<close>

(* TODO: make sure that the way we are making use of the "visible"
 * identifiers is correct.
 *)
definition alpha_equiv_function_contexts' ::
  "(name, name) oalist \<Rightarrow> FunctionContext \<Rightarrow> FunctionContext \<Rightarrow> bool" where
"alpha_equiv_function_contexts' subst vm1 vm2 =
  oalist_all (\<lambda> (n1, n2) .
    (case map_of vm1 n1 of
      None \<Rightarrow> False
      | Some (FunctionDefinition n1' params1 rets1 body1, ids1) \<Rightarrow>
        (case map_of vm2 n2 of
          None \<Rightarrow> False
          | Some (FunctionDefinition n2' params2 rets2 body2, ids2) \<Rightarrow> 
            (n1 = n1' \<and> n2 = n2' \<and>
            alpha_equiv_statement [to_oalist (zip ids1 ids2)] [Oalist.empty]
              (FunctionDefinition n1' params1 rets1 body1)
              (FunctionDefinition n2' params2 rets2 body2))))) subst"

definition alpha_equiv_function_contexts ::
  "subst \<Rightarrow> FunctionContext \<Rightarrow> FunctionContext \<Rightarrow> bool" where
"alpha_equiv_function_contexts subst vm1 vm2 =
  (list_all (\<lambda> subst' . alpha_equiv_function_contexts' subst' vm1 vm2) subst \<and>
   list_all (\<lambda> (k, v) . 
    (case subst_get subst k of
      Some _ \<Rightarrow> True
      | _ \<Rightarrow> False)) vm1 \<and>
   list_all (\<lambda> (k, v) . 
    (case subst_get (map oalist_flip subst) k of
      Some _ \<Rightarrow> True
      | _ \<Rightarrow> False)) vm2)"

(* TODO: ignoring builtins for now *)
definition alpha_equiv_yulcontext ::
  "subst \<Rightarrow> subst \<Rightarrow> 'g yulcontext \<Rightarrow> 'g yulcontext \<Rightarrow> bool" where
"alpha_equiv_yulcontext fsubst vsubst c1 c2 =
 (GlobalState c1 = GlobalState c2 \<and>
  alpha_equiv_Result (Status c1) (Status c2) \<and>
  alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)\<and>
  alpha_equiv_function_contexts fsubst (Functions c1) (Functions c2))"

(* result of running the state monad *)
type_synonym ('g, 'a) yulout = "('a * 'g yulcontext)"

(* for unpacking the State constructor *)
type_synonym ('g, 'a) yulstatef = "'g yulcontext \<Rightarrow> ('a * 'g yulcontext)"

lemma alpha_equiv_getLocalVariable :
  assumes "alpha_equiv_local_variables vsubst lv1 lv2"
  assumes "LocalVariables c1 = lv1"
  assumes "LocalVariables c2 = lv2"
  assumes "alpha_equiv_name vsubst id1 id2"
  shows "getLocalVariable c1 id1 = getLocalVariable c2 id2"
  using assms
  sorry
(*
proof(induction lv1 arbitrary: vsubst lv2 c1 c2 id1 id2)
  case Nil1 : Nil
  then show ?case
    apply(auto simp add: alpha_equiv_local_variables_def)
next
  case (Cons substh substt)
  show ?case
  proof(cases "get substh id1")
    case None1 : None

    show ?thesis
    proof(cases "get (oalist_flip substh) id2")
      case None2 : None
      then show ?thesis
        using Cons None1
        apply(auto simp add: alpha_equiv_local_variables_def)
    next
      case (Some a)
      then show ?thesis sorry
    qed

    then show ?thesis
      using Cons
      apply(auto simp add: alpha_equiv_local_variables_def)
    then show ?thesis sorry
  next
    case Some1 : (Some id1')

    show ?thesis
      using Cons
      apply(auto simp add: alpha_equiv_local_variables_def)

    then show ?thesis sorry
  qed

  then show ?case
    apply(auto simp add: alpha_equiv_local_variables_def)
qed
*)

(* State_Monad.state.rel_state :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c, 'a) state \<Rightarrow> ('c, 'b) state \<Rightarrow> bool" *)
(* run_state :: "('s, 'a) state \<Rightarrow> 's \<Rightarrow> 'a \<times> 's" *)

lemma alpha_equiv_correct :
  shows "(\<forall> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext).
  ((\<forall> st1 st2 m m1 m2 c1' c2'. 
    alpha_equiv_statement fsubst vsubst st1 st2 \<longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<longrightarrow>
    run_state (evalStatement n m st1) c1 = (m1, c1') \<longrightarrow>
    run_state (evalStatement n m st2) c2 = (m2, c2') \<longrightarrow>
    (alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> m1 = m2)) \<and>
   (\<forall> e1 e2 c1' c2' vals1 vals2.
    alpha_equiv_expr fsubst vsubst e1 e2 \<longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<longrightarrow>
    run_state (evalExpression n e1) c1 = (vals1, c1') \<longrightarrow>
    run_state (evalExpression n e2) c2 = (vals2, c2') \<longrightarrow>
    (alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> vals1 = vals2)) \<and>
   (\<forall> e1 e2 c1' c2' v1 v2.
    alpha_equiv_expr fsubst vsubst e1 e2 \<longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<longrightarrow>
    run_state (evalUnaryExpression n e1) c1 = (v1, c1') \<longrightarrow>
    run_state (evalUnaryExpression n e2) c2 = (v2, c2') \<longrightarrow>
    (alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> v1 = v2))))"
proof(induction n)
  case 0
  then show ?case 
(* TODO: make this nicer and not rely on case_tac *)
    by(auto simp add: run_state_def errorState_def alpha_equiv_yulcontext_def;
        case_tac m; auto simp add: errorState_def State_Monad.return_def)
next
  case (Suc n)

  have IH1 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) st1 st2 m m1 m2 c1' c2'.
         alpha_equiv_statement fsubst vsubst
          st1 st2 \<Longrightarrow>
         alpha_equiv_yulcontext fsubst vsubst
          c1 c2 \<Longrightarrow>
         run_state (evalStatement n m st1) c1 =
         (m1, c1') \<Longrightarrow>
         run_state (evalStatement n m st2) c2 =
         (m2, c2') \<Longrightarrow>
         alpha_equiv_yulcontext fsubst vsubst
          c1' c2' \<and>
         m1 = m2"
    using Suc.IH
    by fast

  have IH2 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) e1 e2 c1' c2' vals1 vals2.
      alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
      alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
      run_state (evalExpression n e1) c1 = (vals1, c1') \<Longrightarrow>
      run_state (evalExpression n e2) c2 = (vals2, c2') \<Longrightarrow>
      alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> vals1 = vals2"
    using Suc.IH
    by fast

  have IH3 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) e1 e2 c1' c2' v1 v2.
    alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
    run_state (evalUnaryExpression n e1) c1 = (v1, c1') \<Longrightarrow>
    run_state (evalUnaryExpression n e2) c2 = (v2, c2') \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> v1 = v2"
    using Suc.IH
    by fast

  have Conc1 : 
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext)
        st1 st2 m m1 m2 c1' c2'.
          alpha_equiv_statement fsubst vsubst st1 st2 \<Longrightarrow>
          alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
          run_state (evalStatement (Suc n) m st1) c1 = (m1, c1') \<Longrightarrow>
          run_state (evalStatement (Suc n) m st2) c2 = (m2, c2') \<Longrightarrow>
          alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
          m1 = m2"
  proof-
    fix fsubst vsubst
    fix c1 c2 :: "'g yulcontext"
    fix st1 st2 m m1 m2 c1' c2'

    assume Hstatement : "alpha_equiv_statement fsubst vsubst st1 st2"
    assume Hctx : "alpha_equiv_yulcontext fsubst vsubst c1 c2"
    assume Hrun1 : "run_state (evalStatement (Suc n) m st1) c1 = (m1, c1')"
    assume Hrun2 : "run_state (evalStatement (Suc n) m st2) c2 = (m2, c2')"

    show "alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
       m1 = m2"
      sorry
  qed

  have Conc2 : 
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext)
      e1 e2 c1' c2' vals1 vals2.
        alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
        alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
        run_state (evalExpression (Suc n) e1) c1 = (vals1, c1') \<Longrightarrow>
        run_state (evalExpression (Suc n) e2) c2 = (vals2, c2') \<Longrightarrow>
        alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
        vals1 = vals2"
  proof-
    fix fsubst vsubst
    fix c1 c2 :: "'g yulcontext"
    fix e1 e2 c1' c2' vals1 vals2

    assume Hexpr : "alpha_equiv_expr fsubst vsubst e1 e2" 
    assume Hctx : "alpha_equiv_yulcontext fsubst vsubst c1 c2"
    assume Hrun1 : "run_state (evalExpression (Suc n) e1) c1 = (vals1, c1')"
    assume Hrun2 : "run_state (evalExpression (Suc n) e2) c2 = (vals2, c2')"

    show "alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
       vals1 = vals2"
    proof(cases e1)
      case Fc1 : (FunctionCall x11 x12)
      then show ?thesis sorry
    next
      case Id1 : (Identifier i1)

      then obtain i2 where Id2 : "e2 = Identifier i2"
        using Hexpr
        by(cases e2; auto)

      show ?thesis
      proof(cases "getLocalVariable c1 i1")
        case None1 : None

(* need lemma relating getLocalVariable to alpha_equiv_local_variables *)
        then have None2 : "getLocalVariable c2 i2 = None"
          using Hexpr Hrun1 Hrun2 Id1 Id2 Hctx
          apply(cases "getLocalVariable c2 i2"; auto simp add: errorState_def alpha_equiv_yulcontext_def ValueOfIdentifier_def)
        then show ?thesis
          using Hexpr Hrun1 Hrun2 Id1 Id2
          apply(auto simp add: errorState_def alpha_equiv_yulcontext_def ValueOfIdentifier_def)

      next
        case (Some a)
        then show ?thesis sorry
      qed

(* get_local_variable *)
      then show ?thesis using Hexpr Hctx Hrun1 Hrun2 Id1
        apply(auto simp add: ValueOfIdentifier_def)


      then show ?thesis sorry
    next
      case L1 : (Literal v1)

      then obtain v2 where L2 : "e2 = Literal v2"
        using Hexpr
        by(cases e2; auto)

      then show ?thesis using Hexpr Hctx Hrun1 Hrun2 L1
        by(auto)
    qed
  qed

  have Conc3 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) e1 e2 c1' c2' v1 v2.
          alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
          alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
          run_state (evalUnaryExpression (Suc n) e1) c1 = (v1, c1') \<Longrightarrow>
          run_state (evalUnaryExpression (Suc n) e2) c2 = (v2, c2') \<Longrightarrow>
          alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
          v1 = v2"
  proof-
    fix fsubst vsubst
    fix c1 c2 :: "'g yulcontext"
    fix e1 e2 c1' c2' v1 v2

    assume Hexpr : "alpha_equiv_expr fsubst vsubst e1 e2" 
    assume Hctx : "alpha_equiv_yulcontext fsubst vsubst c1 c2"
    assume Hrun1 : "run_state (evalUnaryExpression (Suc n) e1) c1 = (v1, c1')"
    assume Hrun2 : "run_state (evalUnaryExpression (Suc n) e2) c2 = (v2, c2')"

    obtain rest1 :: "('g, Value list) yulstatef" where Rest1 :
      "evalExpression n e1 = State rest1"
      by(cases "evalExpression n e1 :: ('g, Value list) yulstate"; auto)

    obtain rest2 :: "('g, Value list) yulstatef" where Rest2 :
      "evalExpression n e2 = State rest2"
      by(cases "evalExpression n e2 :: ('g, Value list) yulstate"; auto)

    obtain v1a c1a where Run1a : "run_state (evalExpression n e1) c1 = (v1a, c1a)"
      by force

    obtain v2a c2a where Run2a : "run_state (evalExpression n e2) c2 = (v2a, c2a)"
      by force

    have IndHyp : "alpha_equiv_yulcontext fsubst vsubst c1a c2a" "v1a = v2a"
      using IH2[OF Hexpr Hctx Run1a Run2a] 
      by auto

    show "alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and>
       v1 = v2"
    proof(cases v1a)
      case V1a_Nil : Nil

      have V2a_Nil : "v2a = []"
        using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Nil
        using IndHyp
        by(cases v2a; auto)

      then show ?thesis
        using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Nil 
        using IndHyp
        by(auto simp add: errorState_def alpha_equiv_yulcontext_def)
    next
      case V1a_Cons1 : (Cons v1ah v1at)

      obtain v2ah v2at where V2a_Cons1 : "v2a = v2ah # v2at"
        using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Cons1 
        using IndHyp
        by(cases v2a; auto)

      show ?thesis
      proof(cases v1at)
        case V1at_Nil : Nil

        have V2at_Nil : "v2at = []"
          using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1at_Nil V1a_Cons1 V2a_Cons1
          using IndHyp
          by(cases v2at; auto)
  
        then show ?thesis
          using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Cons1 V2a_Cons1 
          using IndHyp
          by(auto simp add: errorState_def alpha_equiv_yulcontext_def)

      next
        case V1a_Cons2 : (Cons v1ah' v1at')

        obtain v2ah' v2at' where V2a_Cons2 : "v2at = v2ah' # v2at'"
          using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Cons1 V2a_Cons1 V1a_Cons2
          using IndHyp
          by(cases v2at; auto)

        then show ?thesis
          using Hexpr Hctx Hrun1 Hrun2 Run1a Run2a V1a_Cons1 V2a_Cons1 V1a_Cons2
          using IndHyp
          by(auto simp add: errorState_def alpha_equiv_yulcontext_def)
      qed
    qed
  qed

  show ?case sorry
(*
    using Conc1 Conc2 Conc3
    by fast
*)
qed


end