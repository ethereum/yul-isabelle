theory Alpha_Equiv_Bigstep_Correct 
  imports Alpha_Equiv_Bigstep
begin

(*
 * we need a way of relating contexts.
 * we need an equivalent of MiniYul's varmap/varmap'
*)

fun alpha_equiv_Result ::
  "Result \<Rightarrow> Result \<Rightarrow> bool" where
"alpha_equiv_Result Success Success = True"
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

definition alpha_equiv_local_variables ::
  "(name * name) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> (Identifier * Value) list \<Rightarrow> bool" where
"alpha_equiv_local_variables subst vm1 vm2 =
  (subst = zip (map fst vm1) (map fst vm2) \<and>
   map snd vm1 = map snd vm2)"

(* function equivalence
*)

type_synonym FunctionContext =
  \<open>(Identifier\<times> (Statement \<times> Identifier list)) list\<close>

type_synonym 'g BuiltinContext =
  \<open>Identifier \<Rightarrow> ('g BuiltinFunction) option\<close>

definition alpha_equiv_function_context_elem ::
  "(Identifier\<times> (Statement \<times> Identifier list)) \<Rightarrow> (Identifier\<times> (Statement \<times> Identifier list)) \<Rightarrow> bool" where
"alpha_equiv_function_context_elem fe1 fe2 =
  (case fe1 of
    (n1, FunctionDefinition n1' params1 rets1 body1, ids1) \<Rightarrow>
    (case fe2 of
      (n2, FunctionDefinition n2' params2 rets2 body2, ids2) \<Rightarrow>
        (n1 = n1' \<and> n2 = n2' \<and>
        alpha_equiv_statement (zip ids1 ids2) []
          (FunctionDefinition n1' params1 rets1 body1)
          (FunctionDefinition n2' params2 rets2 body2))        
    | _ \<Rightarrow> False)
  | _ \<Rightarrow> False)" 

(* TODO: make sure that the way we are making use of the "visible"
 * identifiers is correct.
 *)
definition alpha_equiv_function_contexts ::
  "(name * name) list \<Rightarrow> FunctionContext \<Rightarrow> FunctionContext \<Rightarrow> bool" where
"alpha_equiv_function_contexts subst vm1 vm2 =
  (subst = zip (map fst vm1) (map fst vm2) \<and>
   list_all2
    alpha_equiv_function_context_elem vm1 vm2)"

definition alpha_equiv_builtin_contexts ::
   "(name * name) list \<Rightarrow> 'g BuiltinContext \<Rightarrow> 'g BuiltinContext \<Rightarrow> bool" where
"alpha_equiv_builtin_contexts subst vm1 vm2 =
  ((\<forall> n f . vm1 n = Some f \<longrightarrow> n \<in> set (map fst subst)) \<and>
   (\<forall> n f . vm2 n = Some f \<longrightarrow> n \<in> set (map snd subst)) \<and>
   list_all (\<lambda> (n1, n2) . vm1 n1 = vm2 n2) subst)"

lemma alpha_equiv_builtin_contextsI :
  fixes vm1 vm2 :: "'g BuiltinContext"
  assumes "\<And> n f . vm1 n = Some f \<Longrightarrow> n \<in> set (map fst subst)" 
  assumes "\<And> n f . vm2 n = Some f \<Longrightarrow> n \<in> set (map snd subst)"
  assumes "list_all (\<lambda> (n1, n2) . vm1 n1 = vm2 n2) subst"
  shows "alpha_equiv_builtin_contexts subst vm1 vm2"
  using assms
  unfolding alpha_equiv_builtin_contexts_def
  by blast

lemma alpha_equiv_builtin_contextsD :
  fixes vm1 vm2 :: "'g BuiltinContext"
  assumes "alpha_equiv_builtin_contexts subst vm1 vm2"
  shows
  "\<And> n f . vm1 n = Some f \<Longrightarrow> n \<in> set (map fst subst)" 
  "\<And> n f . vm2 n = Some f \<Longrightarrow> n \<in> set (map snd subst)"
  "list_all (\<lambda> (n1, n2) . vm1 n1 = vm2 n2) subst"
  using assms
  unfolding alpha_equiv_builtin_contexts_def
  by(auto)

definition alpha_equiv_yulcontext ::
  "subst \<Rightarrow> subst \<Rightarrow> 'g yulcontext \<Rightarrow> 'g yulcontext \<Rightarrow> bool" where
"alpha_equiv_yulcontext fsubst vsubst c1 c2 =
 (GlobalState c1 = GlobalState c2 \<and>
  alpha_equiv_Result (Status c1) (Status c2) \<and>
  alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)\<and>
  alpha_equiv_function_contexts fsubst (Functions c1) (Functions c2) \<and>
  alpha_equiv_builtin_contexts fsubst (BuiltinFunctions c1) (BuiltinFunctions c2))"

lemma alpha_equiv_yulcontextI :
  assumes "GlobalState c1 = GlobalState c2"
  assumes "alpha_equiv_Result (Status c1) (Status c2)"
  assumes "alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)"
  assumes "alpha_equiv_function_contexts fsubst (Functions c1) (Functions c2)"
  assumes "alpha_equiv_builtin_contexts fsubst (BuiltinFunctions c1) (BuiltinFunctions c2)"
  shows "alpha_equiv_yulcontext fsubst vsubst c1 c2"
  using assms
  unfolding alpha_equiv_yulcontext_def
  by auto

lemma alpha_equiv_yulcontextD :
  assumes "alpha_equiv_yulcontext fsubst vsubst c1 c2"
  shows 
    "GlobalState c1 = GlobalState c2"
    "alpha_equiv_Result (Status c1) (Status c2)"
    "alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)"
    "alpha_equiv_function_contexts fsubst (Functions c1) (Functions c2)"
    "alpha_equiv_builtin_contexts fsubst (BuiltinFunctions c1) (BuiltinFunctions c2)"
  using assms
  unfolding alpha_equiv_yulcontext_def
  by auto

lemma find_map_of :
  "map_option snd (find (\<lambda> (declaredName,_) . declaredName = idn) l) =
   map_of l idn"
proof(induction l arbitrary: idn)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh : "lh = (lhk, lhv)"
    by(cases lh; auto)

  show ?case using Cons Lh
    by(auto)
qed

lemma find_map_of_alt :
  "find (\<lambda>(name, _). name = k) l = 
   (case map_of l k of
    None \<Rightarrow> None
    | Some v \<Rightarrow> Some (k, v))"
proof(induction l arbitrary: k)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh : "lh = (lhk, lhv)"
    by(cases lh; auto)

  show ?case using Cons Lh
    by(auto)
qed

lemma getLocalVariable_alt_def :
  shows "getLocalVariable c n = map_of (LocalVariables c) n"
  unfolding getLocalVariable_def
  by(auto simp add: find_map_of)

(* result of running the state monad *)
type_synonym ('g, 'a) yulout = "('a * 'g yulcontext)"

(* for unpacking the State constructor *)
type_synonym ('g, 'a) yulstatef = "'g yulcontext \<Rightarrow> ('a * 'g yulcontext)"

lemma alpha_equiv_getLocalVariable' :
  assumes "alpha_equiv_local_variables vsubst lv1 lv2"
  assumes "LocalVariables c1 = lv1"
  assumes "LocalVariables c2 = lv2"
  assumes "alpha_equiv_name vsubst id1 id2"
  shows "getLocalVariable c1 id1 = getLocalVariable c2 id2"
  using assms
proof(induction vsubst arbitrary: lv1 lv2 c1 c2 id1 id2)
  case Nil1 : Nil
  then show ?case
    by(auto simp add: alpha_equiv_local_variables_def getLocalVariable_def)
next
  case (Cons substh substt)

  obtain substhn1 substhn2 where Substh : "substh = (substhn1, substhn2)"
    by(cases substh; auto)

  obtain lv1h lv1t where Lv1 : "lv1 = lv1h # lv1t"
    using Cons.prems
    by(cases lv1; auto simp add: alpha_equiv_local_variables_def)

  obtain lv1hk lv1hv where Lv1h : "lv1h = (lv1hk, lv1hv)"
    by(cases lv1h; auto)

  obtain lv2h lv2t where Lv2 : "lv2 = lv2h # lv2t"
    using Cons.prems
    by(cases lv2; auto simp add: alpha_equiv_local_variables_def)

  obtain lv2hk lv2hv where Lv2h : "lv2h = (lv2hk, lv2hv)"
    by(cases lv2h; auto)

  show ?case
  proof(cases "id1 = lv1hk")
    case Eq1 : True
    then show ?thesis
      using Cons Substh Lv1 Lv1h Lv2 Lv2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def getLocalVariable_alt_def split: option.splits)
  next
    case Neq1 : False

    show ?thesis
    proof(cases "id2 = lv2hk")
      case Eq2 : True
      then show ?thesis
        using Cons Substh Lv1 Lv1h Lv2 Lv2h Neq1
        by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def getLocalVariable_alt_def flip_def split: option.splits)
    next
      case Neq2 : False
      then show ?thesis
        using Cons.prems Cons.IH[of lv1t lv2t "c1 \<lparr> LocalVariables := lv1t \<rparr>" "c2 \<lparr> LocalVariables := lv2t \<rparr>"] Substh Lv1 Lv1h Lv2 Lv2h Neq1
        by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def getLocalVariable_alt_def flip_def split: option.splits)
    qed
  qed
qed

lemma alpha_equiv_getLocalVariable :
  assumes "alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)"
  assumes "alpha_equiv_name vsubst id1 id2"
  shows "getLocalVariable c1 id1 = getLocalVariable c2 id2"
  using assms alpha_equiv_getLocalVariable'
  by blast

lemma alpha_equiv_name_In :
  assumes "alpha_equiv_name subst n1 n2"
  shows "(n1, n2) \<in> set subst"
  using assms
proof(induction subst arbitrary: n1 n2)
  case Nil
  then show ?case
    by(auto simp add: alpha_equiv_name_def)
next
  case (Cons substh substt)

  obtain substh1 substh2 where Substh : "substh = (substh1, substh2)"
    by force

  show ?case
  proof(cases "substh1 = n1")
    case Eq1 : True

    show ?thesis
    proof(cases "n2 = substh2")
      case Eq2 : True
      then show ?thesis using Cons Substh Eq1
        by(auto simp add: alpha_equiv_name_def flip_def)
    next
      case Neq2 : False
      then show ?thesis using Cons Substh Eq1
        by(cases "map_of (map (\<lambda>(x, y). (y, x)) substt) n2"; auto simp add: alpha_equiv_name_def flip_def)
    qed
  next
    case Neq1 : False

    show ?thesis
    proof(cases "n2 = substh2")
      case Eq2 : True
      then show ?thesis using Cons Substh Neq1
        by(cases "map_of substt n1"; auto simp add: alpha_equiv_name_def flip_def)
    next
      case Neq2 : False
      then show ?thesis using Cons Substh Neq1
        by(auto simp add: alpha_equiv_name_def flip_def)
    qed
  qed
qed


fun unpack_FunctionDefinition ::
  "Statement \<Rightarrow> (Identifier * Identifier list * Identifier list * Statement list) option" where
"unpack_FunctionDefinition (FunctionDefinition name params rets body) = Some (name, params, rets, body)"
| "unpack_FunctionDefinition _ = None"

lemma unpack_FunctionDefinition_case :
  "(case st of
    FunctionDefinition name params rets body \<Rightarrow> f1 name params rets body
    | _ \<Rightarrow> f2) =
   (case unpack_FunctionDefinition st of
    Some (name, params, rets, body) \<Rightarrow> f1 name params rets body
    | None \<Rightarrow> f2)"
  by(cases st; auto)

lemma list_all2_equiv_name_function_contexts :
  assumes "alpha_equiv_name fsubst f1 f2"
  assumes "alpha_equiv_function_contexts fsubst fc1 fc2"
  assumes "map_of fc1 f1 = Some x1"
  assumes "map_of fc2 f2 = Some x2"
  assumes "list_all2 P fc1 fc2"
  shows "P (f1, x1) (f2, x2)"
  using assms
proof(induction fc1 arbitrary: fsubst fc2 f1 f2 x1 x2)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons fc1h fc1t)

  then obtain fc2h fc2t where Cons2 :
    "fc2 = fc2h # fc2t"
    by(cases fc2; auto)

  obtain fc1k fc1v where Fc1h : "fc1h = (fc1k, fc1v)"
    by(cases fc1h; auto)

  obtain fc2k fc2v where Fc2h : "fc2h = (fc2k, fc2v)"
    by(cases fc2h; auto)

  obtain fsubsth fsubstt where Cons_f :
    "fsubst = fsubsth # fsubstt"
    using Cons1.prems
    by(cases fsubst; auto simp add: alpha_equiv_function_contexts_def)

  show ?case
  proof(cases "f1 = fc1k")
    case Eq1 : True

    then have Eq2 : "f2 = fc2k"
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def split: option.splits)

    then show ?thesis
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def split: option.splits)
  next
    case Neq1 : False

    then have Neq2 : "f2 \<noteq> fc2k"
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def split: option.splits)

    have Contexts_tl : "alpha_equiv_function_contexts fsubstt fc1t fc2t"
      using Cons1.prems Cons2 Cons_f Fc1h Fc2h Neq1 Neq2
      by(auto simp add: alpha_equiv_function_contexts_def alpha_equiv_function_context_elem_def)

    have Name' : "alpha_equiv_name fsubstt f1 f2"
      using Neq1 Neq2 Cons1.prems Cons2 Fc1h Fc2h Cons_f
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def
          split: option.splits)

    show ?thesis
      using Cons1.prems Cons2 Fc1h Fc2h Neq1 Neq2
      using Cons1.IH[OF Name' Contexts_tl]
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def split: option.splits)
  qed
qed

lemma list_all2_equiv_name_local_variables :
  assumes "alpha_equiv_name subst f1 f2"
  assumes "alpha_equiv_local_variables subst fc1 fc2"
  assumes "map_of fc1 f1 = Some x1"
  assumes "map_of fc2 f2 = Some x2"
  assumes "list_all2 P fc1 fc2"
  shows "P (f1, x1) (f2, x2)"
  using assms
proof(induction fc1 arbitrary: subst fc2 f1 f2 x1 x2)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons fc1h fc1t)

  then obtain fc2h fc2t where Cons2 :
    "fc2 = fc2h # fc2t"
    by(cases fc2; auto)

  obtain fc1k fc1v where Fc1h : "fc1h = (fc1k, fc1v)"
    by(cases fc1h; auto)

  obtain fc2k fc2v where Fc2h : "fc2h = (fc2k, fc2v)"
    by(cases fc2h; auto)

  obtain substh substt where Cons_f :
    "subst = substh # substt"
    using Cons1.prems
    by(cases subst; auto simp add: alpha_equiv_local_variables_def)

  show ?case
  proof(cases "f1 = fc1k")
    case Eq1 : True

    then have Eq2 : "f2 = fc2k"
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def flip_def split: option.splits)

    then show ?thesis
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def flip_def split: option.splits)
  next
    case Neq1 : False

    then have Neq2 : "f2 \<noteq> fc2k"
      using Cons1.prems Cons2 Fc1h Fc2h
      by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def flip_def split: option.splits)

    have Contexts_tl : "alpha_equiv_local_variables substt fc1t fc2t"
      using Cons1.prems Cons2 Cons_f Fc1h Fc2h Neq1 Neq2
      by(auto simp add: alpha_equiv_local_variables_def alpha_equiv_function_context_elem_def)

    have Name' : "alpha_equiv_name substt f1 f2"
      using Neq1 Neq2 Cons1.prems Cons2 Fc1h Fc2h Cons_f
      by(auto simp add: alpha_equiv_name_def alpha_equiv_local_variables_def flip_def
          split: option.splits)

    show ?thesis
      using Cons1.prems Cons2 Fc1h Fc2h Neq1 Neq2
      using Cons1.IH[OF Name' Contexts_tl]
      by(auto simp add: alpha_equiv_name_def alpha_equiv_function_contexts_def flip_def split: option.splits)
  qed
qed

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
       alpha_equiv_statement fsubst vsubst st1 st2 \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
       run_state (evalStatement n m st1) c1 = (m1, c1') \<Longrightarrow>
       run_state (evalStatement n m st2) c2 = (m2, c2') \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> m1 = m2"
    using Suc.IH
    by fast

  have IH1_traverse_mode :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) l1 l2 m m1 m2 c1' c2'.
       list_all2 (alpha_equiv_statement fsubst vsubst) l1 l2 \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
       run_state (traverse_list_mode (evalStatement n m) l1) c1 = (m1, c1') \<Longrightarrow>
       run_state (traverse_list_mode (evalStatement n m) l2) c2 = (m2, c2') \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> m1 = m2"
  proof-
    fix fsubst vsubst
    fix c1 c2 :: "'g yulcontext"
    fix l1 l2 m m1 m2 c1' c2'

    show "list_all2 (alpha_equiv_statement fsubst vsubst) l1 l2 \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
       run_state (traverse_list_mode (evalStatement n m) l1) c1 = (m1, c1') \<Longrightarrow>
       run_state (traverse_list_mode (evalStatement n m) l2) c2 = (m2, c2') \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> m1 = m2"
    proof(induction l1 arbitrary: fsubst vsubst c1 c2 l2 m m1 m2 c1' c2')
      case Nil1 : Nil
      then show ?case by auto
    next
      case Cons1 : (Cons l1h l1t)

      obtain l2h l2t where Cons2 : "l2 = l2h # l2t"
        using Cons1.prems
        by(cases l2; auto)

      obtain c1h m1h where Run1 : "run_state (evalStatement n m l1h) c1 = (m1h, c1h)"
        by force

      obtain c2h m2h where Run2 : "run_state (evalStatement n m l2h) c2 = (m2h, c2h)"
        by force

      have Result : "alpha_equiv_yulcontext fsubst vsubst c1h c2h" "m1h = m2h"
        using IH1[OF _ _ Run1 Run2, of fsubst vsubst] Cons1.prems Cons2
        by(auto)

      obtain c1t m1t where Run1t : "run_state (traverse_list_mode (evalStatement n m1h) l1t) c1h = (m1t, c1t)"
        by force

      obtain c2t m2t where Run2t : "run_state (traverse_list_mode (evalStatement n m1h) l2t) c2h = (m2t, c2t)"
        by force

      show ?case
      proof(cases "m1h = RegularMode")
        case True
        then show ?thesis 
          using Cons1.prems Cons2 Run1 Run2 Cons1.IH[OF _ Result(1) Run1t Run2t] Result Run1t Run2t
          by(cases m; auto)
      next
        case False
        then show ?thesis
          using Cons1.prems Cons2 Run1 Run2 Result Run1t Run2t
          by(cases m; auto)
      qed
    qed
  qed

  have IH2 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) e1 e2 c1' c2' vals1 vals2.
      alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
      alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
      run_state (evalExpression n e1) c1 = (vals1, c1') \<Longrightarrow>
      run_state (evalExpression n e2) c2 = (vals2, c2') \<Longrightarrow>
      alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> vals1 = vals2"
    using Suc.IH
    by fast

  (* IH2_traverse is probably not needed. *)

  have IH3 :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) e1 e2 c1' c2' v1 v2.
    alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
    run_state (evalUnaryExpression n e1) c1 = (v1, c1') \<Longrightarrow>
    run_state (evalUnaryExpression n e2) c2 = (v2, c2') \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> v1 = v2"
    using Suc.IH
    by fast

  have IH3_traverse :
    "\<And> fsubst vsubst (c1 :: 'g yulcontext) (c2 :: 'g yulcontext) l1 l2 c1' c2' v1 v2 .
    list_all2 (alpha_equiv_expr fsubst vsubst) l1 l2 \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
    run_state (traverse_list (evalUnaryExpression n) l1) c1 = (v1, c1') \<Longrightarrow>
    run_state (traverse_list (evalUnaryExpression n) l2) c2 = (v2, c2') \<Longrightarrow>
    alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> v1 = v2"
  proof-
    fix fsubst vsubst
    fix c1 c2 :: "'g yulcontext"
    fix l1 l2 c1' c2' v1 v2
    show "list_all2 (alpha_equiv_expr fsubst vsubst) l1 l2 \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1 c2 \<Longrightarrow>
       run_state (traverse_list (evalUnaryExpression n) l1) c1 =
       (v1, c1') \<Longrightarrow>
       run_state (traverse_list (evalUnaryExpression n) l2) c2 =
       (v2, c2') \<Longrightarrow>
       alpha_equiv_yulcontext fsubst vsubst c1' c2' \<and> v1 = v2"
    proof(induction l1 arbitrary: fsubst vsubst c1 c2 l2 c1' c2' v1 v2)
      case Nil1 : Nil
      then show ?case 
        by(auto)
    next
      case Cons1 : (Cons l1h l1t)

      obtain l2h l2t where Cons2 : "l2 = l2h # l2t"
        using Cons1.prems
        by(cases l2; auto)

      obtain c1h v1h where Run1 : "run_state (evalUnaryExpression n l1h) c1 = (v1h, c1h)"
        by force

      obtain c2h v2h where Run2 : "run_state (evalUnaryExpression n l2h) c2 = (v2h, c2h)"
        by force

      have Result : "alpha_equiv_yulcontext fsubst vsubst c1h c2h" "v1h = v2h"
        using IH3[OF _ _ Run1 Run2, of fsubst vsubst] Cons1.prems Cons2
        by(auto)

      obtain c1t v1t where Run1t : "run_state (traverse_list (evalUnaryExpression n) l1t) c1h = (v1t, c1t)"
        by force

      obtain c2t v2t where Run2t : "run_state (traverse_list (evalUnaryExpression n) l2t) c2h = (v2t, c2t)"
        by force

      show ?case 
        using Cons1.prems Cons2 Run1 Run2 Cons1.IH[OF _ Result(1) Run1t Run2t] Result(2) Run1t Run2t
        by(auto)
    qed
  qed

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
      case Fc1 : (FunctionCall f1 args1)

      then obtain f2 args2 where Fc2 : "e2 = FunctionCall f2 args2"
        using Hexpr
        by(cases e2; auto)

      have Fname : "alpha_equiv_name fsubst f1 f2"
        using Fc1 Fc2 Hexpr
        by auto

      hence Fname_In : "(f1, f2) \<in> set fsubst"
        using alpha_equiv_name_In
        by auto

      obtain argvals1 argsc1 where Args1 :
        "run_state (traverse_list (evalUnaryExpression n) (rev args1)) c1 = (argvals1, argsc1)"
        by force

      obtain argvals2 argsc2 where Args2 :
        "run_state (traverse_list (evalUnaryExpression n) (rev args2)) c2 = (argvals2, argsc2)"
        by force

      have Equiv_after_args :
        "alpha_equiv_yulcontext fsubst vsubst argsc1 argsc2" "argvals1 = argvals2"
        using IH3_traverse[OF _ _ Args1 Args2, of fsubst vsubst] Hexpr Hctx Fc1 Fc2
        by(auto)

      obtain bivals1_o biresc1 where Builtin1 : "run_state (BuiltinFunctionOfIdentifier f1) argsc1 = (bivals1_o, biresc1)"
        by force

      obtain bivals2_o biresc2 where Builtin2 : "run_state (BuiltinFunctionOfIdentifier f2) argsc2 = (bivals2_o, biresc2)"
        by force

      have Biresc_eq_argsc : "biresc1 = argsc1" "biresc2 = argsc2"
        using Builtin1 Builtin2
        by(auto simp add: BuiltinFunctionOfIdentifier_def split: option.splits)

      have Equiv_after_get_builtin : "alpha_equiv_yulcontext fsubst vsubst biresc1 biresc2"
        using Equiv_after_args Builtin1 Builtin2
        by(auto simp add: BuiltinFunctionOfIdentifier_def split: option.splits)

(* we should probably show biresc1 and biresc2 are also equal. *)

      show ?thesis
      proof(cases bivals1_o)
        case Isnt_builtin1 : None

        have Isnt_builtin1' : "BuiltinFunctions argsc1 f1 = None"
          using Hexpr Hctx Hrun1 Hrun2 Fc1 Fc2 Args1 Args2 Builtin1 Builtin2 Isnt_builtin1
          by(cases "BuiltinFunctions argsc1 f1"; auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def)

        have Argsc_builtins : "list_all (\<lambda>(n1, n2). BuiltinFunctions argsc1 n1 = BuiltinFunctions argsc2 n2) fsubst"
          using Equiv_after_args
          by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_builtin_contexts_def)

        have Isnt_builtin2' : "BuiltinFunctions argsc2 f2 = None"
          using Argsc_builtins Fname_In Isnt_builtin1'
          unfolding list_all_iff
          by(auto)

        have Isnt_builtin2 : "bivals2_o = None"
          using Hexpr Hctx Hrun1 Hrun2 Fc1 Fc2 Args1 Args2 Builtin1 Builtin2 Isnt_builtin1 Isnt_builtin1' Isnt_builtin2'
          by(cases bivals2_o; auto simp add: BuiltinFunctionOfIdentifier_def)

        obtain fundef1 fundefsc1 where Fundef1 : "run_state (FunctionDefinitionOfIdentifier f1) biresc1 = (fundef1, fundefsc1)"
          by(cases "run_state (FunctionDefinitionOfIdentifier f1) biresc1"; auto)

        obtain fundef2 fundefsc2 where Fundef2 : "run_state (FunctionDefinitionOfIdentifier f2) biresc2 = (fundef2, fundefsc2)"
          by(cases "run_state (FunctionDefinitionOfIdentifier f2) biresc2"; auto)

        obtain fundef1_def fundef1_decls where Fundef1' :
          "fundef1 = (fundef1_def, fundef1_decls)"
          by force

        obtain fundef2_def fundef2_decls where Fundef2' :
          "fundef2 = (fundef2_def, fundef2_decls)"
          by force

        have F1_f2_in_functions : "(f1, f2) \<in> set (zip (map fst (Functions biresc1)) (map fst (Functions biresc2)))"
          using Equiv_after_get_builtin alpha_equiv_name_In[OF Fname]
          by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt unpack_FunctionDefinition_case errorState_def alpha_equiv_name_def)

        obtain f1body' where 
          "(f1, f1body') \<in> set (Functions biresc1)"
          using set_zip_leftD[OF F1_f2_in_functions]
          by fastforce

        then obtain f1body where F1body : "map_of (Functions biresc1) f1 = Some f1body"
          using weak_map_of_SomeI
          by fast

        obtain f2body' where 
          "(f2, f2body') \<in> set (Functions biresc2)"
          using set_zip_rightD[OF F1_f2_in_functions]
          by fastforce

        then obtain f2body where F2body : "map_of (Functions biresc2) f2 = Some f2body"
          using weak_map_of_SomeI
          by fast

        have Fundefsc_eq_biresc : "fundefsc1 = biresc1" "fundefsc2 = biresc2"
          using Fundef1 Fundef2 F1body F2body
          by( auto simp add: FunctionDefinitionOfIdentifier_def find_map_of_alt split: option.splits)

        have Equiv_after_fundef :
          "alpha_equiv_yulcontext fsubst vsubst fundefsc1 fundefsc2"
          using Fundef1 Fundef2 Equiv_after_get_builtin F1body F2body
          by(auto simp add: FunctionDefinitionOfIdentifier_def find_map_of_alt)

        have Elems_after_fundef : "list_all2 alpha_equiv_function_context_elem (Functions fundefsc1) (Functions fundefsc2)"
          using Equiv_after_fundef Fundef1 Fundef1' Fundef2 Fundef2' F1body F2body
          by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt unpack_FunctionDefinition_case errorState_def)

        have Elem_after_fundef : "alpha_equiv_function_context_elem (f1, f1body) (f2, f2body)"
          using Elems_after_fundef F1body F2body Equiv_after_fundef
          using list_all2_equiv_name_function_contexts[OF Fname _ _ _ Elems_after_fundef]
          unfolding Fundefsc_eq_biresc
          by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt unpack_FunctionDefinition_case errorState_def)

        have F1body_eq : "f1body = fundef1"
          using Elem_after_fundef Fundef1 Fundef1' Fundefsc_eq_biresc F1body
          by(auto simp add: FunctionDefinitionOfIdentifier_def find_map_of_alt)

        have F2body_eq : "f2body = fundef2"
          using Elem_after_fundef Fundef2 Fundef2' Fundefsc_eq_biresc F2body
          by(auto simp add: FunctionDefinitionOfIdentifier_def find_map_of_alt)

        (* next, check to see if we found a valid function *)
        show ?thesis
        proof(cases "unpack_FunctionDefinition fundef1_def")
          case Isnt_def1 : None

          have Isnt_def2 : "unpack_FunctionDefinition fundef2_def = None"
            using Elem_after_fundef F1body F2body Isnt_def1 Fundef1 Fundef2 Fundef1' Fundef2'
            unfolding Fundefsc_eq_biresc F1body_eq F2body_eq
            by(auto simp add: alpha_equiv_function_context_elem_def unpack_FunctionDefinition_case)

          then show ?thesis
            using Hexpr Hrun1 Hrun2 Fc1 Fc2 Args1 Args2 Builtin1 Builtin2 Isnt_builtin1' Isnt_builtin2'
            using Fundef1 Fundef1' Fundef2 Fundef2' Equiv_after_get_builtin F1body F2body Isnt_def1
            by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt unpack_FunctionDefinition_case errorState_def)
        next
          case Is_def1 : (Some fnd1)

          then obtain fname1 fargs1 frets1 fstms1 where Fnd1 :
            "fundef1_def = FunctionDefinition fname1 fargs1 frets1 fstms1"
            by(cases fundef1_def; auto)

          obtain fnd2 where Is_def2 : "unpack_FunctionDefinition fundef2_def = Some fnd2"
            using Elem_after_fundef F1body F2body Is_def1 Fundef1 Fundef2 Fundef1' Fundef2'
            unfolding Fundefsc_eq_biresc F1body_eq F2body_eq
            by(cases "unpack_FunctionDefinition fundef2_def"; auto simp add: alpha_equiv_function_context_elem_def unpack_FunctionDefinition_case)

          then obtain fname2 fargs2 frets2 fstms2 where Fnd2 :
            "fundef2_def = FunctionDefinition fname2 fargs2 frets2 fstms2"
            by(cases fundef2_def; auto)

          have Eq_arg_vals_length :
            "length args1 = length args2"
            using Fc1 Fc2 Hexpr
            by(auto elim:list_all2_lengthD)

          have Eq_fargs_length :
            "length fargs1 = length fargs2"
            using Elem_after_fundef F1body_eq F2body_eq F1body F2body Fnd1 Fnd2
            using Fundefsc_eq_biresc Fundef1' Fundef2'
            by(cases "length fargs1 = length fargs2"; auto simp add: alpha_equiv_function_context_elem_def)

          have Eq_frets_length :
            "length frets1 = length frets2"
            using Elem_after_fundef F1body_eq F2body_eq F1body F2body Fnd1 Fnd2
            using Fundefsc_eq_biresc Fundef1' Fundef2' Eq_fargs_length
            by(cases "length frets1 = length frets2"; auto simp add: alpha_equiv_function_context_elem_def)

          show ?thesis
          proof(cases "length fargs1 = length args1")
            case Neq_args_length1 : False

            have Neq_args_length2 : "length fargs2 \<noteq> length args2"
              using Neq_args_length1 Fnd1 Fnd2 Elem_after_fundef F1body_eq F2body_eq Fundef1' Fundef2'
              using Eq_arg_vals_length
              by(auto simp add: alpha_equiv_function_context_elem_def)

            show ?thesis 
              using Hexpr Hctx Hrun1 Hrun2 Fc1 Fc2 Args1 Args2 Builtin1 Builtin2 Isnt_builtin1' Isnt_builtin2'
              using Fundef1 Fundef2 Fundef1' Fundef2' F1body_eq F2body_eq Fnd1 Fnd2 F1body F2body
              using Neq_args_length1 Neq_args_length2 Fundefsc_eq_biresc
              using Equiv_after_fundef Eq_fargs_length Eq_frets_length
              by(auto simp add: alpha_equiv_yulcontext_def alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt errorState_def)
          next
            case Eq_args_length1 : True

            have Eq_args_length2 : "length fargs2 = length args2"
              using Eq_args_length1 Fnd1 Fnd2 Elem_after_fundef F1body_eq F2body_eq Fundef1' Fundef2'
              using Eq_arg_vals_length Eq_fargs_length
              by(auto simp add: alpha_equiv_function_context_elem_def)

            obtain bodymode1 bodysc1 where Run_body1 :
              "run_state (evalStatement n RegularMode (Block fstms1))
               (biresc1
                \<lparr>LocalVariables := zip fargs1 (rev argvals1) @ map (\<lambda>v. (v, 0)) frets1,
                   Functions :=
                   filter (\<lambda>(name, z). list_contains fundef1_decls name) (Functions biresc1)\<rparr>) =
               (bodymode1, bodysc1)"
              by force

            obtain bodymode2 bodysc2 where Run_body2 :
              "run_state (evalStatement n RegularMode (Block fstms2))
               (biresc2
                \<lparr>LocalVariables := zip fargs2 (rev argvals2) @ map (\<lambda>v. (v, 0)) frets2,
                   Functions :=
                   filter (\<lambda>(name, z). list_contains fundef2_decls name) (Functions biresc2)\<rparr>) =
               (bodymode2, bodysc2)"
              by force

(* next, show equality on final run_state. (IH1 not needed) *)


            show ?thesis
              using Hexpr Hctx Hrun1 Hrun2 Fc1 Fc2 Args1 Args2 Builtin1 Builtin2 Isnt_builtin1' Isnt_builtin2'
              using Fundef1 Fundef2 Fundef1' Fundef2' F1body_eq F2body_eq Fnd1 Fnd2 F1body F2body
              using Eq_args_length1 Eq_args_length2 Fundefsc_eq_biresc
              using Equiv_after_fundef Eq_fargs_length Eq_frets_length
              using Run_body1 Run_body2
              apply(auto simp add: alpha_equiv_function_contexts_def BuiltinFunctionOfIdentifier_def FunctionDefinitionOfIdentifier_def find_map_of_alt errorState_def)
              sorry
          qed
        qed

      next
        case Is_builtin1 : (Some bivals1)
        then show ?thesis sorry
      qed
    next
      case Id1 : (Identifier i1)

      then obtain i2 where Id2 : "e2 = Identifier i2"
        using Hexpr
        by(cases e2; auto)

      have Locals :
        "alpha_equiv_local_variables vsubst (LocalVariables c1) (LocalVariables c2)"
        using Hctx
        by(auto simp add: alpha_equiv_yulcontext_def)

      have Names :
        "alpha_equiv_name vsubst i1 i2"
        using Hexpr Id1 Id2
        by(auto)

      show ?thesis
      proof(cases "getLocalVariable c1 i1")
        case None1 : None

        (* need lemma relating getLocalVariable to alpha_equiv_local_variables *)
        then have None2 : "getLocalVariable c2 i2 = None"
          using alpha_equiv_getLocalVariable[OF Locals Names]
          by auto

        then show ?thesis
          using Hctx Hexpr Hrun1 Hrun2 Id1 Id2 None1
          by(auto simp add: errorState_def alpha_equiv_yulcontext_def ValueOfIdentifier_def)
      next
        case Some1 : (Some v1)

        then have Some2 : "getLocalVariable c2 i2 = Some v1"
          using alpha_equiv_getLocalVariable[OF Locals Names]
          by auto

        then show ?thesis
          using Hctx Hexpr Hrun1 Hrun2 Id1 Id2 Some1
          by(auto simp add: errorState_def alpha_equiv_yulcontext_def ValueOfIdentifier_def)
      qed
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

  show ?case
    using Conc1 Conc2 Conc3
    by fast

qed


end