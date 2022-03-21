theory Renamer_DeBruijn_Ext_Correct
  imports Renamer_DeBruijn_Ext "../Yul/YulSemanticsSingleStep"

begin

type_synonym subst =
  "(YulIdentifier * YulIdentifier) list list"

type_synonym subst' = "(YulIdentifier * YulIdentifier) list"

definition subst_get1 :: "subst \<Rightarrow> YulIdentifier list list" where
"subst_get1 s =
  map (map fst) s"

definition subst_get2 :: "subst \<Rightarrow> YulIdentifier list list" where
"subst_get2 s =
  map (map snd) s"

definition subst_flip :: "subst \<Rightarrow> subst" where
"subst_flip s =
  map (map (\<lambda> p . case p of (x, y) \<Rightarrow> (y, x))) s"

(* alpha equivalence modulo a set of scopes 
 * s1 and s2 probably need different scopes here *)
definition alpha_equiv_statement' ::
  "subst \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
"alpha_equiv_statement' scopes s1 s2 =
  (yul_statement_to_deBruijn (subst_get1 scopes) s1 =
   yul_statement_to_deBruijn (subst_get2 scopes) s2)"

definition alpha_equiv_expr' ::
  "subst \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
"alpha_equiv_expr' scopes s1 s2 =
  (yul_expr_to_deBruijn (subst_get1 scopes) s1 =
  yul_expr_to_deBruijn (subst_get2 scopes) s2)"

(*
 * 
 *)

definition alpha_equiv_statement ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
"alpha_equiv_statement s1 s2 =
  alpha_equiv_statement' [] s1 s2"

definition alpha_equiv_expr ::
  "('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
"alpha_equiv_expr s1 s2 =
  alpha_equiv_expr' [] s1 s2"

fun subst1 :: "subst \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier option" where
"subst1 [] _ = None"
| "subst1 (h#t) v =
   (case map_of h v of
    None \<Rightarrow> subst1 t v
    | Some v' \<Rightarrow> Some v')"

fun subst_list :: "subst \<Rightarrow> YulIdentifier list \<Rightarrow> YulIdentifier list option" where
"subst_list _ [] = Some []"
| "subst_list s (vh#vt) =
   (case subst1 s vh of
    None \<Rightarrow> None
    | Some vh' \<Rightarrow>
      (case subst_list s vt of
       None \<Rightarrow> None
       | Some vt' \<Rightarrow> Some (vh'#vt')))"

(* for function bodies that are builtins, we need to be able to
 * rename parameters. might want to find a way to share code for doing this
 *)

fun rename_locals :: "subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals option" where
"rename_locals _ [] = Some []"
| "rename_locals s ((n, v)#t) =
   (case subst1 s n of
    None \<Rightarrow> None
    | Some n' \<Rightarrow>
    (case rename_locals s t of
      None \<Rightarrow> None
      | Some t' \<Rightarrow> (Some ((n', v)#t'))))"

(* NB: this may be too strong a notion for other uses, as it
 * depends on the ordering of values in the locals. However for
 * our purposes it should be fine since the states will be exactly the same
 * even in terms of structure, apart from names.
 *)
(*
fun alpha_equiv_locals' ::
  "subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals \<Rightarrow> bool" where
"alpha_equiv_locals' subst [] [] = True"
| "alpha_equiv_locals' subst ((n1, v1)#t1) ((n2, v2)#t2) =
   (subst1 subst n1 = Some n2 \<and>
    v1 = v2 \<and>
    alpha_equiv_locals' subst t1 t2)"
| "alpha_equiv_locals' _ _ _ = False"
*)

(* Enforce that names match for names mentioned in subst.
 * This way, we can avoid name clashes for names not mentioned in subst (e.g. variables bound
 * further down the syntax tree)
 *)
fun alpha_equiv_locals' ::
  "subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals \<Rightarrow> bool" where
"alpha_equiv_locals' subst [] [] = True"
| "alpha_equiv_locals' subst ((n1, v1)#t1) ((n2, v2)#t2) =
   (v1 = v2 \<and>
    subst1 subst n1 = Some n2 \<and>
    alpha_equiv_locals' subst t1 t2)"
| "alpha_equiv_locals' _ _ _ = False"

definition alpha_equiv_function_sig'_scheme ::
  "subst \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> bool" where
"alpha_equiv_function_sig'_scheme subst n1 s1 n2 s2 =
  (subst1 subst n1 = Some n2 \<and>
  (case (f_sig_body s1, f_sig_body s2) of
        (YulBuiltin b1, YulBuiltin b2) \<Rightarrow>
          (let args1 = (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments s1)) in
          (let args2 = (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments s2)) in
          (let rets1 = (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns s1)) in
          (let rets2 = (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns s2)) in
            ((subst_list subst args1 = Some args2) \<and> (subst_list subst rets1 = Some rets2))))))
        | (YulFunction sts1, YulFunction sts2) \<Rightarrow>
            alpha_equiv_statement' subst 
              (YulFunctionDefinitionStatement (YulFunctionDefinition n1 (f_sig_arguments s1) (f_sig_returns s1) sts1))
              (YulFunctionDefinitionStatement (YulFunctionDefinition n2 (f_sig_arguments s2) (f_sig_returns s2) sts2))
        | (_, _) \<Rightarrow> False))"

(* alpha_equiv_function_sig - compare visible ids *)
definition alpha_equiv_function_sig' ::
  "subst \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> bool" where
"alpha_equiv_function_sig' subst n1 s1 n2 s2 =
  (subst_list subst (f_sig_visible s1) = Some (f_sig_visible s2) \<and>
   alpha_equiv_function_sig'_scheme subst n1 s1 n2 s2)"

(*
fun alpha_equiv_function_bodies' ::
  "subst \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> bool" where
"alpha_equiv_function_bodies subst (YulBuiltin f1) (YulBuiltin f2) = (f1 = f2)"
| "alpha_equiv_function_bodies subst (YulFunction sts1) (YulFunction sts2) =
    alpha_equiv_statement' subst
      (YulFunctionDefinitionStatement (YulFunctionDefinition n1 (f_sig_arguments s1) (f_sig_returns s1) (f_sig_body s1)))
      (YulFunctionDefinitionStatement (YulFunctionDefinition n2 (f_sig_arguments s2) (f_sig_returns s2) (f_sig_body s2)))"
*)

(* TODO: we aren't checking that types are compatible here. Perhaps this can be done
 * in a different pass *)
fun alpha_equiv_funs' ::
  "subst \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> bool"
  where
"alpha_equiv_funs' subst [] [] = True"
| "alpha_equiv_funs' subst ((n1, s1)#t1) ((n2, s2)#t2) =
   (alpha_equiv_function_sig' subst n1 s1 n2 s2 \<and>
    alpha_equiv_funs' subst t1 t2)"
| "alpha_equiv_funs' _ _ _ = False"

(* TODO: make sure we are handling equivalence of function-contexts correctly.
 * this is a bit complicated to due to possibility of recursion/mutual recursion *)

fun alpha_equiv_stackEl' ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> bool" where
"alpha_equiv_stackEl' subst (EnterStatement s1) (EnterStatement s2) =
  alpha_equiv_statement' subst s1 s2"
| "alpha_equiv_stackEl' subst (ExitStatement s1 vs1 fs1) (ExitStatement s2 vs2 fs2) =
    (alpha_equiv_statement' subst s1 s2 \<and>
     alpha_equiv_locals' subst vs1 vs2 \<and>
     alpha_equiv_funs' subst fs1 fs2)"
| "alpha_equiv_stackEl' subst (Expression e1) (Expression e2) =
  alpha_equiv_expr' subst e1 e2"
| "alpha_equiv_stackEl' subst (EnterFunctionCall n1 f1) (EnterFunctionCall n2 f2) = 
   (alpha_equiv_function_sig' subst n1 f1 n2 f2)"
| "alpha_equiv_stackEl' subst (ExitFunctionCall n1 vals1 locals1 fs1 f1)
                              (ExitFunctionCall n2 vals2 locals2 fs2 f2) =
    (alpha_equiv_function_sig' subst n1 f1 n2 f2 \<and>
     alpha_equiv_locals' subst locals1 locals2 \<and>
     alpha_equiv_funs' subst fs1 fs2)"
| "alpha_equiv_stackEl' subst _ _ = False"

(* whenever we extend the variable context, we also need to update subst.  *)
(* also need to update subst on function entry. *)

(* gather yul functions / get_fun_decls *)

fun subst_update_enter_statement ::
  "subst \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   subst" where
"subst_update_enter_statement subst (YulBlock ls1) (YulBlock ls2) =
  (zip (get_fun_decls ls1) (get_fun_decls ls2))# subst"
| "subst_update_enter_statement subst _ _ = subst"

(*
fun YulStatement_same_constr ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where

| "YulStatement_same_constr _ _ = False"
*)
fun subst_update_exit_statement ::
  "subst \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   subst option" where
"subst_update_exit_statement subst
  (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1))
  (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) = 
  (case subst of
    sh # subst \<Rightarrow> Some ((sh @ (zip (strip_id_types ns1) (strip_id_types ns2))) # subst)
    | _ \<Rightarrow> None)"
| "subst_update_exit_statement subst
  (YulBlock ls1)
  (YulBlock ls2) = 
  (case subst of
    sh # subst \<Rightarrow> Some subst
   | _ \<Rightarrow> None)"
| "subst_update_exit_statement subst _ _ = Some subst" (* bogus cases mixed with noop cases here. *)

(* TODO: figure out if we need to change
   yul_statement_to_deBruijn to separate the function define/return scope
   from the scope of the function local variables (declared inside a block)

   maybe this doesn't matter though. the subst we generate will
   still be valid, even if it isn't the one generated by
   the renamer?
 *)
fun subst_update_enter_fun_call ::
    "subst \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> subst"
    where
  "subst_update_enter_fun_call subst 
    sig1 sig2 = 
    (case (f_sig_body sig1, f_sig_body sig2) of
      (YulFunction b1, YulFunction b2) \<Rightarrow>
        (zip ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments sig1)) @
             (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns sig1)))
             ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments sig2)) @
             (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns sig1)))) # subst
      | (_, _) \<Rightarrow> subst)
    "

fun subst_update_exit_fun_call ::
  "subst \<Rightarrow> subst option"
  where
"subst_update_exit_fun_call (sh#subst) = Some subst"
| "subst_update_exit_fun_call subst = None"

(* TODO: return an option? *)
fun subst_update ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> subst option" where
"subst_update subst (EnterStatement s1) (EnterStatement s2) =
  Some (subst_update_enter_statement subst s1 s2)"
| "subst_update subst (ExitStatement s1 _ _) (ExitStatement s2 _ _) =
  subst_update_exit_statement subst s1 s2"
| "subst_update subst (EnterFunctionCall f1 s1) (EnterFunctionCall f2 s2) =
  Some (subst_update_enter_fun_call subst s1 s2)"
| "subst_update subst (ExitFunctionCall _ _ _ _ _) (ExitFunctionCall _ _ _ _ _) = 
  subst_update_exit_fun_call subst"
| "subst_update subst _ _ = Some subst"


(* Alternate approach: use existing locals and funs to update subst.
 *)

(*
  idea. if we see variables not in subst, add them as a prefix
  in corresponding order.
  if we see variables in the subst that are not in the locals,
  remove the scope they were declared in (should be outermost)
  Hmm... but, if we have an empty scope it will mess this up.
*)

(*
fun subst_update_result ::
  "subst \<Rightarrow>
   ('x) locals \<Rightarrow>
   ('x) locals \<Rightarrow>
   subst option" where
"subst_update_result [] l1 l2 =
  Some [zip (map fst l1) (map fst l2)]"
| "subst_update_result (sh#st) l1 l2 =
*)

(*
  2 cases:
    - subst has more values, remove values until we are ok
    - subst has fewer values, construct a prefix
*)


(* YulSemanticsSingleStep.result *)

definition alpha_equiv_results' ::
  "subst \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   bool" where
"alpha_equiv_results' subst r1 r2 =
  (global r1 = global r2 \<and>
   vals r1 = vals r2 \<and>
   alpha_equiv_locals' subst (locals r1) (locals r2) \<and>
   alpha_equiv_funs' subst (funs r1) (funs r2) \<and>
   (list_all2 (alpha_equiv_stackEl' subst)
              (cont r1)
              (cont r2)))"

(* Idea: if both programs take a step, then
 * the results are the same (up to alpha equivalence of states)
 * This also means we need to be able to account for alpha-equivalent input
 * states, in order to make this work.
 *)

lemma alpha_equiv_step :
  assumes Hc1 : "cont r1 = (c1h#c1t)"
  assumes Hc2 : "cont r2 = (c2h#c2t)"
  assumes Hinit : "alpha_equiv_results' subst r1 r2"
  assumes H1 : "evalYulStep d r1 = YulResult r1'"
  assumes H2 : "evalYulStep d r2 = YulResult r2'"
  assumes Hupd : "subst_update subst c1h c2h = Some subst'"
  shows "alpha_equiv_results' subst' r1' r2'"
  using assms
proof(cases c1h)
  case EnterStatement1 : (EnterStatement st1)

  obtain st2 where EnterStatement2 :
    "c2h = EnterStatement st2"
    using Hc1 Hc2 EnterStatement1 Hc1 Hinit
    by(cases c2h; auto simp add: alpha_equiv_results'_def)

  show ?thesis
  proof(cases st1)
    case X1: (YulFunctionCallStatement x1)

    obtain f1 args1 where F1 : "x1 = YulFunctionCall f1 args1"
      by(cases x1; auto)

    obtain x2 where X2 :
      "st2 = YulFunctionCallStatement x2"
      (* yul_statement_to_deBruijn fact *)
      sorry

    obtain f2 args2 where F2 : "x2 = YulFunctionCall f2 args2"
      by(cases x2; auto)

    show ?thesis
      using assms Hc1 Hc2 EnterStatement1 EnterStatement2 X1 X2 F1 F2
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_statement'_def alpha_equiv_expr'_def
          split: option.splits)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis sorry
    next
      case X1 : (YulVariableDeclarationStatement x1)
      obtain n1 vs1 where V1 : "x1 = YulVariableDeclaration n1 vs1"
        by(cases x1; auto)
  
      obtain x2 where X2 : "st2 = YulVariableDeclarationStatement x2"
        sorry
  
      obtain n2 vs2 where V2 : "x2 = YulVariableDeclaration n2 vs2"
        by(cases x2; auto)
  
      show ?thesis using assms Hc1 Hc2 EnterStatement1 EnterStatement2 X1 X2 V1 V2
        by(fastforce simp add: alpha_equiv_results'_def alpha_equiv_statement'_def alpha_equiv_expr'_def Let_def
            split: option.splits)
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis sorry
    next
      case (YulIf x51 x52)
      then show ?thesis sorry
    next
      case (YulSwitch x61 x62)
      then show ?thesis sorry
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis sorry
    next
      case YulBreak
      then show ?thesis sorry
    next
      case YulContinue
      then show ?thesis sorry
    next
      case YulLeave
      then show ?thesis sorry
    next
      case (YulBlock x11)
      then show ?thesis sorry
    qed
  next
    case ExitStatement1: (ExitStatement esa1 esb1 esc1)
    
    obtain esa2 esb2 esc2 where ExitStatement2 :
      "c2h = ExitStatement esa2 esb2 esc2"
      using Hc1 Hc2 ExitStatement1 Hc1 Hinit
      by(cases c2h; auto simp add: alpha_equiv_results'_def)
  
    show ?thesis
    proof(cases esa1)
      case X1: (YulFunctionCallStatement x1)
  
      obtain f1 args1 where F1 : "x1 = YulFunctionCall f1 args1"
        by(cases x1; auto)
  
      obtain x2 where X2 :
        "esa2 = YulFunctionCallStatement x2"
        sorry
  
      obtain f2 args2 where F2 : "x2 = YulFunctionCall f2 args2"
        by(cases x2; auto)
  
      show ?thesis
        using assms Hc1 Hc2 ExitStatement1 ExitStatement2 X1 X2 F1 F2
        by(fastforce simp add: alpha_equiv_results'_def alpha_equiv_statement'_def alpha_equiv_expr'_def
            split: option.splits list.splits )
    next
      case (YulAssignmentStatement x2)
      then show ?thesis sorry
    next
      case X1: (YulVariableDeclarationStatement x3)
  
      obtain n1 vs1 where V1 : "x3 = YulVariableDeclaration n1 vs1"
        by(cases x3; auto)
  
      obtain x2 where X2 : "esa2 = YulVariableDeclarationStatement x2"
        sorry
  
      obtain n2 vs2 where V2 : "x2 = YulVariableDeclaration n2 vs2"
        by(cases x2; auto)

      show ?thesis
      proof(cases vs1)
        case None

        then have None' : "vs2 = None"
          sorry

(* empty subst should be ruled out. probably return an option instead *)
        show ?thesis using assms Hc1 Hc2 ExitStatement1 ExitStatement2 Hinit X1 X2 V1 V2 None None'
          apply(cases subst; auto simp add: alpha_equiv_expr'_def alpha_equiv_statement'_def alpha_equiv_results'_def  split: option.split_asm if_splits)
(* lemma about insert_values and alpha_equiv_locals
 * adding (non-conflicting) variable names to a scope won't change alpha equivalence*)
(* first two cases: need to show that length of args lists is the same
   (for Some, need to show values are the same - shouldn't be too hard *)

          sorry

      next
        case (Some a)

        then obtain a' where Some' : "vs2 = Some a'"
          sorry

        show ?thesis using assms Hc1 Hc2 Hinit ExitStatement1 ExitStatement2 X1 X2 V1 V2 Some Some'
          apply(cases subst; auto simp add: alpha_equiv_expr'_def alpha_equiv_statement'_def alpha_equiv_results'_def  split: option.split_asm if_splits)
          sorry
(*
        then show ?thesis sorry
*)
  (*
            apply(fastforce split: option.splits)
           apply(fastforce split: option.splits)
          apply(fastforce split: option.splits)
         apply(fastforce split: option.splits)
  *)
      qed
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis
        
        sorry
    next
      case (YulIf x51 x52)
      then show ?thesis sorry
    next
      case (YulSwitch x61 x62)
      then show ?thesis sorry
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis sorry
    next
      case YulBreak
      then show ?thesis sorry
    next
    case YulContinue
      then show ?thesis sorry
    next
      case YulLeave
      then show ?thesis sorry
    next
      case (YulBlock x11)
    then show ?thesis sorry
    qed
  
  next
    case EnterFunctionCall1: (EnterFunctionCall n1 sig1)

    obtain n2 sig2 where EnterFunctionCall2 :
      "c2h = EnterFunctionCall n2 sig2"
      using Hc1 Hc2 EnterFunctionCall1 Hc1 Hinit
      by(cases c2h; auto simp add: alpha_equiv_results'_def)
  
    show ?thesis using assms Hc1 Hc2 Hinit EnterFunctionCall1 EnterFunctionCall2
      apply(auto simp add: alpha_equiv_expr'_def alpha_equiv_statement'_def alpha_equiv_results'_def  split: option.split_asm if_splits YulFunctionBody.splits Result.splits)


    then show ?thesis sorry
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis sorry
  next
    case (Expression x5)
    then show ?thesis sorry
  qed
    using Hinit
    apply(simp add: alpha_equiv_results'_def)
  qed
(*
proof(induction c1 arbitrary: r1 r2 r1' r2')
  case Nil
  then show ?case
    by(auto simp add: alpha_equiv_results'_def)
next
  case (Cons c1h c1t)
  then show ?case sorry
qed
*)

(* we also need to be able to update substitutions. 
 * this will happen when entering a new context,
 * or declaring a new variable
 * we might be able to do an approach similar to the
 * renamer, where we gather definitions first
 * whenever encountering a new block*)

(*

fun update_subst ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('v, 'g, 't) StackEl \<Rightarrow> subst option"
where
"update_subst subst _ _ 
| "update_subst subst x y =
  (if (x = y) then Some subst else None)"
  

*)

(*
 * TODO: will scopes change during the execution of
 * a step?
 *)
(*
lemma alpha_equiv_correct_step_noerr :
  assumes H: "alpha_equiv_results' scopes s1 s2"
  assumes H1: "evalYulStep d s1 = Result s1'"
  shows "\<exists> s2' . evalYulStep d s2 = Result s2' \<and>
           alpha_equiv_results' scopes s1' s2'"

proof

*)
end