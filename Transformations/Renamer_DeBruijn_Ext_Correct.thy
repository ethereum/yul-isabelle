theory Renamer_DeBruijn_Ext_Correct
  imports Renamer_DeBruijn "../Yul/YulSemanticsSingleStep"

begin

type_synonym subst =
  "(YulIdentifier * YulIdentifier) list list"

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
fun alpha_equiv_locals' ::
  "subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals \<Rightarrow> bool" where
"alpha_equiv_locals' subst [] [] = True"
| "alpha_equiv_locals' subst ((n1, v1)#t1) ((n2, v2)#t2) =
   (subst1 subst n1 = Some n2 \<and>
    v1 = v2 \<and>
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

(* YOU ARE HERE *)
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


(* YulSemanticsSingleStep.result *)

definition alpha_equiv_results' ::
  "subst \<Rightarrow>
   ('g, 'v, 't) YulSemanticsSingleStep.result \<Rightarrow>
   ('g, 'v, 't) YulSemanticsSingleStep.result \<Rightarrow>
   bool" where
"alpha_equiv_results' subst r1 r2 =
  (global r1 = global r2 \<and>
   vals r1 = vals r2 \<and>
   alpha_equiv_locals' subst (locals r1) (locals r2) \<and>
   alpha_equiv_locals' subst (funs r1) (funs r2) \<and>
   (list_all2 (alpha_equiv_stackEl' subst)
              (cont r1)
              (cont r2)))"

(* Idea: if both programs take a step, then
 * the results are the same (up to alpha equivalence of states)
 * This also means we need to be able to account for alpha-equivalent input
 * states, in order to make this work.
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