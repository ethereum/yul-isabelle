theory Renamer_DeBruijn_Ext_Correct
  imports Renamer_DeBruijn "../Yul/YulSemanticsSingleStep"

begin

(* alpha equivalence modulo a set of scopes *)
definition alpha_equiv_statement' ::
  "YulIdentifier list list \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
"alpha_equiv_statement' scopes s1 s2 =
  (yul_statement_to_deBruijn scopes s1 = yul_statement_to_deBruijn scopes s2)"

definition alpha_equiv_expr' ::
  "YulIdentifier list list \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
"alpha_equiv_expr' scopes s1 s2 =
  (yul_expr_to_deBruijn scopes s1 = yul_expr_to_deBruijn scopes s2)"

(*
 * 
 *)

(* Idea: if both programs take a step, then
 * the results are the same (up to alpha equivalence of states)
 * This also means we need to be able to account for alpha-equivalent input
 * states, in order to make this work.
 *)
(*
lemma alpha_equiv_correct_full :
  
*)
end