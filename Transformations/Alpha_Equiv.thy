theory Alpha_Equiv
  imports "../Yul/YulSyntax" "../Yul/YulSemanticsSingleStep"

begin

(* definition of alpha_equiv that does not rely on de Bruijn.
 * based on Renamer_DeBruijn_Ext_Correct, but hopefully simpler to reason on *)
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

definition subst'_flip :: "subst' \<Rightarrow> subst'" where
"subst'_flip s =
  map (\<lambda> p . case p of (x, y) \<Rightarrow> (y, x)) s"

fun subst_lookup :: "subst \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier option" where
"subst_lookup [] x = None"
| "subst_lookup (hl#t) x =
  (case map_of hl x of
    Some y \<Rightarrow> Some y
    | None \<Rightarrow> subst_lookup t x)"

fun get_var_decls' ::
  "('v, 't) YulStatement list \<Rightarrow> nat \<Rightarrow>
   (YulIdentifier list * nat)" where
"get_var_decls' [] i = ([], i)"
| "get_var_decls' ((YulVariableDeclarationStatement (YulVariableDeclaration decls v))#t) i =
   (case get_var_decls' t (i + length decls) of
    (l', i') \<Rightarrow>
    ((map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls) @ l', i'))"
| "get_var_decls' (h#t) i = get_var_decls' t i"

definition get_var_decls ::
  "('v, 't) YulStatement list \<Rightarrow> YulIdentifier list" where
"get_var_decls l =
  (case get_var_decls' l 0 of
    (l', _) \<Rightarrow> l')"

fun get_fun_decls' ::
"('v, 't) YulStatement list \<Rightarrow> nat \<Rightarrow>
 (YulIdentifier list * nat)" where
"get_fun_decls' [] i = ([], i)"
| "get_fun_decls' ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t) i =
   (case get_fun_decls' t (i + 1) of
     (l', i') \<Rightarrow> 
     (name # l'
     , i'))"
| "get_fun_decls' (h#t) i = 
    get_fun_decls' t i"

definition get_fun_decls ::
"('v, 't) YulStatement list \<Rightarrow>
 (YulIdentifier list)" where
"get_fun_decls l =
  (case get_fun_decls' l 0 of
    (l', _) \<Rightarrow> l')"


fun alpha_equiv_expr' ::
  "subst \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
  "alpha_equiv_expr' scopes
    (YulLiteralExpression x1) (YulLiteralExpression x2) = (x1 = x2)"
| "alpha_equiv_expr' scopes
    (YulIdentifier x1) (YulIdentifier x2) =
    (subst_lookup scopes x1 = Some x2)"
(* TODO: we may need to either put a stronger predicate on subst,
 * or have these checks go "both ways" *)
| "alpha_equiv_expr' scopes
    (YulFunctionCallExpression (YulFunctionCall fn1 args1))
    (YulFunctionCallExpression (YulFunctionCall fn2 args2)) =
    (subst_lookup scopes fn1 = Some fn2 \<and>
    (list_all2 (alpha_equiv_expr' scopes) args1 args2))"
| "alpha_equiv_expr' scopes _ _ = False"

definition alpha_equiv_name :: "subst \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> bool" where
"alpha_equiv_name scopes n1 n2 =
  (subst_lookup scopes n1 = Some n2)"

definition alpha_equiv_typed_name' ::
  "subst \<Rightarrow> ('t) YulTypedName \<Rightarrow> ('t) YulTypedName \<Rightarrow> bool" where
"alpha_equiv_typed_name' subst tn1 tn2 =
  (case tn1 of
    (YulTypedName n1 t1) \<Rightarrow>
    (case subst_lookup subst n1 of
      None \<Rightarrow> False
      | Some n2 \<Rightarrow> tn2 = YulTypedName n2 t1))"

definition alpha_equiv_check_decls ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list \<Rightarrow> (YulIdentifier * YulIdentifier) list option"
  where
"alpha_equiv_check_decls body1 body2 =
  (let vdecls1 = get_var_decls body1 in
  (let fdecls1 = get_fun_decls body1 in
  (let vdecls2 = get_var_decls body2 in
  (let fdecls2 = get_fun_decls body2 in
  (if (length vdecls1 = length vdecls2 \<and> length fdecls1 = length fdecls2)
   then Some (zip (vdecls1 @ fdecls1) (vdecls2 @ fdecls2))
   else None)))))"
  

fun alpha_equiv_statement' ::
  "subst \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
  "alpha_equiv_statement' scopes
    (YulFunctionCallStatement (YulFunctionCall fn1 args1)) stm2 =
    (case stm2 of
      (YulFunctionCallStatement (YulFunctionCall fn2 args2)) \<Rightarrow>
        (subst_lookup scopes fn1 = Some fn2 \<and>
        (list_all2 (alpha_equiv_expr' scopes) args1 args2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
    (YulAssignmentStatement (YulAssignment ns1 e1)) stm2 =
    (case stm2 of
      (YulAssignmentStatement (YulAssignment ns2 e2)) \<Rightarrow>
        (alpha_equiv_expr' scopes e1 e2 \<and>
         those (map (subst_lookup scopes) ns1) = Some ns2)
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
    (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1)) stm2 =
    (case stm2 of
      (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) \<Rightarrow>
        ((case (eo1, eo2) of
          (Some e1, Some e2) \<Rightarrow> alpha_equiv_expr' scopes e1 e2
          | (None, None) \<Rightarrow> True
          | _ \<Rightarrow> False) \<and>
         (length ns1 = length ns2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  (YulFunctionDefinitionStatement
      (YulFunctionDefinition name1 args1 rets1 body1)) stm2 =
  (case stm2 of
    (YulFunctionDefinitionStatement
        (YulFunctionDefinition name2 args2 rets2 body2)) \<Rightarrow>
        (case alpha_equiv_check_decls body1 body2 of
          None \<Rightarrow> False
          | Some scopes' \<Rightarrow>
            (length args1 = length args2 \<and>
             length rets1 = length rets2 \<and>
             (let newscope1 =
                ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args1) @
                 (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets1)) in
             (let newscope2 =
                ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args2) @
                 (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets2)) in
             (list_all2 (alpha_equiv_statement' (((zip newscope1 newscope2) @ scopes') # scopes))
              body1 body2)))))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  (YulIf e1 body1) stm2 =
  (case stm2 of
    (YulIf e2 body2) \<Rightarrow>
      (alpha_equiv_expr' scopes e1 e2 \<and>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some scopes' \<Rightarrow>
          list_all2 (alpha_equiv_statement' (scopes' # scopes)) body1 body2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  (YulSwitch e1 cases1) stm2 =
  (case stm2 of
    (YulSwitch e2 cases2) \<Rightarrow>
      (alpha_equiv_expr' scopes e1 e2 \<and>
      (list_all2
        (\<lambda> c1 c2 .
          (case c1 of
            (YulSwitchCase l1 body1) \<Rightarrow>
          (case c2 of
            (YulSwitchCase l2 body2) \<Rightarrow>
            (l1 = l2 \<and>
            (case alpha_equiv_check_decls body1 body2 of
              None \<Rightarrow> False
              | Some scopes' \<Rightarrow>
                list_all2 (alpha_equiv_statement' (scopes' # scopes)) body1 body2)))))
        cases1 cases2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  (YulForLoop pre1 cond1 post1 body1) stm2 =
  (case stm2 of
    (YulForLoop pre2 cond2 post2 body2) \<Rightarrow>
      (case alpha_equiv_check_decls pre1 pre2 of
        None \<Rightarrow> False
        | Some scopes'_pre \<Rightarrow> 
      (case alpha_equiv_check_decls post1 post2 of
        None \<Rightarrow> False
        | Some scopes'_post \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some scopes'_body \<Rightarrow>
          (alpha_equiv_expr' (scopes'_pre # scopes) cond1 cond2 \<and>
           list_all2 (alpha_equiv_statement' (scopes'_pre # scopes)) pre1 pre2 \<and>
           list_all2 (alpha_equiv_statement' ((scopes'_pre @ scopes'_body) # scopes)) body1 body2 \<and>
           list_all2 (alpha_equiv_statement' ((scopes'_pre @ scopes'_post) # scopes)) post1 post2))))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  YulBreak stm2 =
  (case stm2 of
    YulBreak \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  YulContinue stm2 =
  (case stm2 of
    YulContinue \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  YulLeave stm2 =
  (case stm2 of
    YulLeave \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' scopes
  (YulBlock body1) stm2 =
  (case stm2 of
    (YulBlock body2) \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some scopes' \<Rightarrow> list_all2 (alpha_equiv_statement' (scopes' # scopes)) body1 body2)
    | _ \<Rightarrow> False)"

fun alpha_equiv_locals' ::
  "subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals \<Rightarrow> bool" where
"alpha_equiv_locals' subst [] [] = True"
| "alpha_equiv_locals' subst ((n1, v1)#t1) ((n2, v2)#t2) =
   (v1 = v2 \<and>
    subst_lookup subst n1 = Some n2 \<and>
    alpha_equiv_locals' subst t1 t2)"
| "alpha_equiv_locals' _ _ _ = False"

(* Not yet finished - remaining primitives from Renamer_DeBruijn_Ext_Correct *)

(*
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
*)

end