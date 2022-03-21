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

(* we split into function and variable namespaces
 * since that is how the interpreter works *)
fun alpha_equiv_expr' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
  "alpha_equiv_expr' vsubst fsubst
    (YulLiteralExpression x1) (YulLiteralExpression x2) = (x1 = x2)"
| "alpha_equiv_expr' vsubst fsubst
    (YulIdentifier x1) (YulIdentifier x2) =
    (subst_lookup vsubst x1 = Some x2)"
(* TODO: we may need to either put a stronger predicate on subst,
 * or have these checks go "both ways" *)
| "alpha_equiv_expr' vsubst fsubst
    (YulFunctionCallExpression (YulFunctionCall fn1 args1))
    (YulFunctionCallExpression (YulFunctionCall fn2 args2)) =
    (subst_lookup fsubst fn1 = Some fn2 \<and>
    (list_all2 (alpha_equiv_expr' vsubst fsubst) args1 args2))"
| "alpha_equiv_expr' scopes _ _ _ = False"

definition alpha_equiv_name' :: "subst \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> bool" where
"alpha_equiv_name' scopes n1 n2 =
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
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list \<Rightarrow>
    ((YulIdentifier * YulIdentifier) list * (YulIdentifier * YulIdentifier) list) option"
  where
"alpha_equiv_check_decls body1 body2 =
  (let vdecls1 = get_var_decls body1 in
  (let fdecls1 = get_fun_decls body1 in
  (let vdecls2 = get_var_decls body2 in
  (let fdecls2 = get_fun_decls body2 in
  (if (length vdecls1 = length vdecls2 \<and> length fdecls1 = length fdecls2)
   then Some (zip vdecls1 vdecls2, zip fdecls1 fdecls2)
   else None)))))"
  

fun alpha_equiv_statement' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
  "alpha_equiv_statement' vsubst fsubst
    (YulFunctionCallStatement (YulFunctionCall fn1 args1)) stm2 =
    (case stm2 of
      (YulFunctionCallStatement (YulFunctionCall fn2 args2)) \<Rightarrow>
        (subst_lookup fsubst fn1 = Some fn2 \<and>
        (list_all2 (alpha_equiv_expr' vsubst fsubst) args1 args2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
    (YulAssignmentStatement (YulAssignment ns1 e1)) stm2 =
    (case stm2 of
      (YulAssignmentStatement (YulAssignment ns2 e2)) \<Rightarrow>
        (alpha_equiv_expr' vsubst fsubst e1 e2 \<and>
         those (map (subst_lookup vsubst) ns1) = Some ns2)
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
    (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1)) stm2 =
    (case stm2 of
      (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) \<Rightarrow>
        ((case (eo1, eo2) of
          (Some e1, Some e2) \<Rightarrow> alpha_equiv_expr' vsubst fsubst e1 e2
          | (None, None) \<Rightarrow> True
          | _ \<Rightarrow> False) \<and>
         (length ns1 = length ns2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  (YulFunctionDefinitionStatement
      (YulFunctionDefinition name1 args1 rets1 body1)) stm2 =
  (case stm2 of
    (YulFunctionDefinitionStatement
        (YulFunctionDefinition name2 args2 rets2 body2)) \<Rightarrow>
        (case alpha_equiv_check_decls body1 body2 of
          None \<Rightarrow> False
          | Some (vsubst', fsubst') \<Rightarrow>
            (length args1 = length args2 \<and>
             length rets1 = length rets2 \<and>
             (let newscope1 =
                ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args1) @
                 (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets1)) in
             (let newscope2 =
                ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args2) @
                 (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets2)) in
             (list_all2 (alpha_equiv_statement' 
              (((zip newscope1 newscope2) @ vsubst') # vsubst)
              (fsubst' # fsubst))
              body1 body2)))))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  (YulIf e1 body1) stm2 =
  (case stm2 of
    (YulIf e2 body2) \<Rightarrow>
      (alpha_equiv_expr' vsubst fsubst e1 e2 \<and>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (vsubst', fsubst') \<Rightarrow>
          list_all2 (alpha_equiv_statement' (vsubst' # vsubst) (fsubst' # fsubst)) body1 body2))
    | _ \<Rightarrow> False)"
  
| "alpha_equiv_statement' vsubst fsubst
  (YulSwitch e1 cases1) stm2 =
  (case stm2 of
    (YulSwitch e2 cases2) \<Rightarrow>
      (alpha_equiv_expr' vsubst fsubst e1 e2 \<and>
      (list_all2
        (\<lambda> c1 c2 .
          (case c1 of
            (YulSwitchCase l1 body1) \<Rightarrow>
          (case c2 of
            (YulSwitchCase l2 body2) \<Rightarrow>
            (l1 = l2 \<and>
            (case alpha_equiv_check_decls body1 body2 of
              None \<Rightarrow> False
              | Some (vsubst', fsubst') \<Rightarrow>
                list_all2 (alpha_equiv_statement' (vsubst' # vsubst) (fsubst' # fsubst)) body1 body2)))))
        cases1 cases2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  (YulForLoop pre1 cond1 post1 body1) stm2 =
  (case stm2 of
    (YulForLoop pre2 cond2 post2 body2) \<Rightarrow>
      (case alpha_equiv_check_decls pre1 pre2 of
        None \<Rightarrow> False
        | Some (vsubst'_pre, fsubst'_pre) \<Rightarrow> 
      (case alpha_equiv_check_decls post1 post2 of
        None \<Rightarrow> False
        | Some (vsubst'_post, fsubst'_post) \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (vsubst'_body, fsubst'_body) \<Rightarrow>
          (alpha_equiv_expr' (vsubst'_pre # vsubst) (fsubst'_pre # fsubst) cond1 cond2 \<and>
           list_all2 (alpha_equiv_statement' (vsubst'_pre # vsubst) (fsubst'_pre # fsubst)) pre1 pre2 \<and>
           list_all2 (alpha_equiv_statement' ((vsubst'_body @ vsubst'_pre) # vsubst)
                                             ((fsubst'_body @ fsubst'_pre) # fsubst)) body1 body2 \<and>
           list_all2 (alpha_equiv_statement' ((vsubst'_post @ vsubst'_pre) # vsubst)
                                             ((fsubst'_post @ fsubst'_pre) # fsubst)) post1 post2))))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  YulBreak stm2 =
  (case stm2 of
    YulBreak \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  YulContinue stm2 =
  (case stm2 of
    YulContinue \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  YulLeave stm2 =
  (case stm2 of
    YulLeave \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' vsubst fsubst
  (YulBlock body1) stm2 =
  (case stm2 of
    (YulBlock body2) \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (vsubst', fsubst') \<Rightarrow>
          list_all2 (alpha_equiv_statement' (vsubst' # vsubst) (fsubst' # fsubst)) body1 body2)
    | _ \<Rightarrow> False)"

term "undefined :: 'v locals"

definition alpha_equiv_local ::
  "subst \<Rightarrow> subst \<Rightarrow> (YulIdentifier * 'v) \<Rightarrow> (YulIdentifier * 'v) \<Rightarrow> bool" where
"alpha_equiv_local vsubst fsubst loc1 loc2 =
  (case loc1 of (n1, v1) \<Rightarrow>
  (case loc2 of (n2, v2) \<Rightarrow>
  (v1 = v2 \<and> subst_lookup vsubst n1 = Some n2)))"

definition alpha_equiv_locals' ::
  "subst \<Rightarrow> subst \<Rightarrow> (YulIdentifier * 'v) list \<Rightarrow> (YulIdentifier * 'v) list \<Rightarrow> bool" where
"alpha_equiv_locals' vsubst fsubst locs1 locs2 =
  list_all2 (alpha_equiv_local vsubst fsubst) locs1 locs2"

(*
definition alpha_equiv_locals' ::
  "subst \<Rightarrow> subst \<Rightarrow> 'v locals \<Rightarrow> 'v locals \<Rightarrow> bool" where
"alpha_equiv_locals' vsubst fsubst [] [] = True"
| "alpha_equiv_locals' vsubst fsubst ((n1, v1)#t1) ((n2, v2)#t2) =
   (v1 = v2 \<and>
    subst_lookup vsubst n1 = Some n2 \<and>
    alpha_equiv_locals' vsubst fsubst t1 t2)"
| "alpha_equiv_locals' _ _ _ _ = False"
*)

(* TODO: need equality of function parameters/returns here?
 * or just alpha equivalence?
 * i think alpha equivalence should suffice. but under what context?
 *)
(* builtins need to be exactly equal.
 * TODO: perhaps revisit
 * TODO: can we get away with something weaker than alpha_equiv_statement' here?
 *  *)
definition alpha_equiv_function_sig'_scheme ::
  "subst \<Rightarrow> subst \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> bool" where
"alpha_equiv_function_sig'_scheme vsubst fsubst n1 s1 n2 s2 =
  (case (f_sig_body s1, f_sig_body s2) of
        (YulBuiltin b1, YulBuiltin b2) \<Rightarrow> s1 = s2
        | (YulFunction sts1, YulFunction sts2) \<Rightarrow>
          alpha_equiv_statement' vsubst fsubst
              (YulFunctionDefinitionStatement (YulFunctionDefinition n1 (f_sig_arguments s1) (f_sig_returns s1) sts1))
              (YulFunctionDefinitionStatement (YulFunctionDefinition n2 (f_sig_arguments s2) (f_sig_returns s2) sts2))
        | (_, _) \<Rightarrow> False)"

(* alpha_equiv_function_sig. TODO: do we need to compare visible ids, or can we get away
 * with not doing so? *)
(*
definition alpha_equiv_function_sig' ::
  "subst \<Rightarrow> subst \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> bool" where
"alpha_equiv_function_sig' vsubst fsubst n1 s1 n2 s2 =
  (those (map (subst_lookup fsubst) (f_sig_visible s1)) = Some (f_sig_visible s2) \<and>
   alpha_equiv_function_sig'_scheme vsubst fsubst n1 s1 n2 s2)"
*)

(* fun alpha_equiv_function_bodies' ::
  "subst \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> bool" where
(* TODO: see if we need it *)
*)

definition alpha_equiv_fun ::
  "subst \<Rightarrow> subst \<Rightarrow> (YulIdentifier * ('g, 'v, 't) function_sig) \<Rightarrow> (YulIdentifier * ('g, 'v, 't) function_sig) \<Rightarrow> bool"
  where
"alpha_equiv_fun vsubst fsubst fun1 fun2 =
  (case fun1 of (n1, s1) \<Rightarrow>
  (case fun2 of (n2, s2) \<Rightarrow>
  (alpha_equiv_function_sig'_scheme vsubst fsubst n1 s1 n2 s2)))"

(* TODO: we aren't checking that types are compatible here. Perhaps this can be done
 * in a different pass *)
(*
fun alpha_equiv_funs' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> bool"
  where
"alpha_equiv_funs' vsubst fsubst [] [] = True"
| "alpha_equiv_funs' vsubst fsubst ((n1, s1)#t1) ((n2, s2)#t2) =
   (alpha_equiv_function_sig'_scheme vsubst fsubst n1 s1 n2 s2 \<and>
    alpha_equiv_funs' vsubst fsubst t1 t2)"
| "alpha_equiv_funs' _ _ _ _ = False"
*)

definition alpha_equiv_funs' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> ('g, 'v, 't) function_sig locals \<Rightarrow> bool"
  where
"alpha_equiv_funs' vsubst fsubst funs1 funs2 =
  list_all2 (alpha_equiv_fun vsubst fsubst) funs1 funs2"

(* TODO: make sure we are handling equivalence of function-contexts correctly.
 * this is a bit complicated to due to possibility of recursion/mutual recursion *)

fun alpha_equiv_stackEl' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> bool" where
"alpha_equiv_stackEl' vsubst fsubst (EnterStatement s1) (EnterStatement s2) =
  alpha_equiv_statement' vsubst fsubst s1 s2"
| "alpha_equiv_stackEl' vsubst fsubst (ExitStatement s1 vs1 fs1) (ExitStatement s2 vs2 fs2) =
    (alpha_equiv_statement' vsubst fsubst s1 s2 \<and>
     alpha_equiv_locals' vsubst fsubst vs1 vs2 \<and>
     alpha_equiv_funs' vsubst fsubst fs1 fs2)"
| "alpha_equiv_stackEl' vsubst fsubst (Expression e1) (Expression e2) =
  alpha_equiv_expr' vsubst fsubst e1 e2"
| "alpha_equiv_stackEl' vsubst fsubst (EnterFunctionCall n1 f1) (EnterFunctionCall n2 f2) = 
   (alpha_equiv_function_sig'_scheme vsubst fsubst n1 f1 n2 f2)"
| "alpha_equiv_stackEl' vsubst fsubst (ExitFunctionCall n1 vals1 locals1 fs1 f1)
                                      (ExitFunctionCall n2 vals2 locals2 fs2 f2) =
    (alpha_equiv_function_sig'_scheme vsubst fsubst n1 f1 n2 f2 \<and>
     alpha_equiv_locals' vsubst fsubst locals1 locals2 \<and>
     alpha_equiv_funs' vsubst fsubst fs1 fs2)"
| "alpha_equiv_stackEl' vsubst fsubst _ _ = False"

(* whenever we extend the variable context, we also need to update subst.  *)
(* also need to update subst on function entry. *)

(* gather yul functions / get_fun_decls *)

fun subst_update_enter_statement ::
  "subst \<Rightarrow> subst \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst * subst)" where
"subst_update_enter_statement vsubst fsubst (YulBlock ls1) (YulBlock ls2) =
  (vsubst, (zip (get_fun_decls ls1) (get_fun_decls ls2))# fsubst)"
| "subst_update_enter_statement vsubst fsubst _ _ = (vsubst, fsubst)"

(*
fun YulStatement_same_constr ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where

| "YulStatement_same_constr _ _ = False"
*)
fun subst_update_exit_statement ::
  "subst \<Rightarrow> subst \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst * subst) option" where
"subst_update_exit_statement vsubst fsubst
  (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1))
  (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) = 
  (case vsubst of
    sh # subst \<Rightarrow>
      Some ((((zip (strip_id_types ns1) (strip_id_types ns2)) @ sh) # subst), fsubst)
    | _ \<Rightarrow> None)"
| "subst_update_exit_statement vsubst fsubst
  (YulBlock ls1)
  (YulBlock ls2) = 
  (case (vsubst, fsubst) of
    (vsh # vsubst', fsh # fsubst') \<Rightarrow> Some (vsubst', fsubst')
   | _ \<Rightarrow> None)"
(* bogus cases mixed with noop cases here. *)
| "subst_update_exit_statement vsubst fsubst _ _ = Some (vsubst, fsubst)" 

fun subst_update_enter_fun_call ::
    "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> ('g, 'v, 't) function_sig \<Rightarrow> (subst * subst)"
    where
  "subst_update_enter_fun_call vsubst fsubst
    sig1 sig2 = 
    (case (f_sig_body sig1, f_sig_body sig2) of
      (YulFunction b1, YulFunction b2) \<Rightarrow>
        ((zip ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments sig1)) @
              (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns sig1)))
              ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_arguments sig2)) @
              (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) (f_sig_returns sig1)))) # vsubst
        , fsubst)
      | (_, _) \<Rightarrow> (vsubst, fsubst))
    "

fun subst_update_exit_fun_call ::
  "subst \<Rightarrow> subst \<Rightarrow> (subst * subst) option"
  where
"subst_update_exit_fun_call (vh#vsubst') (fsh # fsubst') = Some (vsubst', fsubst')"
| "subst_update_exit_fun_call vsubst fsubst = None"

(* TODO: return an option? *)
fun subst_update ::
  "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> (subst * subst) option" where
"subst_update vsubst fsubst (EnterStatement s1) (EnterStatement s2) =
  Some (subst_update_enter_statement vsubst fsubst s1 s2)"
| "subst_update vsubst fsubst (ExitStatement s1 _ _) (ExitStatement s2 _ _) =
  subst_update_exit_statement vsubst fsubst s1 s2"
| "subst_update vsubst fsubst (EnterFunctionCall f1 s1) (EnterFunctionCall f2 s2) =
  Some (subst_update_enter_fun_call vsubst fsubst s1 s2)"
| "subst_update vsubst fsubst (ExitFunctionCall _ _ _ _ _) (ExitFunctionCall _ _ _ _ _) = 
  subst_update_exit_fun_call vsubst fsubst"
| "subst_update vsubst fsubst _ _ = Some (vsubst, fsubst)"

definition alpha_equiv_results' ::
  "subst \<Rightarrow> subst \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   bool" where
"alpha_equiv_results' vsubst fsubst r1 r2 =
  (global r1 = global r2 \<and>
   vals r1 = vals r2 \<and>
   alpha_equiv_locals' vsubst fsubst (locals r1) (locals r2) \<and>
   alpha_equiv_funs' vsubst fsubst (funs r1) (funs r2) \<and>
   (list_all2 (alpha_equiv_stackEl' vsubst fsubst)
              (cont r1)
              (cont r2)))"

lemma alpha_equiv_locals'_length :
  assumes "alpha_equiv_locals' vsubst fsubst l1 l2"
  shows "length l1 = length l2"
  using assms
proof(induction l1 arbitrary: vsubst fsubst l2)
  case Nil
  then show ?case 
    by(cases l2; auto simp add: alpha_equiv_locals'_def)
next
  case (Cons l1h l1t)

  show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis using Cons
      by(auto simp add: alpha_equiv_locals'_def)
  next
    case Cons' : (Cons l2h l2t)
    then show ?thesis using Cons.prems Cons.IH[of vsubst fsubst l2t]
      by(cases l1h; cases l2h; auto simp add: alpha_equiv_locals'_def)
  qed
qed

lemma alpha_equiv_locals_v_insert1_unmentioned :
  assumes "alpha_equiv_locals' (vsubsth # vsubstt) fsubst l1 l2"
  assumes "map_of l1 n1 = None"
  assumes "map_of l2 n2 = None" 
  shows "alpha_equiv_locals' (((n1, n2) # vsubsth) # vsubstt) fsubst l1 l2"
  using assms
proof(induction l1 arbitrary: vsubsth vsubstt l2 n1 n2)
  case Nil
  then show ?case
    by(cases l2; auto simp add: alpha_equiv_locals'_def)
next
  case (Cons l1h l1t)

  obtain l2h l2t where Cons2 :
    "l2 = l2h # l2t"
    using Cons.prems
    by(cases l2; auto simp add: alpha_equiv_locals'_def)

  show ?case 
    using Cons.prems Cons.IH[of vsubsth vsubstt l2t n1 n2] Cons2
    by(cases l1h; cases l2h; auto simp add: alpha_equiv_locals'_def alpha_equiv_local_def split: option.splits if_splits)
qed

(* NB: induction not needed here. *)
lemma alpha_equiv_locals_v_insert1 :
  assumes H1 : "insert_value l1 n1 v = Some l1'"
  assumes H2 : "insert_value l2 n2 v = Some l2'"
  assumes "alpha_equiv_locals' (vsubsth # vsubstt) fsubst l1 l2"
  shows "alpha_equiv_locals' (((n1, n2)#vsubsth) # vsubstt) fsubst l1' l2'"
  using assms
proof(induction vsubstt arbitrary: vsubsth n1 n2 v l1 l2 l1' l2')
  case Nil
  then show ?case using alpha_equiv_locals_v_insert1_unmentioned[of vsubsth "[]" fsubst l1 l2]
    by(auto simp add: alpha_equiv_locals'_def alpha_equiv_local_def split: option.splits)
next
  case (Cons vsubsth' vsubstt')
  show ?case using Cons.prems
    alpha_equiv_locals_v_insert1_unmentioned[of vsubsth "vsubsth' # vsubstt'" fsubst l1 l2 n1 n2]
    using Cons.prems
    by(auto simp add: alpha_equiv_locals'_def alpha_equiv_local_def split: option.splits)
qed


lemma alpha_equiv_locals_v_insert :
  assumes H1 : "insert_values l1 ns1 vs = Some l1'"
  assumes H2 : "insert_values l2 ns2 vs = Some l2'"
  assumes "alpha_equiv_locals' (vsubsth # vsubstt) fsubst l1 l2"
  shows "alpha_equiv_locals' ((zip ns1 ns2 @ vsubsth) # vsubstt) fsubst l1' l2'"
  using assms
proof(induction vs arbitrary: vsubsth vsubstt ns1 ns2 l1 l2 l1' l2')
  case Nil

  have Nil1 : "ns1 = []"
    using Nil
    by(cases ns1; auto)

  have Nil2 : "ns2 = []"
    using Nil
    by(cases ns2; auto)

  show ?case using Nil Nil1 Nil2
    by(auto)
next
  case (Cons vh vt)

  obtain n1h n1t where Cons1 : "ns1 = n1h#n1t"
    using Cons
    by(cases ns1; auto)

  obtain n2h n2t where Cons2 : "ns2 = n2h#n2t"
    using Cons
    by(cases ns2; auto)

  obtain l1't where L1't : "insert_values l1 n1t vt = Some l1't" "insert_value l1't n1h vh = Some l1'"
    using Cons1 Cons.prems
    by(auto split: option.split_asm)

  obtain l2't where L2't : "insert_values l2 n2t vt = Some l2't" "insert_value l2't n2h vh = Some l2'"
    using Cons2 Cons.prems
    by(auto split: option.split_asm)

  have Conc' : "alpha_equiv_locals' ((zip n1t n2t @ vsubsth) # vsubstt) fsubst l1't l2't"
    using Cons1 Cons2 Cons.IH[OF L1't(1) L2't(1) Cons.prems(3)]
    by(auto)

  show ?case
    using alpha_equiv_locals_v_insert1[OF L1't(2) L2't(2) Conc'] Cons1 Cons2
    by(auto)
qed

(* TODO: do we need an additional assumption that locals and funs
 * don't have name collisions?
 *)
(*
lemma alpha_equiv_function_sig'_insert1_unmentioned :
  assumes "alpha_equiv_function_sig' (substh # substt) l1 l2"
  assumes "map_of l1 n1 = None"
  assumes "map_of l2 n2 = None" 
  shows "alpha_equiv_function_sig' (((n1, n2) # substh) # substt) l1 l2"
  using assms
proof(induction l1 arbitrary: substh substt l2 n1 n2)
  case Nil
  then show ?case
    by(cases l2; auto)
next
  case (Cons l1h l1t)

  obtain l2h l2t where Cons2 :
    "l2 = l2h # l2t"
    using Cons.prems
    by(cases l2; auto)

  show ?case 
    using Cons.prems Cons.IH[of substh substt l2t n1 n2] Cons2
    apply(cases l1h; cases l2h; auto split: if_splits)
    apply( simp add: alpha_equiv_function_sig'_def split: option.splits if_splits)
qed
*)

(* make sure builtins are mentioned in subst? *)
(* problem: need to recurse into functions in order to see if
 * there is a name collision... *)
lemma alpha_equiv_funs_f_insert1_unmentioned :
  assumes "alpha_equiv_funs' vsubst (fsubsth # fsubstt) l1 l2"
  assumes "map_of l1 n1 = None"
  assumes "map_of l2 n2 = None" 
  shows "alpha_equiv_funs' vsubst (((n1, n2) # fsubsth) # fsubstt) l1 l2"
  using assms
proof(induction l1 arbitrary: vsubst fsubsth fsubstt l2 n1 n2)
  case Nil
  then show ?case
    by(cases l2; auto simp add: alpha_equiv_funs'_def)
next
  case (Cons l1h l1t)

  obtain l2h l2t where Cons2 :
    "l2 = l2h # l2t"
    using Cons.prems
    by(cases l2; auto simp add: alpha_equiv_funs'_def)

  show ?case 
    using Cons.prems Cons.IH[of vsubst fsubsth fsubstt l2t n1 n2] Cons2
    unfolding alpha_equiv_funs'_def alpha_equiv_fun_def
    apply(cases l1h; cases l2h; auto split: if_splits)
    apply(auto simp add:  alpha_equiv_function_sig'_scheme_def
          alpha_equiv_name'_def split: option.splits if_splits YulFunctionBody.splits)
qed


lemma alpha_equiv_funs_f_insert1 :
  assumes H1 : "insert_value l1 n1 v = Some l1'"
  assumes H2 : "insert_value l2 n2 v = Some l2'"
  assumes "alpha_equiv_funs' (substh # substt) l1 l2"
  shows "alpha_equiv_funs' (((n1, n2)#substh) # substt) l1' l2'"
  using assms
proof(induction substt arbitrary: substh n1 n2 v l1 l2 l1' l2')
  case Nil
  then show ?case using alpha_equiv_locals_insert1_unmentioned[of substh "[]" l1 l2]
    by(auto split: option.splits)
next
  case (Cons substh' substt')
  show ?case using Cons.prems
    alpha_equiv_locals_insert1_unmentioned[of substh "substh' # substt'" l1 l2 n1 n2]
    using Cons.prems
    by(auto split: option.splits)
qed


lemma alpha_equiv_funs_insert :
  assumes H1 : "insert_values l1 ns1 vs = Some l1'"
  assumes H2 : "insert_values l2 ns2 vs = Some l2'"
  assumes "alpha_equiv_funs' (substh # substt) l1 l2"
  shows "alpha_equiv_funs' ((zip ns1 ns2 @ substh) # substt) l1' l2'"
  using assms
proof(induction vs arbitrary: substh substt ns1 ns2 l1 l2 l1' l2')
  case Nil

  have Nil1 : "ns1 = []"
    using Nil
    by(cases ns1; auto)

  have Nil2 : "ns2 = []"
    using Nil
    by(cases ns2; auto)

  show ?case using Nil Nil1 Nil2
    by(auto)
next
  case (Cons vh vt)

  obtain n1h n1t where Cons1 : "ns1 = n1h#n1t"
    using Cons
    by(cases ns1; auto)

  obtain n2h n2t where Cons2 : "ns2 = n2h#n2t"
    using Cons
    by(cases ns2; auto)

  obtain l1't where L1't : "insert_values l1 n1t vt = Some l1't" "insert_value l1't n1h vh = Some l1'"
    using Cons1 Cons.prems
    by(auto split: option.split_asm)

  obtain l2't where L2't : "insert_values l2 n2t vt = Some l2't" "insert_value l2't n2h vh = Some l2'"
    using Cons2 Cons.prems
    by(auto split: option.split_asm)

  have Conc' : "alpha_equiv_funs' ((zip n1t n2t @ substh) # substt) l1't l2't"
    using Cons1 Cons2 Cons.IH[OF L1't(1) L2't(1) Cons.prems(3)]
    by(auto)

  show ?case
    using alpha_equiv_insert1[OF L1't(2) L2't(2) Conc'] Cons1 Cons2
    by(auto)
qed

(* need a lemma about alpha_equiv_stackEl'
 * and consing onto the front of the vars/funs lists.
 *)

lemma alpha_equiv_step :
  assumes Hc1 : "cont r1 = (c1h#c1t)"
  assumes Hc2 : "cont r2 = (c2h#c2t)"
  assumes Hinit : "alpha_equiv_results' vsubst fsubst r1 r2"
  assumes H1 : "evalYulStep d r1 = YulResult r1'"
  assumes H2 : "evalYulStep d r2 = YulResult r2'"
  assumes Hupd : "subst_update vsubst fsubst c1h c2h = Some (vsubst', fsubst')"
  shows "alpha_equiv_results' vsubst' fsubst' r1' r2'"
  using assms
proof(cases c1h)
  case ES1 : (EnterStatement x1)

  then obtain x2 where ES2 : "c2h = EnterStatement x2"
    using Hc1 Hc2 Hinit
    by(cases c2h; auto simp add: alpha_equiv_results'_def)

  show ?thesis
  proof(cases x1)
    case F1: (YulFunctionCallStatement f1)

    then obtain n1 args1 where 
      FC1 : "f1 = YulFunctionCall n1 args1"
      by(cases f1; auto)

    obtain f2 where F2 :
      "x2 = YulFunctionCallStatement f2"
      using ES1 ES2 F1 FC1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain n2 args2 where
      FC2 : "f2 = YulFunctionCall n2 args2"
      by(cases f2; auto)

    show ?thesis 
      using ES1 F1 FC1 ES2 F2 FC2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next

    case A1 : (YulAssignmentStatement a1)

    then obtain vs1 e1 where
      AS1 : "a1 = YulAssignment vs1 e1"
      by(cases a1; auto)

    obtain a2 where A2 :
      "x2 = YulAssignmentStatement a2"
      using ES1 ES2 A1 AS1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain vs2 e2 where
      AS2 : "a2 = YulAssignment vs2 e2"
      by(cases a2; auto)

    show ?thesis
      using ES1 A1 AS1 ES2 A2 AS2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case D1 : (YulVariableDeclarationStatement d1)

    then obtain vs1 eo1 where
      VD1 : "d1 = YulVariableDeclaration vs1 eo1"
      by(cases d1; auto)

    obtain d2 where
      D2 : "x2 = YulVariableDeclarationStatement d2"
      using ES1 ES2 D1 VD1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain vs2 eo2 where
      VD2 : "d2 = YulVariableDeclaration vs2 eo2"
      by(cases d2; auto)

    show ?thesis
      using ES1 D1 VD1 ES2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(cases eo1; cases eo2; auto simp add: alpha_equiv_results'_def)
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
  case XS1 : (ExitStatement x1 locs1 funs1)

  then obtain x2 locs2 funs2 where XS2 : "c2h = ExitStatement x2 locs2 funs2"
    using Hc1 Hc2 Hinit
    by(cases c2h; auto simp add: alpha_equiv_results'_def)

  show ?thesis
  proof(cases x1)
    case F1 : (YulFunctionCallStatement f1)

    then obtain n1 args1 where 
      FC1 : "f1 = YulFunctionCall n1 args1"
      by(cases f1; auto)

    obtain f2 where F2 :
      "x2 = YulFunctionCallStatement f2"
      using XS1 XS2 F1 FC1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain n2 args2 where
      FC2 : "f2 = YulFunctionCall n2 args2"
      by(cases f2; auto)

    show ?thesis 
      using XS1 F1 FC1 XS2 F2 FC2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(cases "vals r2"; auto simp add: alpha_equiv_results'_def)

  next
    case (YulAssignmentStatement x2)
    then show ?thesis sorry
  next
    case D1 : (YulVariableDeclarationStatement d1)

    then obtain vs1 eo1 where
      VD1 : "d1 = YulVariableDeclaration vs1 eo1"
      by(cases d1; auto)

    obtain d2 where
      D2 : "x2 = YulVariableDeclarationStatement d2"
      using XS1 XS2 D1 VD1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain vs2 eo2 where
      VD2 : "d2 = YulVariableDeclaration vs2 eo2"
      by(cases d2; auto)

    show ?thesis
    proof(cases eo1)
      case None1 : None

      then have None2 : "eo2 = None"
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd
        by(cases eo2; auto simp add: alpha_equiv_results'_def)

      have Vemp : "vals r1 = []" 
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd None1 None2
        by(cases "vals r2"; auto simp add: alpha_equiv_results'_def)

      obtain substh substt where Subst_cons :
        "vsubst = substh#substt"
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd None1 None2 Vemp
        by(cases vsubst; auto simp add: alpha_equiv_results'_def)

      obtain L1 where L1v :
        "insert_values (locals r1) (map strip_id_type vs1) (replicate (length vs1) (default_val d)) = Some L1"
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd None1 None2 Vemp Subst_cons
        by(auto simp add: alpha_equiv_results'_def split: option.split_asm)

      obtain L2 where L2v :
        "insert_values (locals r2) (map strip_id_type vs2) (replicate (length vs2) (default_val d)) = Some L2"
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd None1 None2 Vemp Subst_cons
        by(auto simp add: alpha_equiv_results'_def split: option.split_asm)

      have Vlens : "length vs1 = length vs2"
        using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 
        by(auto simp add: alpha_equiv_results'_def)

      show ?thesis using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd None1 None2 Vemp Subst_cons
          L1v L2v
          alpha_equiv_locals_v_insert[OF L1v[unfolded Vlens] L2v, of substh substt fsubst']
        apply(auto simp add: alpha_equiv_results'_def)
          defer

    next
      case (Some a)
      then show ?thesis sorry
    qed


      using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd
      apply(cases eo1; cases eo2; auto simp add: alpha_equiv_results'_def)
(* again, we need a lemma relating updates to alpha-equivalence *)
  next

    case (YulVariableDeclarationStatement x3)
    then show ?thesis sorry
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

  then show ?thesis sorry
next
  case (EnterFunctionCall x31 x32)
  then show ?thesis sorry
next
  case (ExitFunctionCall x41 x42 x43 x44 x45)
  then show ?thesis sorry
next
  case (Expression x5)
  then show ?thesis sorry
qed


end