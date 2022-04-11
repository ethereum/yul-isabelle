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

(*
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
*)

fun get_var_decls ::
  "('v, 't) YulStatement list \<Rightarrow>
   (YulIdentifier list)" where
"get_var_decls [] = []"
| "get_var_decls ((YulVariableDeclarationStatement (YulVariableDeclaration decls v))#t) =
   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls) @ (get_var_decls t)"
| "get_var_decls (h#t) = get_var_decls t"

(*
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
*)


fun get_fun_decls ::
"('v, 't) YulStatement list \<Rightarrow>
 (YulIdentifier list)" where
"get_fun_decls [] = []"
| "get_fun_decls ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t) =
   name # get_fun_decls t"
| "get_fun_decls (h#t) = 
    get_fun_decls t"

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

(*
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
*)

fun yul_statement_same_constructor ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
"yul_statement_same_constructor
  (YulFunctionCallStatement _) y =
  (case y of (YulFunctionCallStatement _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulAssignmentStatement _) y = 
  (case y of (YulAssignmentStatement _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulVariableDeclarationStatement _) y =
  (case y of (YulVariableDeclarationStatement _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulFunctionDefinitionStatement _) y =
  (case y of (YulFunctionDefinitionStatement _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulIf _ _) y =
  (case y of (YulIf _ _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulSwitch _ _)  y =
  (case y of (YulSwitch _ _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulForLoop _ _ _ _) y =
  (case y of (YulForLoop _ _ _ _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  YulBreak y =
  (case y of YulBreak \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  YulContinue y =
  (case y of YulContinue \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  YulLeave y = 
  (case y of YulLeave \<Rightarrow> True
   | _ \<Rightarrow> False)"
| "yul_statement_same_constructor
  (YulBlock _) y = 
  (case y of (YulBlock _) \<Rightarrow> True
   | _ \<Rightarrow> False)"
  

(* stronger version of check_decls
 * should we also check the other statements are the same? probably better to do a different one
 * *)
fun alpha_equiv_check_decls ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list \<Rightarrow>
    ((YulIdentifier * YulIdentifier) list * (YulIdentifier * YulIdentifier) list) option"
  where
"alpha_equiv_check_decls
  ((YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1))#t1)
  ((YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2))#t2) =
  (case alpha_equiv_check_decls t1 t2 of
     None \<Rightarrow> None
     | Some (vds, fds) \<Rightarrow>
     (if length decls1 = length decls2
      then Some 
           ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                 (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vds
           , fds)
      else None))"
| "alpha_equiv_check_decls
  ((YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1))#t1)
  ((YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2))#t2) = 
  (case alpha_equiv_check_decls t1 t2 of
     None \<Rightarrow> None
     | Some (vds, fds) \<Rightarrow>
     Some (vds, (name1, name2)#fds))"
| "alpha_equiv_check_decls (h1#t1) (h2#t2) = 
    (if yul_statement_same_constructor h1 h2
     then alpha_equiv_check_decls t1 t2
     else None)"
| "alpha_equiv_check_decls _ _ = None"

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
              ([((zip newscope1 newscope2) @ vsubst')])
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

(* add to function_sig'_scheme? :
  list_all2 (alpha_equiv_name vsubst fsubst) visible1 visible2
and/or
  do restriction on functions context?
*)

(* fun alpha_equiv_function_bodies' ::
  "subst \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> ('g, 'v, 't) YulFunctionBody \<Rightarrow> bool" where
(* TODO: see if we need it *)
*)

definition alpha_equiv_fun ::
  "subst \<Rightarrow> subst \<Rightarrow> (YulIdentifier * ('g, 'v, 't, 'z) function_sig'_scheme) \<Rightarrow> (YulIdentifier * ('g, 'v, 't, 'z) function_sig'_scheme) \<Rightarrow> bool"
  where
"alpha_equiv_fun vsubst fsubst fun1 fun2 =
  (case fun1 of (n1, s1) \<Rightarrow>
  (case fun2 of (n2, s2) \<Rightarrow>
  (alpha_equiv_function_sig'_scheme vsubst fsubst n1 s1 n2 s2)))"

definition alpha_equiv_funs' ::
  "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme locals \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme locals \<Rightarrow> bool"
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
    "subst \<Rightarrow> subst \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> (subst * subst)"
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

lemma alpha_equiv_locals_f_change :
  assumes "alpha_equiv_locals' vsubst fsubst l1 l2"
  shows "alpha_equiv_locals' vsubst fsubst' l1 l2"
  using assms
  unfolding alpha_equiv_locals'_def alpha_equiv_local_def
  by(auto)

lemma alpha_equiv_fun_trunc :
  assumes H: "alpha_equiv_fun vsubst fsubst fun1 fun2"
  shows "alpha_equiv_fun vsubst fsubst
     ((\<lambda>(n, fs). (n, function_sig'.truncate fs)) fun1)
     ((\<lambda>(n, fs). (n, function_sig'.truncate fs)) fun2)"
proof-
  obtain n1 b1 where F1 : "fun1 = (n1, b1)"
    by(cases fun1; auto)

  obtain n2 b2 where F2 : "fun2 = (n2, b2)"
    by(cases fun2; auto)

  show ?thesis
  proof(cases "f_sig_body b1")
    case B1 : (YulBuiltin x1)

    then obtain x2 where B2 : "f_sig_body b2 = YulBuiltin x2"
      using H F1 F2
      by(cases "f_sig_body b2"; auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)

    have B1' : "f_sig_body (function_sig'.truncate b1) = YulBuiltin x1"
      using B1
      by(cases b1; auto simp add: function_sig'.truncate_def)

    have B2' : "f_sig_body (function_sig'.truncate b2) = YulBuiltin x2"
      using B2
      by(cases b2; auto simp add: function_sig'.truncate_def)

    then show ?thesis using B1 B2 H F1 F2 B1' B2'
      by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
  next
    case B1 : (YulFunction x1)

    then obtain x2 where B2 : "f_sig_body b2 = YulFunction x2"
      using H F1 F2
      by(cases "f_sig_body b2"; auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)

    have B1' : "f_sig_body (function_sig'.truncate b1) = YulFunction x1"
      using B1
      by(cases b1; auto simp add: function_sig'.truncate_def)

    have B2' : "f_sig_body (function_sig'.truncate b2) = YulFunction x2"
      using B2
      by(cases b2; auto simp add: function_sig'.truncate_def)

    show ?thesis
    proof(cases "alpha_equiv_check_decls x1 x2")
      case None
      then show ?thesis using B1 B2 H F1 F2 B1' B2'
        by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
    next
      case (Some decs)
      then show ?thesis using B1 B2 H F1 F2 B1' B2'
        by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def function_sig'.truncate_def)
    qed
  qed
qed

lemma list_all2_map :
  assumes All2 : "list_all2 P l1 l2"
  assumes F : "\<And> x y . P x y \<Longrightarrow> P' (f x) (g y)"
  shows "list_all2 P' (map f l1) (map g l2)"
  using assms
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons l1h l1t)

  then obtain l2h l2t where Cons2 :
    "l2 = l2h # l2t"
    by(cases l2; auto)

  have Tl : "list_all2 P l1t l2t"
    using Cons1.prems Cons2
    by(auto)

  show ?case using Cons1.prems Cons1.IH[OF Tl] Cons2
    by(auto)
qed

lemma alpha_equiv_funs_trunc :
  assumes H: "alpha_equiv_funs' vsubst fsubst funs1 funs2"
  shows "alpha_equiv_funs' vsubst fsubst
     (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs1)
     (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs2)"
  using alpha_equiv_fun_trunc H
  unfolding alpha_equiv_funs'_def
  using list_all2_map[of "alpha_equiv_fun vsubst fsubst" _ _
      "alpha_equiv_fun vsubst fsubst"
      "(\<lambda>(n, fs). (n, function_sig'.truncate fs))"
      "(\<lambda>(n, fs). (n, function_sig'.truncate fs))"]
  by(blast)

lemma alpha_equiv_check_decls_cases :
  assumes H: "alpha_equiv_check_decls l1 l2 = Some x"
  shows
    "(l1 = [] \<and> l2 = [] \<and> x = ([], [])) \<or>
     (\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> decls1 v1 decls2 v2 vs' .
        l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1)) \<and>
        l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs', fs) \<and>
        vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')) \<or>
      (\<exists> name1 args1 rets1 body1 name2 args2 rets2 body2 fs' .
        l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1)) \<and>
        l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs, fs') \<and>
        fs = (name1, name2)#fs') \<or>
      ((case l1h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and>
       (case l2h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and> alpha_equiv_check_decls l1t l2t = Some x))"

proof(cases l1)
  case Nil
  then show ?thesis using H
    by(cases l2; auto)
next
  case C1: (Cons l1h l1t)

  then obtain l2h l2t where C2 :
    "l2 = l2h # l2t"
    using H
    by(cases l2; auto)

  obtain x1 x2 where X: "x = (x1, x2)"
    by(cases x; auto)

  show ?thesis
  proof(cases l1h)
    case (YulFunctionCallStatement x1)

    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulAssignmentStatement x2)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case L1h : (YulVariableDeclarationStatement vds)

    then obtain vds' where L2h : "l2h = YulVariableDeclarationStatement vds'"
      using H C1 C2 X
      by(cases l2h; auto)

    then have Conc' : "(\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> decls1 v1 decls2 v2 vs' .
        l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1)) \<and>
        l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs', fs) \<and>
        vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')))"
      using H C1 C2 X L1h
      by(cases vds; cases vds'; auto split: option.splits if_splits)

    then show ?thesis by metis
      
  next
    case L1h : (YulFunctionDefinitionStatement fds)

    then obtain fds' where L2h : "l2h = YulFunctionDefinitionStatement fds'"
      using H C1 C2 X
      by(cases l2h; auto)

    then have Conc' : "(\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> name1 args1 rets1 body1 name2 args2 rets2 body2 fs' .
        l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1)) \<and>
        l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs, fs') \<and>
        fs = (name1, name2)#fs'))"
      using H C1 C2 X L1h
      by(cases fds; cases fds'; auto split: option.splits if_splits)

    then show ?thesis by metis
  next
    case (YulIf x51 x52)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulSwitch x61 x62)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulForLoop x71 x72 x73 x74)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case YulBreak
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
  case YulContinue
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case YulLeave
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulBlock x11)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  qed
qed

lemma alpha_equiv_check_decls_cases_alt :
  assumes H: "alpha_equiv_check_decls l1 l2 = Some x"
  shows
    "(l1 = [] \<and> l2 = [] \<and> x = ([], [])) \<or>
     (\<exists> l1h l1t l2h l2t fs vs decls1 v1 decls2 v2 vs' . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
        l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1)) \<and>
        l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs', fs) \<and>
        vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')) \<or>
      (\<exists> l1h l1t l2h l2t fs vs name1 args1 rets1 body1 name2 args2 rets2 body2 fs' . x = (vs, fs) \<and>
        l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
        l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1)) \<and>
        l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs, fs') \<and>
        fs = (name1, name2)#fs') \<or>
      (\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and>
      (case l1h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and>
       (case l2h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and> alpha_equiv_check_decls l1t l2t = Some x)"
proof(cases l1)
  case Nil
  then show ?thesis using H
    by(cases l2; auto)
next
  case C1: (Cons l1h l1t)

  then obtain l2h l2t where C2 :
    "l2 = l2h # l2t"
    using H
    by(cases l2; auto)

  obtain x1 x2 where X: "x = (x1, x2)"
    by(cases x; auto)

  show ?thesis
  proof(cases l1h)
    case (YulFunctionCallStatement x1)

    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulAssignmentStatement x2)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case L1h : (YulVariableDeclarationStatement vds)

    then obtain vds' where L2h : "l2h = YulVariableDeclarationStatement vds'"
      using H C1 C2 X
      by(cases l2h; auto)

    then have Conc' : "(\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> decls1 v1 decls2 v2 vs' .
        l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1)) \<and>
        l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs', fs) \<and>
        vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')))"
      using H C1 C2 X L1h
      by(cases vds; cases vds'; auto split: option.splits if_splits)

    then show ?thesis by metis
      
  next
    case L1h : (YulFunctionDefinitionStatement fds)

    then obtain fds' where L2h : "l2h = YulFunctionDefinitionStatement fds'"
      using H C1 C2 X
      by(cases l2h; auto)

    then have Conc' : "(\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> name1 args1 rets1 body1 name2 args2 rets2 body2 fs' .
        l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1)) \<and>
        l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs, fs') \<and>
        fs = (name1, name2)#fs'))"
      using H C1 C2 X L1h
      by(cases fds; cases fds'; auto split: option.splits if_splits)

    then show ?thesis by metis
  next
    case (YulIf x51 x52)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulSwitch x61 x62)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulForLoop x71 x72 x73 x74)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case YulBreak
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
  case YulContinue
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case YulLeave
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  next
    case (YulBlock x11)
    then have "(\<exists>l1h l1t l2h l2t fs vs.
        x = (vs, fs) \<and>
        l1 = l1h # l1t \<and>
        l2 = l2h # l2t \<and>
        yul_statement_same_constructor l1h l2h \<and>
        (case l1h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        (case l2h of YulVariableDeclarationStatement x \<Rightarrow> False
         | YulFunctionDefinitionStatement x \<Rightarrow> False
         | _ \<Rightarrow> True) \<and>
        alpha_equiv_check_decls l1t l2t = Some x)" using H C1 C2 X
      by(cases l2h; auto)

    then show ?thesis by blast
  qed
qed

lemma alpha_equiv_check_decls_result :
  assumes Decls : "alpha_equiv_check_decls sts1 sts2 = Some (locs', funcs')"
  shows "\<exists> vs1 fs1 vs2 fs2 . 
    length sts1 = length sts2 \<and>
    get_var_decls sts1 = (map fst locs') \<and>
    get_var_decls sts2 = (map snd locs') \<and>
    get_fun_decls sts1 = (map fst funcs') \<and>
    get_fun_decls sts2 = (map snd funcs')"
  using assms
proof(induction sts1 arbitrary: sts2 locs' funcs')
  case Nil
  then show ?case 
    by(cases sts2; auto)
next
  case Cons1 : (Cons sts1h sts1t)

  then obtain sts2h sts2t where Cons2 :
    "sts2 = sts2h # sts2t"
    using Cons1.prems
    by(cases sts2; auto)

  consider 
    (1) "(sts1h#sts1t = [] \<and> sts2 = [] \<and> (locs', funcs') = ([], []))" |
    (2) l1h l1t l2h l2t fs vs decls1 v1 decls2 v2 vs' where 
      "(locs', funcs') = (vs, fs)"
      "sts1h#sts1t  = l1h # l1t"
      "sts2 = l2h # l2t"
      "yul_statement_same_constructor l1h l2h"
      "l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1))"
      "l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2))"
      "alpha_equiv_check_decls l1t l2t = Some (vs', fs)"
      "vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                  (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')" |
    (3) l1h l1t l2h l2t fs vs name1 args1 rets1 body1 name2 args2 rets2 body2 fs' where
      "(locs', funcs') = (vs, fs)"
      "sts1h#sts1t  = l1h # l1t"
      "sts2 = l2h # l2t"
      "yul_statement_same_constructor l1h l2h"
      "l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1))"
      "l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2))"
      "alpha_equiv_check_decls l1t l2t = Some (vs, fs')"
      "fs = (name1, name2)#fs'" |
    (4) l1h l1t l2h l2t fs vs where
    "(locs', funcs') = (vs, fs)"
     "sts1h#sts1t  = l1h # l1t"
     "sts2 = l2h # l2t"
     "yul_statement_same_constructor l1h l2h"
    "(case l1h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True)"
    "(case l2h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True)"
    "alpha_equiv_check_decls l1t l2t = Some (locs', funcs')"
    using alpha_equiv_check_decls_cases_alt[OF Cons1.prems(1)] unfolding Cons2
    by(clarsimp; metis)

  then show ?case
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2

    have Arg : "alpha_equiv_check_decls sts1t l2t = Some (vs', fs)"
      using Cons1.prems 2
      by(auto)

    show ?thesis using Cons1.prems Cons1.IH[OF Arg] Cons2 2
      by(auto simp add: split: if_split_asm prod.splits)
  next
    case 3

    have Arg : "alpha_equiv_check_decls sts1t l2t = Some (vs, fs')"
      using Cons1.prems 3
      by(auto)

    show ?thesis using Cons1.prems Cons1.IH[OF Arg] Cons2 3
      by(auto simp add: split: if_split_asm prod.splits)
  next
    case 4

    have Arg : "alpha_equiv_check_decls sts1t l2t = Some (vs, fs)"
      using Cons1.prems 4
      by(auto)

    show ?thesis using Cons1.prems Cons1.IH[OF Arg] Cons2 4
      apply(cases l1h)
                apply(cases l2h; auto)
               apply(cases l2h; auto)
              apply(cases l2h; auto)
             apply(cases l2h; auto)
            apply(cases l2h; auto)
           apply(cases l2h; auto)
          apply(cases l2h; auto)
         apply(cases l2h; auto)
      apply(cases l2h; auto)
      apply(cases l2h; auto)
      apply(cases l2h; auto)
      done
  qed
qed
  

(* NB we are using combine_keep to avoid making
changes to names field of existing functions.
we actually know that there are no conflicts.

induction on number of function decls in sts.
*) 
declare [[show_types]]

lemma alpha_equiv_expr_fun_empty :
  fixes x1 :: "(String.literal, 'a, 'b) YulFunctionCall'"
  fixes st1 :: "(String.literal, 'a, 'b) YulExpression'"
  shows "(\<forall> vsubst fsubst x2 f1 es1 f2 es2 . 
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<longrightarrow>
          x1 = (YulFunctionCall f1 es1) \<longrightarrow>
          x2 = (YulFunctionCall f2 es2) \<longrightarrow> 
      alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2)
    \<and> (\<forall> vsubst fsubst st2 . alpha_equiv_expr' vsubst fsubst st1 st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) st1 st2)"
proof(induction rule: YulFunctionCall'_YulExpression'.induct)

  case H : (YulFunctionCall x1 x2)
(*
  assume H: "(\<And>x2a::(String.literal, 'a, 'b) YulExpression'.
           x2a \<in> set x2 \<Longrightarrow>
           \<forall>(vsubst::(String.literal \<times> String.literal) list list) (fsubst::(String.literal \<times> String.literal) list list)
              st2::(String.literal, 'a, 'b) YulExpression'. alpha_equiv_expr' vsubst fsubst x2a st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) x2a st2)"
*)
  hence H' : "(\<And>x2a::(String.literal, 'a, 'b) YulExpression'.
           x2a \<in> set x2 \<Longrightarrow>
           (\<And>(vsubst::(String.literal \<times> String.literal) list list) (fsubst::(String.literal \<times> String.literal) list list)
              st2::(String.literal, 'a, 'b) YulExpression'. alpha_equiv_expr' vsubst fsubst x2a st2 \<Longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) x2a st2))"
    by blast

  have Conc' : 
"\<And> (vsubst::(String.literal \<times> String.literal) list list) (fsubst::(String.literal \<times> String.literal) list list)
          (x2a::(String.literal, 'a, 'b) YulFunctionCall') (f1::String.literal) (es1::(String.literal, 'a, 'b) YulExpression' list) (f2::String.literal)
          es2::(String.literal, 'a, 'b) YulExpression' list.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression (YulFunctionCall x1 x2)) (YulFunctionCallExpression x2a) \<Longrightarrow>
          YulFunctionCall x1 x2 = YulFunctionCall f1 es1 \<Longrightarrow>
          x2a = YulFunctionCall f2 es2 \<Longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
  proof-
    fix vsubst fsubst x2a f1 es1 f2 es2

    assume Hi1 : "alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression (YulFunctionCall x1 x2)) (YulFunctionCallExpression x2a)"
    assume Hi2 : "YulFunctionCall x1 x2 = YulFunctionCall f1 es1"
    assume Hi3 : "x2a = YulFunctionCall f2 es2" 
    show "alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      using H'
  qed
  then show " \<forall>(vsubst::(String.literal \<times> String.literal) list list) (fsubst::(String.literal \<times> String.literal) list list)
          (x2a::(String.literal, 'a, 'b) YulFunctionCall') (f1::String.literal) (es1::(String.literal, 'a, 'b) YulExpression' list) (f2::String.literal)
          es2::(String.literal, 'a, 'b) YulExpression' list.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression (YulFunctionCall x1 x2)) (YulFunctionCallExpression x2a) \<longrightarrow>
          YulFunctionCall x1 x2 = YulFunctionCall f1 es1 \<longrightarrow>
          x2a = YulFunctionCall f2 es2 \<longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
    by blast
next
  
  
  fix vsubst fsubst x2a f1 es1 f2 es2

    assume "alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression (YulFunctionCall x1 x2)) (YulFunctionCallExpression x2a)"

  case H: (YulFunctionCall x1x x2x)

  have Conc' : "\<And> (x1::(String.literal, 'a, 'b) YulFunctionCall') (vsubst::(String.literal \<times> String.literal) list list)
       (fsubst::(String.literal \<times> String.literal) list list) (x2::(String.literal, 'a, 'b) YulFunctionCall') (f1::String.literal)
       (es1::(String.literal, 'a, 'b) YulExpression' list) (f2::String.literal) es2::(String.literal, 'a, 'b) YulExpression' list.
       alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<Longrightarrow>
       x1 = YulFunctionCall f1 es1 \<Longrightarrow>
       x2 = YulFunctionCall f2 es2 \<Longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
  proof-
    fix x1 :: "(String.literal, 'a, 'b) YulFunctionCall'"
    fix vsubst fsubst x2 f1 es1 f2 es2

    assume Hi1: "alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2)"
    assume Hi2 : "x1 = YulFunctionCall f1 es1"
    assume Hi3 : "x2 = YulFunctionCall f2 es2"

    show "alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      using Hi1 Hi2 Hi3 H
      apply(auto simp add: alpha_equiv_name'_def)
      sorry
  qed

  then show ?case by blast
next
  case H: (YulFunctionCallExpression x)

  have H' : "\<And> (x1 :: (String.literal, 'a, 'b) YulFunctionCall') vsubst fsubst x2 f1 es1 f2 es2.
     alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<Longrightarrow>
     x1 = YulFunctionCall f1 es1 \<Longrightarrow>
     x2 = YulFunctionCall f2 es2 \<Longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
  proof-
    fix x1 :: "((String.literal, 'a, 'b) YulFunctionCall')"
    fix vsubst fsubst x2 f1 es1 f2 es2
    assume Hi1 : "alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2)"
    assume Hi2 : "x1 = YulFunctionCall f1 es1"
    assume Hi3 : "x2 = YulFunctionCall f2 es2" 
    show "alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      using H Hi1 Hi2 Hi3
      by(blast)
  qed
  have Conc' : "\<And>vsubst fsubst (st2 :: (String.literal, 'a, 'b) YulExpression').
       alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x) st2 \<Longrightarrow>
       alpha_equiv_expr' vsubst ([] # fsubst) (YulFunctionCallExpression x) st2"
  proof-
    fix vsubst fsubst st2
    assume Hi : "alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x) st2"

    obtain x2 where X2 : "st2 = YulFunctionCallExpression x2"
      using Hi by (cases st2; auto)

    obtain f1 es1 where Xc : "x = YulFunctionCall f1 es1"
      by(cases x; auto)

    obtain f2 es2 where Xc2 : "x2 = YulFunctionCall f2 es2"
      by(cases x2; auto)

    show "alpha_equiv_expr' vsubst ([] # fsubst) (YulFunctionCallExpression x) st2"
      using H'[OF Hi[unfolded X2] Xc Xc2] X2 Xc Xc2
      by(auto simp add: alpha_equiv_name'_def)
  qed

  then show ?case
    by blast
next
  case H : (YulIdentifier x)

  then show ?case
    sorry
next
  case H : (YulLiteralExpression x)
  then show ?case
    sorry
qed

    show "\<And>(x1 :: String.literal) x2.
       (\<And>(x2a :: (String.literal, 'a, 'b) YulExpression') . x2a \<in> set x2 \<Longrightarrow> \<forall>vsubst fsubst st2. alpha_equiv_expr' vsubst fsubst x2a st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) x2a st2) \<Longrightarrow>
       \<forall>x1 vsubst fsubst x2 f1 es1 f2 es2.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<longrightarrow>
          x1 = YulFunctionCall f1 es1 \<longrightarrow>
          x2 = YulFunctionCall f2 es2 \<longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
    proof-
      fix x1 :: "String.literal"
      fix x2 :: "((String.literal, 'a, 'b) YulExpression') list"

      assume Hset : "(\<And>x2a. x2a \<in> set x2 \<Longrightarrow> \<forall>vsubst fsubst st2. alpha_equiv_expr' vsubst fsubst x2a st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) x2a st2)"

      show "\<forall>x1 vsubst fsubst x2 f1 es1 f2 es2.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<longrightarrow>
          x1 = YulFunctionCall f1 es1 \<longrightarrow>
          x2 = YulFunctionCall f2 es2 \<longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      proof-
        fix x1 :: "(String.literal, 'e, 'f) YulFunctionCall'" 
        fix vsubst :: "((String.literal \<times> String.literal) list list)"
        fix fsubst x2 f1 es1 f2 es2

        assume H' : "
           alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<Longrightarrow>
           x1 = YulFunctionCall f1 es1 \<Longrightarrow>
           x2 = YulFunctionCall f2 es2"

        show "alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      sorry
  next
    show "\<And>x. \<forall>vsubst fsubst st2. alpha_equiv_expr' vsubst fsubst (YulIdentifier x) st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) (YulIdentifier x) st2"
      sorry
  next
    show "\<And>x. \<forall>vsubst fsubst st2.
            alpha_equiv_expr' vsubst fsubst (YulLiteralExpression x) st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) (YulLiteralExpression x) st2"
      sorry
  qed

    case H: (YulFunctionCallExpression x1)
    (*fix x2 :: "(String.literal, 'a, 'b) YulExpression' list"*)
    have H' : "\<And> (x1 :: (String.literal, 'a, 'b) YulFunctionCall') vsubst fsubst x2 f1 es1 f2 es2.
     alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<Longrightarrow>
     x1 = YulFunctionCall f1 es1 \<Longrightarrow>
     x2 = YulFunctionCall f2 es2 \<Longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      using H
      by blast

   (* assume Hset : "(\<And>x2a. x2a \<in> set x2 \<Longrightarrow> \<forall>vsubst fsubst st2. alpha_equiv_expr' vsubst fsubst x2a st2 \<longrightarrow> alpha_equiv_expr' vsubst ([] # fsubst) x2a st2)"*)

    have Conc' : "\<And> x1 vsubst fsubst x2 f1 es1 f2 es2.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<Longrightarrow>
          x1 = YulFunctionCall f1 es1 \<Longrightarrow>
          x2 = YulFunctionCall f2 es2 \<Longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"
      sorry

    show " \<forall>x1 vsubst fsubst x2 f1 es1 f2 es2.
          alpha_equiv_expr' vsubst fsubst (YulFunctionCallExpression x1) (YulFunctionCallExpression x2) \<longrightarrow>
          x1 = YulFunctionCall f1 es1 \<longrightarrow>
          x2 = YulFunctionCall f2 es2 \<longrightarrow> alpha_equiv_name' ([] # fsubst) f1 f2 \<and> list_all2 (alpha_equiv_expr' vsubst ([] # fsubst)) es1 es2"

      then show ?thesis
    apply(cases x1; cases st2; auto)
    apply(case_tac x1aa; auto)
  next
  case (YulIdentifier x2)
  then show ?thesis sorry
next
  case (YulLiteralExpression x3)
  then show ?thesis sorry
qed


lemma alpha_equiv_statement_fun_empty :
  assumes H : "alpha_equiv_statement' vsubst fsubst st1 st2"
  shows "alpha_equiv_statement' vsubst ([] # fsubst) st1 st2"
proof(cases st1)
  case (YulFunctionCallStatement x1)
  then show ?thesis using H
    apply(cases x1; cases st2; auto)
    apply(case_tac x1aa; auto)
next
  case (YulAssignmentStatement x2)
  then show ?thesis sorry
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

  sorry

(* need a version of this for statements. *)
lemma alpha_equiv_fun_empty :
  assumes H: "alpha_equiv_fun vsubst fsubst f1 f2"
  shows "alpha_equiv_fun vsubst ([]#fsubst) f1 f2"
  using H
proof(induction fsubst arbitrary: vsubst)
  case Nil

  obtain n1 s1 where F1 : "f1 = (n1, s1)"
    by(cases f1; auto)

  obtain n2 s2 where F2 : "f2 = (n2, s2)"
    by(cases f2; auto)

  show ?case
  proof(cases "f_sig_body s1")
    case (YulBuiltin x1)
    then show ?thesis using Nil F1 F2
    by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
  next
    case X1 : (YulFunction x1)

    obtain x2 where X2 : "f_sig_body s2 = YulFunction x2"
      using Nil X1 F1 F2
      by(cases "f_sig_body s2"; auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)

(* alpha_equiv_statement'_nil - adding nil on the end has no effect *)
    then show ?thesis using Nil F1 F2 X1 X2 list_all2_map
      apply(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def
split: option.splits) 
      sorry
  qed
next
  case (Cons fh ft)

  obtain n1 s1 where F1 : "f1 = (n1, s1)"
    by(cases f1; auto)

  obtain n2 s2 where F2 : "f2 = (n2, s2)"
    by(cases f2; auto)

  show ?case
  proof(cases "f_sig_body s1")
    case (YulBuiltin x1)
    then show ?thesis using Cons.prems F1 F2
    by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
  next
    case X1 : (YulFunction x1)

    obtain x2 where X2 : "f_sig_body s2 = YulFunction x2"
      using Cons.prems X1 F1 F2
      by(cases "f_sig_body s2"; auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)

(* alpha_equiv_statement'_nil - adding nil on the end has no effect *)
    then show ?thesis using Cons F1 F2 X1 X2
      apply(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def
split: option.splits) 
      sorry
  qed

  then show ?case
    apply(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
qed

  apply(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def)
  apply(case_tac "f_sig_body s1"; auto)
  apply(case_tac "f_sig_body s2"; auto)
  apply(case_tac "alpha_equiv_check_decls x2 x2a"; auto)


lemma alpha_equiv_gather_funs'_combine :
  assumes Decls : "alpha_equiv_check_decls sts1 sts2 = Some (locs', funcs')"
  assumes Equiv : "alpha_equiv_funs' vsubst' fsubst funs1 funs2"
  assumes Sts : "list_all2 (alpha_equiv_statement' (locs' # vsubst') (funcs' # fsubst))
     sts1 sts2"
  assumes Gather1 :
    "gatherYulFunctions' (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs1) sts1 =
      Inl fs1"
  assumes Gather2 :
     "gatherYulFunctions' (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs2) sts2 =
       Inl fs2"
  shows "alpha_equiv_funs' vsubst' (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)
     (combine_keep (funs1)
       (map (\<lambda>(n, fs). (n, function_sig'.extend fs \<lparr>f_sig_visible = map fst fs1\<rparr>))
         fs1))
     (combine_keep (funs2)
       (map (\<lambda>(n, fs). (n, function_sig'.extend fs \<lparr>f_sig_visible = map fst fs2\<rparr>))
         fs2))"
  using assms
proof(induction funcs' arbitrary: sts1 sts2 locs' funs1 fs1 funs1 funs2 fs2 vsubst' fsubst)
  case Nil1 : Nil

  have Nil1' : "get_fun_decls sts1 = []" "get_fun_decls sts2 = []"
    using alpha_equiv_check_decls_result[OF Nil1.prems(1)]
    by auto

  have X1 : "fs1 = (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs1)"
    sorry

  have X2 : "fs2 = (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) funs2)"
    sorry

  show ?case using Nil1 Nil1' X1 X2
    apply(auto simp add: alpha_equiv_funs'_def alpha_equiv_fun_def)

  then show ?case
    apply(auto)
    sorry
next
  case Cons1 : (Cons fs1h fs1t)

  have Nil2 : "sts2 = []"
    using Nil1
    by(cases sts2; auto)

  then show ?case using Nil1 alpha_equiv_funs_trunc[OF Nil1(2)]
    by(auto simp add: alpha_equiv_funs'_def alpha_equiv_fun_def
get_fun_decls_def get_var_decls_def)
next
  case Cons1 : (Cons h1 t1)

  using assms
proof(induction sts1 arbitrary: sts2 locs' funcs' funs1 fs1 funs2 fs2 vsubst' fsubst)
  case Nil1 : Nil

  have Nil2 : "sts2 = []"
    using Nil1
    by(cases sts2; auto)

  then show ?case using Nil1 alpha_equiv_funs_trunc[OF Nil1(2)]
    by(auto simp add: alpha_equiv_funs'_def alpha_equiv_fun_def
get_fun_decls_def get_var_decls_def)
next
  case Cons1 : (Cons h1 t1)

  then obtain h2 t2 where Cons2 : "sts2 = h2#t2"
    by(cases sts2; auto)

  consider 
    (1) "(h1#t1 = [] \<and> sts2 = [] \<and> (locs', funcs') = ([], []))" |
    (2) l1h l1t l2h l2t fs vs decls1 v1 decls2 v2 vs' where 
      "(locs', funcs') = (vs, fs)"
      "h1#t1 = l1h # l1t"
      "sts2 = l2h # l2t"
      "yul_statement_same_constructor l1h l2h"
      "l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1))"
      "l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2))"
      "alpha_equiv_check_decls l1t l2t = Some (vs', fs)"
      "vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                  (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')" |
    (3) l1h l1t l2h l2t fs vs name1 args1 rets1 body1 name2 args2 rets2 body2 fs' where
      "(locs', funcs') = (vs, fs)"
      "h1#t1 = l1h # l1t"
      "sts2 = l2h # l2t"
      "yul_statement_same_constructor l1h l2h"
      "l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1))"
      "l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2))"
      "alpha_equiv_check_decls l1t l2t = Some (vs, fs')"
      "fs = (name1, name2)#fs'" |
    (4) l1h l1t l2h l2t fs vs where
    "(locs', funcs') = (vs, fs)"
     "h1#t1 = l1h # l1t"
     "sts2 = l2h # l2t"
     "yul_statement_same_constructor l1h l2h"
    "(case l1h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True)"
    "(case l2h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True)"
    "alpha_equiv_check_decls l1t l2t = Some (locs', funcs')"
    using alpha_equiv_check_decls_cases_alt[OF Cons1.prems(1)] unfolding Cons2
    by(clarsimp; metis)

  then show ?case
  proof cases
    case 1
    then show ?thesis using Cons1 by auto
  next
    case 2

    have Eq0 : "locs' = vs" "funcs' = fs"
      using 2 by auto

    have Eq1 : "h1 = l1h" "t1 = l1t"
      using 2 by auto

    have Eq2 : "h2 = l2h" "t2 = l2t"
      using 2 Cons2 by auto

    have All_tl : "list_all2 (alpha_equiv_statement' (locs' # vsubst') (funcs' # fsubst)) (l1t) l2t"
      using Cons1.prems Cons2 Eq0 Eq1 Eq2
      by auto

    show ?thesis 
      using Cons1.IH[unfolded Cons2, unfolded Eq0, unfolded Eq1, unfolded Eq2
                    , OF "2"(7) Cons1.prems(2)] Cons1.prems
      using All_tl[unfolded Eq0]
      using "2"(8)
(* something related to extending locals environment...
   relate decls to insert values? *)
  next
    case 3
    then show ?thesis sorry
  next
    case 4
    then show ?thesis sorry
  qed

(*
"(l1 = [] \<and> l2 = [] \<and> x = ([], [])) \<or>
     (\<exists> l1h l1t l2h l2t fs vs . x = (vs, fs) \<and>
      l1 = l1h # l1t \<and> l2 = l2h # l2t \<and> yul_statement_same_constructor l1h l2h \<and> 
      (\<exists> decls1 v1 decls2 v2 vs' .
        l1h = (YulVariableDeclarationStatement (YulVariableDeclaration decls1 v1)) \<and>
        l2h = (YulVariableDeclarationStatement (YulVariableDeclaration decls2 v2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs', fs) \<and>
        vs = ((zip (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls1)
                   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls2)) @ vs')) \<or>
      (\<exists> name1 args1 rets1 body1 name2 args2 rets2 body2 fs' .
        l1h = (YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1)) \<and>
        l2h = (YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2)) \<and>
        alpha_equiv_check_decls l1t l2t = Some (vs, fs') \<and>
        fs = (name1, name2)#fs') \<or>
      ((case l1h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and>
       (case l2h of
        YulVariableDeclarationStatement _ \<Rightarrow> False
        | YulFunctionDefinitionStatement _ \<Rightarrow> False
        | _ \<Rightarrow> True) \<and> alpha_equiv_check_decls l1t l2t = Some x))"
*)
  obtain locs0 funcs0 locs1 funcs1 where
    Split : "alpha_equiv_check_decls t1 t2 = Some (locs1, funcs1)"
       "locs' = locs0 @ locs1" "funcs' = funcs0 @ funcs1"
    sorry
  show ?case using Cons1.IH[OF Split(1) Cons1.prems(2)] Cons1.prems(3) 
    using Cons1.prems alpha_equiv_funs_trunc
      apply(auto simp add: alpha_equiv_funs'_def alpha_equiv_fun_def 
       get_fun_decls_def get_var_decls_def Let_def split:if_splits)
      apply(clarsimp)

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
    case F1 : (YulFunctionDefinitionStatement f1)
    
    then obtain names1 args1 rets1 body1 where
      FS1 : "f1 = YulFunctionDefinition names1 args1 rets1 body1"
      by(cases f1; auto)

    obtain f2 where F2 :
      "x2 = YulFunctionDefinitionStatement f2"
      using ES1 ES2 F1 FS1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain names2 args2 rets2 body2 where
      FS2 : "f2 = YulFunctionDefinition names2 args2 rets2 body2"
      by(cases f2; auto)

    show ?thesis
      using ES1 F1 FS1 ES2 F2 FS2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case I1 : (YulIf cond1 body1)

    obtain cond2 body2 where I2 :
      "x2 = YulIf cond2 body2"
      using ES1 ES2 I1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 I1 ES2 I2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case S1 : (YulSwitch cond1 body1)

    obtain cond2 body2 where S2 :
      "x2 = YulSwitch cond2 body2"
      using ES1 ES2 S1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 S1 ES2 S2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)

  next
    case L1 : (YulForLoop pre1 cond1 post1 body1)

    obtain pre2 cond2 post2 body2 where L2 :
      "x2 = YulForLoop pre2 cond2 post2 body2"
      using ES1 ES2 L1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis sorry

  next
    case B1 : YulBreak

    then have B2 : "x2 = YulBreak"
      using ES1 ES2 B1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case C1 : YulContinue
    then have C2 : "x2 = YulContinue"
      using ES1 ES2 C1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 C1 ES2 C2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case L1 : YulLeave
    then have L2 : "x2 = YulLeave"
      using ES1 ES2 L1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def)
  next
    case B1 : (YulBlock sts1)

    obtain sts2 where B2 :
      "x2 = YulBlock sts2"
      using ES1 ES2 B1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    obtain fs1 where Fs1 :
      "gatherYulFunctions'
                (map (\<lambda>(n, fs). (n, function_sig'.truncate fs))
                  (funs r1)) sts1 = Inl fs1"
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def split: sum.splits)

    obtain fs2 where Fs2 :
      "gatherYulFunctions'
                (map (\<lambda>(n, fs). (n, function_sig'.truncate fs))
                  (funs r2)) sts2 = Inl fs2"
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def split: sum.splits)

    obtain locs' funcs' where Decls :
      "alpha_equiv_check_decls sts1 sts2 = Some (locs', funcs')"
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    show ?thesis
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls
        alpha_equiv_locals_f_change[of vsubst' fsubst "locals r1" "locals r2" 
          "(zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)"]

      apply(auto simp add: alpha_equiv_results'_def)
(* 2 things needed here.
1. alpha_equiv_fun' of inputs implies alpha_equiv_funs' when updating the
inputs using combine_keep and updating fsubst using the decls 
2. equivalence of stack elements
*)
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