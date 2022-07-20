theory Alpha_Equiv_Fun
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

definition subst_ok :: "subst \<Rightarrow> bool" where
"subst_ok x =
  True"

fun get_var_decls ::
  "('v, 't) YulStatement list \<Rightarrow>
   (YulIdentifier list)" where
"get_var_decls [] = []"
| "get_var_decls ((YulVariableDeclarationStatement (YulVariableDeclaration decls v))#t) =
   (map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls) @ (get_var_decls t)"
| "get_var_decls (h#t) = get_var_decls t"

fun get_fun_decls ::
"('v, 't) YulStatement list \<Rightarrow>
 (YulIdentifier list)" where
"get_fun_decls [] = []"
| "get_fun_decls ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t) =
   name # get_fun_decls t"
| "get_fun_decls (h#t) = 
    get_fun_decls t"

(* whenever we extend the variable context, we also need to update subst.  *)
(* also need to update subst on function entry. *)

(* gather yul functions / get_fun_decls *)

fun subst_update_enter_statement ::
  "subst \<Rightarrow> 
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst)" where
"subst_update_enter_statement fsubst (YulBlock ls1) (YulBlock ls2) =
  ((zip (get_fun_decls ls1) (get_fun_decls ls2))# fsubst)"
| "subst_update_enter_statement fsubst _ _ = (fsubst)"

(*
fun subst_update_break ::
  "subst \<Rightarrow> 
*)

(* TODO: one approach to solving the problems around break/continue/etc.
 * is to handle them here. this requires changing type signatures though.
 * or does it? maybe we can get away with just removing the first element *)

fun subst_update_exit_statement ::
  "subst \<Rightarrow> 
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst) option" where
"subst_update_exit_statement fsubst
  (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1))
  (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) = Some fsubst"
| "subst_update_exit_statement fsubst
  (YulBlock ls1)
  (YulBlock ls2) = 
  (case (fsubst) of
    (fsh # fsubst') \<Rightarrow> Some (fsubst')
   | _ \<Rightarrow> None)"
(* bogus cases mixed with noop cases here. *)
| "subst_update_exit_statement fsubst _ _ = Some (fsubst)" 

(* TODO: update fsubst with sig? *)
fun subst_update_enter_fun_call ::
    "subst \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> (subst)"
    where
  "subst_update_enter_fun_call fsubst
    sig1 sig2 = fsubst
    "

fun subst_update_exit_fun_call ::
  "subst \<Rightarrow>  (subst) option"
  where
"subst_update_exit_fun_call (fsh # fsubst') = Some (fsubst')"
| "subst_update_exit_fun_call fsubst = None"

fun subst_update ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> (subst) option" where
"subst_update fsubst (EnterStatement s1) (EnterStatement s2) =
  Some (subst_update_enter_statement fsubst s1 s2)"
| "subst_update fsubst (ExitStatement s1 _ _) (ExitStatement s2 _ _) =
  subst_update_exit_statement fsubst s1 s2"
| "subst_update fsubst (EnterFunctionCall f1 s1) (EnterFunctionCall f2 s2) =
  Some (subst_update_enter_fun_call fsubst s1 s2)"
| "subst_update fsubst (ExitFunctionCall _ _ _ _ _) (ExitFunctionCall _ _ _ _ _) = 
  subst_update_exit_fun_call fsubst"
| "subst_update fsubst _ _ = Some (fsubst)"

(* subst_updatex is used when comparing stack element lists.
 * it does not extend the context when processing statement entry,
 * but does remove context elements on statement exit.
 *)
fun subst_updatex_enter_statement ::
  "subst \<Rightarrow> 
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst)" where
"subst_updatex_enter_statement fsubst (YulBlock ls1) (YulBlock ls2) =
  (fsubst)"
| "subst_updatex_enter_statement fsubst _ _ = (fsubst)"

fun subst_updatex_exit_statement ::
  "subst \<Rightarrow> 
   ('v, 't) YulStatement \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (subst) option" where
"subst_updatex_exit_statement fsubst
  (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1))
  (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) = Some fsubst"
| "subst_updatex_exit_statement fsubst
  (YulBlock ls1)
  (YulBlock ls2) = 
  (case (fsubst) of
    (fsh # fsubst') \<Rightarrow> Some (fsubst')
   | _ \<Rightarrow> None)"
(* bogus cases mixed with noop cases here. *)
| "subst_updatex_exit_statement fsubst _ _ = Some (fsubst)" 

(* TODO: update fsubst with sig? *)
fun subst_updatex_enter_fun_call ::
    "subst \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> (subst)"
    where
  "subst_updatex_enter_fun_call fsubst
    sig1 sig2 = fsubst
    "

fun subst_updatex_exit_fun_call ::
  "subst \<Rightarrow>  (subst) option"
  where
"subst_updatex_exit_fun_call (fsh # fsubst') = Some (fsubst')"
| "subst_updatex_exit_fun_call fsubst = None"

fun subst_updatex ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> (subst) option" where
"subst_updatex fsubst (EnterStatement s1) (EnterStatement s2) =
  Some (subst_updatex_enter_statement fsubst s1 s2)"
| "subst_updatex fsubst (ExitStatement s1 _ _) (ExitStatement s2 _ _) =
  subst_updatex_exit_statement fsubst s1 s2"
| "subst_updatex fsubst (EnterFunctionCall f1 s1) (EnterFunctionCall f2 s2) =
  Some (subst_updatex_enter_fun_call fsubst s1 s2)"
| "subst_updatex fsubst (ExitFunctionCall _ _ _ _ _) (ExitFunctionCall _ _ _ _ _) = 
  subst_updatex_exit_fun_call fsubst"
| "subst_updatex fsubst _ _ = Some (fsubst)"


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

fun yul_expression_same_constructor ::
  "('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
"yul_expression_same_constructor
  (YulFunctionCallExpression _) ex2 =
  (case ex2 of
    (YulFunctionCallExpression _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
|"yul_expression_same_constructor
  (YulLiteralExpression _) ex2 =
  (case ex2 of
    (YulLiteralExpression _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
|"yul_expression_same_constructor
  (YulIdentifier _) ex2 =
  (case ex2 of
    (YulIdentifier _) \<Rightarrow> True
    | _ \<Rightarrow> False)"

fun stackEl_same_constructor ::
  "('a, 'b, 'c) StackEl \<Rightarrow> ('a, 'b, 'c) StackEl \<Rightarrow> bool" where
"stackEl_same_constructor
  (EnterStatement _) e2 =
  (case e2 of (EnterStatement _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor
  (ExitStatement _ _ _) e2 =
  (case e2 of (ExitStatement _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor
  (EnterFunctionCall _ _) e2 =
  (case e2 of (EnterFunctionCall _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor
  (ExitFunctionCall _ _ _ _ _) e2 =
  (case e2 of (ExitFunctionCall _ _ _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor
  (Expression _) e2 =
  (case e2 of (Expression _) \<Rightarrow> True
    | _ \<Rightarrow> False)"

fun stackEl_same_constructor_strong ::
    "('a, 'b, 'c) StackEl \<Rightarrow> ('a, 'b, 'c) StackEl \<Rightarrow> bool" where
"stackEl_same_constructor_strong
  (EnterStatement st1) e2 =
  (case e2 of
    (EnterStatement st2) \<Rightarrow> yul_statement_same_constructor st1 st2
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor_strong
  (ExitStatement st1 _ _) e2 =
  (case e2 of 
    (ExitStatement st2 _ _) \<Rightarrow> yul_statement_same_constructor st1 st2
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor_strong
  (EnterFunctionCall _ _) e2 =
  (case e2 of (EnterFunctionCall _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor_strong
  (ExitFunctionCall _ _ _ _ _) e2 =
  (case e2 of (ExitFunctionCall _ _ _ _ _) \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "stackEl_same_constructor_strong
  (Expression ex1) e2 =
  (case e2 of
    (Expression ex2) \<Rightarrow> yul_expression_same_constructor ex1 ex2
    | _ \<Rightarrow> False)"

(* stronger version of check_decls
 * should we also check the other statements are the same? probably better to do a different one
 * *)
fun alpha_equiv_check_decls ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list \<Rightarrow>
    ((YulIdentifier * YulIdentifier) list) option"
  where
"alpha_equiv_check_decls
  ((YulFunctionDefinitionStatement (YulFunctionDefinition name1 args1 rets1 body1))#t1)
  ((YulFunctionDefinitionStatement (YulFunctionDefinition name2 args2 rets2 body2))#t2) = 
  (case alpha_equiv_check_decls t1 t2 of
     None \<Rightarrow> None
     | Some fds \<Rightarrow>
       (case map_of fds name1 of
        Some _ \<Rightarrow> None
        | None \<Rightarrow> 
          (case map_of (subst'_flip fds) name2 of
           Some _ \<Rightarrow> None
           | None \<Rightarrow> Some ((name1, name2)#fds))))"
| "alpha_equiv_check_decls (h1#t1) (h2#t2) = 
    (if yul_statement_same_constructor h1 h2
     then alpha_equiv_check_decls t1 t2
     else None)"
| "alpha_equiv_check_decls _ _ = None"

definition alpha_equiv_name' :: "subst \<Rightarrow> YulIdentifier \<Rightarrow> YulIdentifier \<Rightarrow> bool" where
"alpha_equiv_name' scopes n1 n2 =
  (subst_lookup scopes n1 = Some n2 \<and>
   subst_lookup (subst_flip scopes) n2 = Some n1)"

definition alpha_equiv_typed_name' ::
  "subst \<Rightarrow> ('t) YulTypedName \<Rightarrow> ('t) YulTypedName \<Rightarrow> bool" where
"alpha_equiv_typed_name' subst tn1 tn2 =
  (case tn1 of
    (YulTypedName n1 t1) \<Rightarrow>
      (case tn2 of
        (YulTypedName n2 t2) \<Rightarrow>
          (case subst_lookup subst n1 of
            None \<Rightarrow> False
            | Some n2' \<Rightarrow> 
              (case subst_lookup (subst_flip subst) n2 of
                None \<Rightarrow> False
                | Some n1' \<Rightarrow> t1 = t2 \<and> n1 = n1' \<and> n2 = n2'))))"

definition alpha_equiv_local ::
  "subst \<Rightarrow> (YulIdentifier * 'v) \<Rightarrow> (YulIdentifier * 'v) \<Rightarrow> bool" where
"alpha_equiv_local fsubst loc1 loc2 =
  (case loc1 of (n1, v1) \<Rightarrow>
  (case loc2 of (n2, v2) \<Rightarrow>
  (v1 = v2 \<and> n1 = n2)))"

definition alpha_equiv_locals' ::
  "subst \<Rightarrow> (YulIdentifier * 'v) list \<Rightarrow> (YulIdentifier * 'v) list \<Rightarrow> bool" where
"alpha_equiv_locals' fsubst locs1 locs2 =
  (locs1 = locs2)"


fun  alpha_equiv_expr' ::
  "subst \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> bool" where
  "alpha_equiv_expr' fsubst
    (YulLiteralExpression x1) (YulLiteralExpression x2) = (x1 = x2)"
| "alpha_equiv_expr' fsubst
    (YulIdentifier x1) (YulIdentifier x2) = (x1 = x2)"
(* Should be sufficient to just check for a name match here*)
| "alpha_equiv_expr' fsubst
    (YulFunctionCallExpression (YulFunctionCall fn1 args1))
    (YulFunctionCallExpression (YulFunctionCall fn2 args2)) =
    (subst_lookup fsubst fn1 = Some fn2 \<and>
     subst_lookup (subst_flip fsubst) fn2 = Some fn1 \<and>
    (list_all2 (alpha_equiv_expr' fsubst) args1 args2))"
| "alpha_equiv_expr' _ _ _ = False"



(* TODO: get rid of bool argument, fix how we construct contexts. *)
fun alpha_equiv_statement' ::
  "subst \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement \<Rightarrow> bool" where
  "alpha_equiv_statement' fsubst
    (YulFunctionCallStatement (YulFunctionCall fn1 args1)) stm2 =
    (case stm2 of
      (YulFunctionCallStatement (YulFunctionCall fn2 args2)) \<Rightarrow>
        (subst_lookup fsubst fn1 = Some fn2 \<and>
         subst_lookup (subst_flip fsubst) fn2 = Some fn1 \<and>
        (list_all2 (alpha_equiv_expr' fsubst) args1 args2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
    (YulAssignmentStatement (YulAssignment ns1 e1)) stm2 =
    (case stm2 of
      (YulAssignmentStatement (YulAssignment ns2 e2)) \<Rightarrow>
        (alpha_equiv_expr' fsubst e1 e2 \<and> ns1 = ns2)
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
    (YulVariableDeclarationStatement (YulVariableDeclaration ns1 eo1)) stm2 =
    (case stm2 of
      (YulVariableDeclarationStatement (YulVariableDeclaration ns2 eo2)) \<Rightarrow>
        ((case (eo1, eo2) of
          (Some e1, Some e2) \<Rightarrow> alpha_equiv_expr' fsubst e1 e2
          | (None, None) \<Rightarrow> True
          | _ \<Rightarrow> False) \<and>
         (ns1 = ns2))
      | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
  (YulFunctionDefinitionStatement
      (YulFunctionDefinition name1 args1 rets1 body1)) stm2 =
  (case stm2 of
    (YulFunctionDefinitionStatement
        (YulFunctionDefinition name2 args2 rets2 body2)) \<Rightarrow>
        (case alpha_equiv_check_decls body1 body2 of
          None \<Rightarrow> False
          | Some (fsubst') \<Rightarrow>
            (args1 = args2 \<and>
             rets1 = rets2 \<and>
             (list_all2 (alpha_equiv_statement' 
              (fsubst' # fsubst))
              body1 body2)))
      | _ \<Rightarrow> False)"

(* TODO: need entry/exit  cases? *)
| "alpha_equiv_statement' fsubst
  (YulIf e1 body1) stm2 =
  (case stm2 of
    (YulIf e2 body2) \<Rightarrow>
      (alpha_equiv_expr' fsubst e1 e2 \<and>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (fsubst') \<Rightarrow>
          list_all2 (alpha_equiv_statement' (fsubst' # fsubst)) body1 body2))
    | _ \<Rightarrow> False)"

(* TODO: need entry/exit  cases? *)

| "alpha_equiv_statement' fsubst
  (YulSwitch e1 cases1) stm2 =
  (case stm2 of
    (YulSwitch e2 cases2) \<Rightarrow>
      (alpha_equiv_expr' fsubst e1 e2 \<and>
      (list_all2
        (\<lambda> c1 c2 .
          (case c1 of
            (YulSwitchCase l1 body1) \<Rightarrow>
          (case c2 of
            (YulSwitchCase l2 body2) \<Rightarrow>
            (l1 = l2 \<and>
            (case alpha_equiv_check_decls body1 body2 of
              None \<Rightarrow> False
              | Some (fsubst') \<Rightarrow>
                list_all2 (alpha_equiv_statement' (fsubst' # fsubst)) body1 body2)))))
        cases1 cases2))
    | _ \<Rightarrow> False)"

(* TODO: need entry/exit  cases? *)

| "alpha_equiv_statement' fsubst
  (YulForLoop pre1 cond1 post1 body1) stm2 =
  (case stm2 of
    (YulForLoop pre2 cond2 post2 body2) \<Rightarrow>
      (case alpha_equiv_check_decls pre1 pre2 of
        None \<Rightarrow> False
        | Some (fsubst'_pre) \<Rightarrow> 
      (case alpha_equiv_check_decls post1 post2 of
        None \<Rightarrow> False
        | Some (fsubst'_post) \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (fsubst'_body) \<Rightarrow>
          (alpha_equiv_expr' (fsubst'_pre # fsubst) cond1 cond2 \<and>
           list_all2 (alpha_equiv_statement' (fsubst'_pre # fsubst)) pre1 pre2 \<and>
           list_all2 (alpha_equiv_statement' ((fsubst'_body @ fsubst'_pre) # fsubst)) body1 body2 \<and>
           list_all2 (alpha_equiv_statement' ((fsubst'_post @ fsubst'_pre) # fsubst)) post1 post2))))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
  YulBreak stm2 =
  (case stm2 of
    YulBreak \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
  YulContinue stm2 =
  (case stm2 of
    YulContinue \<Rightarrow> True
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement' fsubst
  YulLeave stm2 =
  (case stm2 of
    YulLeave \<Rightarrow> True
    | _ \<Rightarrow> False)"

(* should we not augment context here? *)
| "alpha_equiv_statement' fsubst
  (YulBlock body1) stm2 =
  (case stm2 of
    (YulBlock body2) \<Rightarrow>
      (case alpha_equiv_check_decls body1 body2 of
        None \<Rightarrow> False
        | Some (fsubst') \<Rightarrow>
          list_all2 (alpha_equiv_statement' (fsubst' # fsubst)) body1 body2)
    | _ \<Rightarrow> False)"


(* builtins need to be exactly equal.
 * TODO: can we get away with something weaker than alpha_equiv_statement' here?
 *  *)
definition alpha_equiv_function_sig'_scheme ::
  "subst \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> YulIdentifier \<Rightarrow> ('g, 'v, 't, 'z) function_sig'_scheme \<Rightarrow> bool" where
"alpha_equiv_function_sig'_scheme fsubst n1 s1 n2 s2 =
  (case (f_sig_body s1, f_sig_body s2) of
        (YulBuiltin b1, YulBuiltin b2) \<Rightarrow> s1 = s2
        | (YulFunction sts1, YulFunction sts2) \<Rightarrow>
          alpha_equiv_statement' fsubst
              (YulFunctionDefinitionStatement (YulFunctionDefinition n1 (f_sig_arguments s1) (f_sig_returns s1) sts1))
              (YulFunctionDefinitionStatement (YulFunctionDefinition n2 (f_sig_arguments s2) (f_sig_returns s2) sts2))
        | (_, _) \<Rightarrow> False)"

definition alpha_equiv_fun ::
  "subst \<Rightarrow> (YulIdentifier * ('g, 'v, 't, 'z) function_sig_scheme) \<Rightarrow> (YulIdentifier * ('g, 'v, 't, 'z) function_sig_scheme) \<Rightarrow> bool"
  where
"alpha_equiv_fun fsubst fun1 fun2 =
  (case fun1 of (n1, s1) \<Rightarrow>
  (case fun2 of (n2, s2) \<Rightarrow>
  (list_all2 (alpha_equiv_name' fsubst) (f_sig_visible s1) (f_sig_visible s2) \<and>
   alpha_equiv_function_sig'_scheme fsubst n1 s1 n2 s2)))"

definition alpha_equiv_funs' ::
  "subst \<Rightarrow> ('g, 'v, 't, 'z) function_sig_scheme locals \<Rightarrow> ('g, 'v, 't, 'z) function_sig_scheme locals \<Rightarrow> bool"
  where
"alpha_equiv_funs' fsubst funs1 funs2 =
  list_all2 (alpha_equiv_fun fsubst) funs1 funs2"

fun alpha_equiv_stackEl' ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> ('g, 'v, 't) StackEl \<Rightarrow> bool" where
"alpha_equiv_stackEl' fsubst (EnterStatement s1) (EnterStatement s2) =
  alpha_equiv_statement' fsubst s1 s2"
| "alpha_equiv_stackEl' fsubst (ExitStatement s1 vs1 fs1) (ExitStatement s2 vs2 fs2) =
      (alpha_equiv_statement' fsubst s1 s2 \<and>
       alpha_equiv_locals' fsubst vs1 vs2 \<and>
       alpha_equiv_funs' fsubst fs1 fs2)"
| "alpha_equiv_stackEl' fsubst (Expression e1) (Expression e2) =
  alpha_equiv_expr' fsubst e1 e2"
| "alpha_equiv_stackEl' fsubst (EnterFunctionCall n1 f1) (EnterFunctionCall n2 f2) = 
   (alpha_equiv_function_sig'_scheme fsubst n1 f1 n2 f2)"
| "alpha_equiv_stackEl' fsubst (ExitFunctionCall n1 vals1 locals1 fs1 f1)
                                      (ExitFunctionCall n2 vals2 locals2 fs2 f2) =
    (alpha_equiv_function_sig'_scheme fsubst n1 f1 n2 f2 \<and>
     alpha_equiv_locals' fsubst locals1 locals2 \<and>
     alpha_equiv_funs' fsubst fs1 fs2)"
| "alpha_equiv_stackEl' fsubst _ _ = False"

(* do we need a subst_updatex variant also? *)

(* TODO: perhaps there is an easier way to handle "jumping" to after the break.
 * e.g. we just run the "normal alpha equiv interpreter" a bunch of times.
 *)
(* do we need more error cases in this? *)
fun subst_update_cont_break ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow>
    (subst * ('g, 'v, 't) StackEl list * ('g, 'v, 't) StackEl list) option"
where
"subst_update_cont_break fsubst [] [] = None"
| "subst_update_cont_break fsubst
  (ExitStatement st1 vs1 fs1 # t1)
  (ExitStatement st2 vs2 fs2 # t2) =
  (case st1 of
    YulForLoop pre1 cond1 post1 body1 \<Rightarrow>
      (case st2 of
       YulForLoop pre2 cond2 post2 body2 \<Rightarrow>
        Some (fsubst, t1, t2)
       | _ \<Rightarrow> None)
    | YulBlock sts1 \<Rightarrow>
      (case st2 of
        YulBlock sts2 \<Rightarrow>
          (case fsubst of
            [] \<Rightarrow> None
            | fsubsth#fsubstt \<Rightarrow> subst_update_cont_break fsubstt t1 t2)
        | _ \<Rightarrow> None)
    | _ \<Rightarrow> 
      (if yul_statement_same_constructor st1 st2
       then subst_update_cont_break fsubst t1 t2
       else None))"
(* How to handle exitFunction here? *)
| "subst_update_cont_break fsubst ((ExitFunctionCall _ _ _ _ _)#t1) ((ExitFunctionCall _ _ _ _ _)#t2) = None"
| "subst_update_cont_break fsubst (h1#t1) (h2#t2) =
   (if stackEl_same_constructor_strong h1 h2 then
    subst_update_cont_break fsubst t1 t2
    else None)"
| "subst_update_cont_break _ _ _ = None"

lemma subst_update_cont_break_length :
  assumes "subst_update_cont_break subst l1 l2 = Some (subst', l1', l2')"
  shows "length l1' < length l1"
  using assms
proof(induction l1 arbitrary: subst l2 subst' l1' l2')
  case Nil
  then show ?case
    by(cases l2; auto)
next
  case Cons1 : (Cons l1h l1t)

  obtain l2h l2t where Cons2 : "l2 = l2h # l2t"
    using Cons1.prems
    by(cases l2; auto)

  show ?case
  proof(cases l1h)
    case (EnterStatement x1)
    then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
      by(cases l2h; auto split: if_split_asm)
  next
    case XS1 : (ExitStatement st1 vs1 fs1)

    show ?thesis
    proof(cases l2h)
      case (EnterStatement x1)
      then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
        by(cases l2h; auto split: if_split_asm)
    next
      case XS2 : (ExitStatement st2 vs2 fs2)

      show ?thesis
      proof(cases subst)
        case Nil
        then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2 XS1 XS2
          by(cases st1; cases st2; auto)
      next
        case (Cons substh substt)
        then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons1.IH[of substt l2t] Cons2 XS1 XS2
          by(cases st1; cases st2; auto)
      qed
    next
      case (EnterFunctionCall x31 x32)
      then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
        by(cases l2h; auto split: if_split_asm)
    next
      case (ExitFunctionCall x41 x42 x43 x44 x45)
      then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2 XS1
        by(cases l2h; auto split: if_split_asm)
    next
      case (Expression x5)
      then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
        by(cases l2h; auto split: if_split_asm)
    qed
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
      by(cases l2h; auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
      by(cases l2h; auto)
  next
    case (Expression x5)
    then show ?thesis using Cons1.prems Cons1.IH[of subst l2t] Cons2
      by(cases l2h; auto split: if_split_asm)
  qed
qed

(* TODO. We have updated this to check alpha equivalence when we break,
 * as well as alpha equivalence if we pretend break is a no-op *)
(*
function (sequential) alpha_equiv_stackEls' ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> bool" where
"alpha_equiv_stackEls' fsubst [] [] = True"
| "alpha_equiv_stackEls' fsubst (h1#t1) (h2#t2) =
   (case h1 of
    (ExitStatement YulBreak _ _) \<Rightarrow>
      (case h2 of
        (ExitStatement YulBreak _ _) \<Rightarrow>
          (case subst_update_cont_break fsubst t1 t2 of
            None \<Rightarrow> alpha_equiv_stackEls' fsubst t1 t2 \<comment> \<open>Changed - this used to be false\<close>
            | Some (fsubst', t1', t2') \<Rightarrow> 
              alpha_equiv_stackEls' fsubst t1 t2 \<and>
              alpha_equiv_stackEls' fsubst' t1' t2')
        | _ \<Rightarrow> False)
    | _ \<Rightarrow>
    (if stackEl_same_constructor_strong h1 h2 then
     (case subst_updatex fsubst h1 h2 of
      None \<Rightarrow> False
      | Some fsubst' \<Rightarrow>
      (alpha_equiv_stackEl' fsubst' h1 h2 \<and>
       alpha_equiv_stackEls' fsubst' t1 t2))
     else False))"
| "alpha_equiv_stackEls' fsubst _ _ = False"
           apply(pat_completeness)
           apply(auto)
  done
*)

(* TODO: one way to understand the problem is that we are giving the wrong result
 * in cases where the programs will crash on the next step 
 * eg. if we are about to exit a block but the fsubst context is nil.
 * do we say that the programs are equal under this context?*)
function (sequential) alpha_equiv_stackEls' ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> bool" where
"alpha_equiv_stackEls' fsubst [] [] = True"
| "alpha_equiv_stackEls' fsubst (h1#t1) (h2#t2) =
   (case h1 of
    (ExitStatement YulBreak _ _) \<Rightarrow>
      (case h2 of
        (ExitStatement YulBreak _ _) \<Rightarrow>
          (case subst_update_cont_break fsubst t1 t2 of
            None \<Rightarrow> alpha_equiv_stackEl' fsubst h1 h2 \<and>
                    alpha_equiv_stackEls' fsubst t1 t2
            | Some (fsubst', t1', t2') \<Rightarrow> 
              alpha_equiv_stackEl' fsubst h1 h2 \<and>
              alpha_equiv_stackEls' fsubst t1 t2 \<and>
              alpha_equiv_stackEls' fsubst' t1' t2')
        | _ \<Rightarrow> False)
    | _ \<Rightarrow>
    (if stackEl_same_constructor_strong h1 h2 then
     (case subst_updatex fsubst h1 h2 of
      None \<Rightarrow> True
      | Some fsubst' \<Rightarrow>
      (alpha_equiv_stackEl' fsubst' h1 h2 \<and>
       alpha_equiv_stackEls' fsubst' t1 t2))
     else False))"
| "alpha_equiv_stackEls' fsubst _ _ = False"
           apply(pat_completeness)
           apply(auto)
  done


termination
proof(relation "measure (\<lambda>(s, l1, l2) . length l1)"; auto)
  fix fsubst t1 t2 subst' t1' t2'
  assume H: "subst_update_cont_break fsubst t1 t2 = Some (subst', t1', t2')"
  show "length t1' < Suc (length t1)"
    using subst_update_cont_break_length[OF H]
    by auto
qed

(* used for splitting apart alpha_equiv_stackEls' *)
(*
fun alpha_equiv_stackEls'_newsubst ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> subst option" where
"alpha_equiv_stackEls'_newsubst fsubst [] [] = Some fsubst"
| "alpha_equiv_stackEls'_newsubst fsubst (h1#t1) (h2#t2) =
   (case subst_updatex fsubst h1 h2 of
    None \<Rightarrow> None
    | Some fsubst' \<Rightarrow>
      alpha_equiv_stackEls'_newsubst fsubst' t1 t2)"
| "alpha_equiv_stackEls'_newsubst fsubst _ _ = None"
*)

(* if compared stackEls' are equal so far,
 * return the resultant substitution.
 *)
function (sequential) alpha_equiv_stackEls'_newsubst ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> subst option" where
"alpha_equiv_stackEls'_newsubst fsubst [] [] = Some fsubst"
| "alpha_equiv_stackEls'_newsubst fsubst (h1#t1) (h2#t2) =
  (case h1 of
    (ExitStatement YulBreak _ _) \<Rightarrow>
      (case h2 of
        (ExitStatement YulBreak  _ _) \<Rightarrow>
          (case subst_update_cont_break fsubst t1 t2 of
            None \<Rightarrow> None
            | Some (fsubst', t1', t2') \<Rightarrow> 
              alpha_equiv_stackEls'_newsubst fsubst' t1' t2')
        | _ \<Rightarrow> None)
      | _ \<Rightarrow>
      (case subst_updatex fsubst h1 h2 of
          None \<Rightarrow> None
          | Some fsubst' \<Rightarrow>
            alpha_equiv_stackEls'_newsubst fsubst' t1 t2))"
| "alpha_equiv_stackEls'_newsubst fsubst _ _ = None"
           apply(pat_completeness)
           apply(auto)
  done


termination
proof(relation "measure (\<lambda>(s, l1, l2) . length l1)"; auto)
  fix fsubst t1 t2 subst' t1' t2'
  assume H: "subst_update_cont_break fsubst t1 t2 = Some (subst', t1', t2')"
  show "length t1' < Suc (length t1)"
    using subst_update_cont_break_length[OF H]
    by auto
qed

lemma subst_update_cont_break_tail :
  assumes "subst_update_cont_break fsubst pre1 pre2 = Some (fsubst', pre1', pre2')"
  shows "subst_update_cont_break fsubst (pre1 @ post1) (pre2 @ post2) = Some (fsubst', pre1' @ post1, pre2' @ post2)"
  using assms
proof(induction pre1 arbitrary: fsubst pre2 fsubst' pre1' pre2' post1 post2)
  case Nil
  then show ?case 
    by(cases pre2; auto)
next
  case Cons1 : (Cons pre1h pre1t)

  then obtain pre2h pre2t where Cons2 : "pre2 = pre2h # pre2t"
    by(cases pre2; auto)

  show ?case
  proof (cases pre1h)
    case (EnterStatement x1)
    then show ?thesis 
      using Cons1 Cons2
        by(cases pre2h; auto split: if_split_asm)
  next
    case XS1 : (ExitStatement st1 vs1 fs1)

    then obtain st2 vs2 fs2 where
      XS2 : "pre2h = ExitStatement st2 vs2 fs2"
      using Cons1 Cons2 XS1
      by(cases pre2h; auto)

    show ?thesis 
      using Cons1 Cons2 XS1 XS2
      apply(cases st1; auto split: if_split_asm)
      apply(cases st2; auto split: if_split_asm)
      apply(cases st2; auto split: if_split_asm)
      apply(cases fsubst; auto)
      done
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto)
  next
    case (Expression x5)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto split: if_split_asm)
  qed

qed

lemma newsubst_subst_update_cont_break_tail :
  assumes "alpha_equiv_stackEls'_newsubst fsubst pre1 pre2 = Some fsubst'"
  assumes "alpha_equiv_stackEls'_newsubst fsubst' post1 post2 = Some fsubst''"
  shows "alpha_equiv_stackEls'_newsubst fsubst (pre1 @ post1) (pre2 @ post2) = Some fsubst''"
  sorry


(*
lemma alpha_equiv_stackEls'_newsubst_comp :
  assumes "alpha_equiv_stackEls'_newsubst fsubst pre1 pre2 = Some fsubst'"
  assumes "alpha_equiv_stackEls'_newsubst fsubst' post1 post2 = Some fsubst''"
  shows "alpha_equiv_stackEls'_newsubst fsubst (pre1 @ post1) (pre2 @ post2) = Some fsubst''"
  sorry
*)
(*
lemma subst_update_cont_break_tail_None :
  assumes "subst_update_cont_break fsubst (pre1h # pre1t) (pre2h # pre2t) = None"
  shows "subst_update_cont_break fsubst (pre1h # pre1t @ post1) (pre2h # pre2t @ post2) = None"
  using assms
proof(induction pre1t arbitrary: fsubst pre1h pre2h pre2t post1 post2)
  case Nil1 : Nil

  show ?case
  proof(cases pre2t)
    case Nil2 : Nil

    show ?thesis
    proof(cases pre1h)
      case (EnterStatement x1)

      then show ?thesis
        using Nil1 Nil2
        apply(cases pre2h; auto)

      then show ?thesis sorry
    next
      case (ExitStatement x21 x22 x23)
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

    then show ?thesis 
      apply(auto)
  next
    case (Cons a list)
    then show ?thesis sorry
  qed

  then show ?case 
    apply(auto)
next
  case Cons1 : (Cons pre1h pre1t)

  show ?case
  proof(cases pre2)
    case Nil2 : Nil
    then show ?thesis using Cons1
      apply(auto)
  next
    case Cons2 : (Cons a list)
    then show ?thesis sorry
  qed

  then obtain pre2h pre2t where Cons2 : "pre2 = pre2h # pre2t"
    by(cases pre2; auto)

  show ?case
  proof (cases pre1h)
    case (EnterStatement x1)
    then show ?thesis 
      using Cons1 Cons2
        by(cases pre2h; auto split: if_split_asm)
  next
    case XS1 : (ExitStatement st1 vs1 fs1)

    then obtain st2 vs2 fs2 where
      XS2 : "pre2h = ExitStatement st2 vs2 fs2"
      using Cons1 Cons2 XS1
      by(cases pre2h; auto)


    show ?thesis 
      using Cons1 Cons2 XS1 XS2
      apply(cases st1; auto split: if_split_asm)
      apply(cases st2; auto split: if_split_asm)
      apply(cases st2; auto split: if_split_asm)
      apply(cases fsubst; auto)
      done
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto)
  next
    case (Expression x5)
    then show ?thesis 
      using Cons1 Cons2
      by(cases pre2h; auto split: if_split_asm)
  qed

qed
*)


(* TODO *)
(* this may no longer hold in the same way, since we may "skip"
 * some stack elements when evaluating break
 * generalize by making pre1 and pre2 itself have a prefix?

 * Figured it out. need a version of newsubst that can reflect the post-break
 * version of the rename context.
 *)
(*
lemma alpha_equiv_stackEls'_split :
  assumes "alpha_equiv_stackEls' fsubst pre1 pre2"
  assumes "alpha_equiv_stackEls'_newsubst fsubst pre1 pre2 = Some fsubst'"
  assumes "alpha_equiv_stackEls' fsubst' post1 post2"
  shows "alpha_equiv_stackEls' fsubst (pre1 @ post1) (pre2 @ post2)"
using assms
*)

(*
lemma alpha_equiv_stackEls'_split_gen :
  assumes "alpha_equiv_stackEls' fsubst (pre1 @ mid1) (pre2 @ mid2)"
  assumes "alpha_equiv_stackEls'_newsubst fsubst (pre1 @ mid1) (pre2 @! = Some fsubst'"
  assumes "alpha_equiv_stackEls' fsubst' post1 post2"
  shows "alpha_equiv_stackEls' fsubst (pre1 @ post1) (pre2 @ post2)"
using assms
*)

(*
lemma subst_update_cont_break_split :
  assumes "subst_update_cont_break fsubst l1 l2 = Some (fsubst', l1', l2')"
  shows "\<exists> fsubst_pre l1_pre l2_pre .
    fsubst = fsubst_pre @ fsubst' \<and>
    l1 = l_pre @ ExitStatement (YulForLoop 
*)

(* need a more general version of this? *)
(*
lemma alpha_equiv_stackEls'_split :
  assumes "alpha_equiv_stackEls' fsubst pre1 pre2"
  assumes "alpha_equiv_stackEls'_newsubst fsubst pre1 pre2 = Some fsubst'"
  assumes "alpha_equiv_stackEls' fsubst' post1 post2"
  shows "alpha_equiv_stackEls' fsubst (pre1 @ post1) (pre2 @ post2)"
using assms
proof(induction pre1 arbitrary: fsubst pre2 fsubst' post1 post2)
  case Nil1 : Nil

  have Nil2 : "pre2 = []"
    using Nil1
    by(cases pre2; auto)

  show ?case
    using Nil1 Nil2
    by(auto)
next
  case Cons1 : (Cons preh1 pret1)

  obtain preh2 pret2 where Cons2 : "pre2 = preh2 # pret2"
    using Cons1.prems
    by(cases pre2; auto)

  show ?case
  proof(cases preh1)
    case ES1 : (EnterStatement s1)

    obtain s2 where ES2 : "preh2 = (EnterStatement s2)"
      using ES1 Cons1.prems Cons2
      by (cases preh2; auto)

    then show ?thesis
      using Cons1 Cons2 ES1 ES2
      by(cases s1; auto split: if_split_asm)
  next
    case XS1 : (ExitStatement s1 locals1 funcs1)

    then obtain s2 locals2 funcs2 where XS2 :
      "preh2 = ExitStatement s2 locals2 funcs2"
      using Cons1.prems Cons2
      by(cases preh2; cases s1; auto)

    show ?thesis
    proof(cases s1)
      case (YulFunctionCallStatement x1)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
      case (YulVariableDeclarationStatement x3)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto split: option.splits)
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
      case (YulIf x51 x52)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
      case (YulSwitch x61 x62)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
    case (YulForLoop x71 x72 x73 x74)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases s2; auto)
    next
      case B1 : YulBreak

      have B2 : "s2 = YulBreak"
        using Cons1 Cons2 XS1 XS2 B1
        by(cases s2; auto)

      obtain pret1'' pret2'' fsubst'' where Upd_Break :
        "subst_update_cont_break fsubst pret1 pret2 = Some (fsubst'', pret1'', pret2'')"
        using Cons1 Cons2 XS1 XS2 B1 B2
        by(cases "subst_update_cont_break fsubst pret1 pret2"; auto)

      show ?thesis
        using Cons1.prems Cons1.IH[of fsubst pret2 _ post1 post2] Cons2 XS1 XS2 B1 B2 Upd_Break subst_update_cont_break_tail[OF Upd_Break, of post1 post2]
        apply(auto)

      proof(cases "subst_update_cont_break fsubst2 pret1 pret2")
        case None1 : None

        show ?thesis
          using Cons1 Cons2 XS1 XS2 Fsubst2 B1 B2 None1
          by(auto)
      next
        case Some1 : (Some r1)
        then obtain fsubst_out_1 pret1_out_1 pret2_out_1 where R1 :
          "r1 = (fsubst_out_1, pret1_out_1, pret2_out_1)"
          by (cases r1; auto)

(* relate subst_update_cont_break to alpha_equiv_stackEls'_newsubst? *)

        then show ?thesis
          using Cons1 Cons2 XS1 XS2 Fsubst2 B1 B2 Some1
          using subst_update_cont_break_tail[OF Some1[unfolded R1]]
          apply(auto)

(*
        proof(cases "subst_update_cont_break fsubst2 (pret1 @ post1) (pret2 @ post2)")
          case None2 : None

          show ?thesis
            using Cons1 Cons2 XS1 XS2 Fsubst2 B1 B2 None1 None2
            by(auto)
        next
          case Some2 : (Some r2)

          then obtain fsubst_out_2 pret1_out_2 pret2_out_2 where R2 :
            "r2 = (fsubst_out_2, pret1_out_2, pret2_out_2)"
            by (cases r2; auto)

          then show ?thesis
            using Cons1 Cons2 XS1 XS2 Fsubst2 B1 B2 None1 Some2
            apply(auto)
      next
        case (Some a)
        then show ?thesis sorry
      qed

        using Cons1 Cons2 XS1 XS2 Fsubst2 B1 B2
        apply( auto)
*)
      obtain pret1'' pret2'' fsubst'' where Upd_Break :
        "subst_update_cont_break fsubst pret1 pret2 = Some (fsubst'', pret1'', pret2'')"
        using Cons1 Cons2 XS1 XS2 B1 B2
        by(cases "subst_update_cont_break fsubst pret1 pret2"; auto)

(* idea here.
 * need to show that last element of prefix is loop exit.
 * we probably need another lemma as well
 *)
      have Break_Tail :
        "subst_update_cont_break fsubst2 (pret1 @ post1) (pret2 @ post2) = 
          Some (fsubst'', pret1'' @ post1, pret2'' @ post2)"
        using subst_update_cont_break_tail[OF Upd_Break, of "post1" "post2"]
        by(auto)

      show ?thesis
        using Cons1.prems Cons1.IH [of fsubst2 pret2 fsubst' post1 post2] Cons2 XS1 XS2 Fsubst2 B1 B2 Upd_Break Break_Tail
        apply(auto)
        apply(rule_tac Cons1.IH)

    next
      case YulContinue
      then show ?thesis
        using Cons1 Cons2 XS1 XS2 Fsubst2
        by(cases s2; auto)
    next
      case YulLeave
      then show ?thesis
        using Cons1 Cons2 XS1 XS2 Fsubst2
        by(cases s2; auto)
    next
      case (YulBlock x11)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2 Fsubst2
        by(cases s2; auto)
    qed
(*
    obtain fsubst3 pret1' pret2' where Fsubst3 :
      "subst_update_cont_break fsubst2 pret1 pret2 = Some (fsubst3, pret1', pret2')"
      using Cons1 Cons2 XS1 XS2 Fsubst2
      apply(cases s1; auto)
      apply(cases s2; auto)
*)
    show ?thesis using Cons1 Cons2 XS1 XS2 Fsubst2
      apply(cases s1; auto)
      apply(cases s2; auto)
      apply(cases "subst_update_cont_break fsubst2 pret1 pret2"; auto)
  next
    case EF1 : (EnterFunctionCall name1 sig1)

    then obtain name2 sig2 where EF2:
      "preh2 = EnterFunctionCall name2 sig2"
      using EF1 Cons1.prems Cons2
      by(cases preh2; auto)

    show ?thesis
      using Cons1 Cons2 EF1 EF2
      by(auto)
  next
    case XF1 : (ExitFunctionCall name1 vals1 locals1 funcs1 f1)
    then obtain name2 vals2 locals2 funcs2 f2 where XF2 :
      "preh2 = ExitFunctionCall name2 vals2 locals2 funcs2 f2"
      using XF1 Cons1.prems Cons2
      by(cases preh2; auto)

    obtain fsubst' where Fsubst' :
      "subst_updatex_exit_fun_call fsubst = Some fsubst'"
      using Cons1 Cons2 XF1 XF2
      by(cases "subst_updatex_exit_fun_call fsubst"; auto)

    show ?thesis using Cons1 Cons2 XF1 XF2 Fsubst'
      by(auto)
  next
    case Exp1 : (Expression e1)

    obtain e2 where Exp2 : "preh2 = (Expression e2)"
      using Exp1 Cons1.prems Cons2
      by (cases preh2; auto)

    show ?thesis
      using Cons1 Cons2 Exp1 Exp2
      by(cases e1; auto)
  qed
qed
*)

(*
abbreviation (input) alpha_equiv_stackEls' ::
  "subst \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> ('g, 'v, 't) StackEl list \<Rightarrow> bool" where
"alpha_equiv_stackEls' fsubst l1 l2 \<equiv>
  list_all2 (alpha_equiv_stackEl' fsubst) l1 l2"
*)

definition alpha_equiv_results' ::
  "subst \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   ('g, 'v, 't) YulInput \<Rightarrow>
   bool" where
"alpha_equiv_results' fsubst r1 r2 =
  (global r1 = global r2 \<and>
   vals r1 = vals r2 \<and>
   locals r1 = locals r2 \<and>
   alpha_equiv_funs' fsubst (funs r1) (funs r2) \<and>
   (alpha_equiv_stackEls' fsubst
              (cont r1)
              (cont r2)))"

lemma alpha_equiv_locals'_length :
  assumes "alpha_equiv_locals' fsubst l1 l2"
  shows "length l1 = length l2"
  using assms
proof(induction l1 arbitrary: fsubst l2)
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
    then show ?thesis using Cons.prems Cons.IH[of fsubst l2t]
      by(cases l1h; cases l2h; auto simp add: alpha_equiv_locals'_def)
  qed
qed
(*
lemma alpha_equiv_fun_trunc :
  assumes H: "alpha_equiv_fun fsubst fun1 fun2"
  shows "alpha_equiv_fun fsubst
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
*)
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
next
qed


lemma gatherYulFunctions'_notin :
  assumes "gatherYulFunctions' (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1)) st1 =
    Inl gather1"
  assumes "map_of gather1 n1 = None"
  shows "map_of (funs r1) n1 = None"
  using assms
proof(induction st1 arbitrary: n1 r1 gather1)
  case Nil

  have Impl : "\<And> b . (n1, b) \<in> set (funs r1) \<Longrightarrow> n1 \<in> fst ` (\<lambda>x. case x of (n, fs) \<Rightarrow> (n, function_sig'.truncate fs)) ` set (funs r1)"
  proof-
    fix b
    assume H: "(n1, b) \<in> set (funs r1)"
    show "n1 \<in> fst ` (\<lambda>x. case x of (n, fs) \<Rightarrow> (n, function_sig'.truncate fs)) ` set (funs r1)"
      using imageI[OF imageI[OF H, of "(\<lambda>x. case x of (n, fs) \<Rightarrow> (n, function_sig'.truncate fs))"], of "fst"]
    by(auto)
  qed

  then show ?case using Nil
    unfolding map_of_eq_None_iff
    by(auto)
next
  case (Cons sth st1)

  show ?case 
  proof(cases sth)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons
      by(auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons
      by(auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons
      by(auto)
  next
    case Fdef : (YulFunctionDefinitionStatement f)

    obtain n args rets body where 
      F: "f = YulFunctionDefinition n args rets body"
      by(cases f; auto)

    obtain gather1' where Gather1' :
      "gatherYulFunctions' (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1)) st1 = Inl gather1'"
      using Cons Fdef F
      by(cases "gatherYulFunctions' (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1)) st1"; auto)

    show ?thesis
    proof(cases "map_of gather1' n1")
      case None

      have Notin : "n1 \<notin> fst ` set gather1'"
        using None unfolding map_of_eq_None_iff
        by(auto)

      have None' : "\<And> sig' . (n1, sig') \<notin> set gather1'"
      proof
        fix sig'
        assume Bad : "(n1, sig') \<in> set gather1'"
        show False
          using Notin imageI[OF Bad, of "fst"]
          by auto
      qed

      then show ?thesis using Cons.prems Fdef F Gather1' None
        using Cons.IH[OF Gather1']
        by(auto)
    next
      case (Some sig1)
      show ?thesis using Cons.prems Fdef F Gather1' Some
        using Cons.IH[OF Gather1']
        by(cases "map_of gather1' n"; auto split:if_split_asm)
    qed
  next
    case (YulIf x51 x52)
    then show ?thesis using Cons
      by(auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons
      by(auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons
      by(auto)
  next
    case YulBreak
    then show ?thesis using Cons
      by(auto)
  next
    case YulContinue
    then show ?thesis using Cons
      by(auto)
  next
    case YulLeave
    then show ?thesis using Cons
      by(auto)
  next
    case (YulBlock x11)
    then show ?thesis using Cons
      by(auto)
  qed
qed

lemma check_decls_fun_decls :
  assumes H: "alpha_equiv_check_decls st1 st2 = Some funs_t"
  shows "zip (get_fun_decls st1) (get_fun_decls st2) = funs_t"
  using assms
proof(induction st1 arbitrary: st2 funs_t)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons st1h st1t)

  then obtain st2h st2t where Cons2 : "st2 = st2h#st2t"
    by(cases st2; auto)

  show ?case
  proof(cases st1h)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case FD1: (YulFunctionDefinitionStatement f1)

    obtain f2 where FD2 : "st2h = YulFunctionDefinitionStatement f2"
      using FD1 Cons1 Cons2
      by(cases st2h; auto)

    obtain n1 args1 rets1 body1 where F1 : "f1 = YulFunctionDefinition n1 args1 rets1 body1"
      by(cases f1; auto)

    obtain n2 args2 rets2 body2 where F2 : "f2 = YulFunctionDefinition n2 args2 rets2 body2"
      by(cases f2; auto)

    then show ?thesis using Cons1 Cons2 FD1 FD2 F1 F2
      by(cases "alpha_equiv_check_decls st1t st2t"; auto split:option.split_asm)
  next
    case (YulIf x51 x52)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case YulBreak
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case YulContinue
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
    case YulLeave
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  next
  case (YulBlock x11)
    then show ?thesis using Cons1 Cons2
      by(cases st2h; auto)
  qed
qed


lemma alpha_equiv_name_gather_functions :
assumes Hg1 : "gatherYulFunctions'
  (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1)) sts1 = Inl fs1"
assumes Hg2 : "gatherYulFunctions'
   (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2)) sts2 = Inl fs2"
assumes Heqv :  "list_all2 (alpha_equiv_statement' ((pre @ funcs') # fsubst)) sts1 sts2"
assumes Hcheck : "alpha_equiv_check_decls sts1 sts2 = Some (funcs')"
assumes Hpre1 : "distinct (map fst (pre @ funcs'))"
assumes Hpre2 : "distinct (map snd (pre @ funcs'))"
assumes Hfsubst : "list_all2 (alpha_equiv_fun fsubst) (funs r1) (funs r2) "
shows "list_all2
         (alpha_equiv_name'
           ((pre @
             zip (get_fun_decls sts1) (get_fun_decls sts2)) #
            fsubst))
         (map fst gather1) (map fst gather2)"
  using assms
proof(induction sts1 arbitrary: sts2 r1 fs1 r2 fs2 funcs' fsubst pre)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons sth1 stt1)

  obtain sth2 stt2 where Cons2 : "sts2 = sth2 # stt2"
    using Cons1.prems
    by(cases sts2; auto)

  then show ?case
  proof(cases sth1)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case X4 : (YulFunctionDefinitionStatement x4)

    then obtain y4 where Y4 : "sth2 = YulFunctionDefinitionStatement y4"
      using Cons1.prems Cons2
      by(cases sth2; auto)

    obtain n1 args1 rets1 body1 where F1 :
      "x4 = YulFunctionDefinition n1 args1 rets1 body1"
      by(cases x4; auto)

    obtain n2 args2 rets2 body2 where F2 :
      "y4 = YulFunctionDefinition n2 args2 rets2 body2"
      by(cases y4; auto)

    obtain funs_t where Funs_t :
      "alpha_equiv_check_decls stt1 stt2 = Some funs_t"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls stt1 stt2"; auto)

    obtain funs_body where Funs_body :
      "alpha_equiv_check_decls body1 body2 = Some funs_body"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls body1 body2"; auto)

    obtain gather1 where Gather1 :
      "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1))
              stt1 = Inl gather1"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Funs_body
      by(cases "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1))
              stt1"; auto)

    obtain gather2 where Gather2:
      "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2))
              stt2 = Inl gather2"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Funs_body
      by(cases "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2))
              stt2"; auto)

    have Gather1_None :
      "map_of gather1 n1 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2
      by(cases "map_of gather1 n1"; auto)

    have Gather2_None :
      "map_of gather2 n2 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2
      by(cases "map_of gather2 n2"; auto)

    have Funs1_None : "map_of (funs r1) n1 = None"
      using gatherYulFunctions'_notin[OF Gather1 Gather1_None]
      by auto

    have Funs2_None : "map_of (funs r2) n2 = None"
      using gatherYulFunctions'_notin[OF Gather2 Gather2_None]
      by auto

    have Noshadow : "map_of (zip (get_fun_decls stt1) (get_fun_decls stt2)) n1 = None"
      using check_decls_fun_decls[OF Funs_t] Cons1.prems Cons2 X4 Y4 F1 F2 
        Funs_t Funs_body Gather1 Gather2
        Gather1_None Gather2_None Funs1_None Funs2_None
      by(cases "map_of (zip (get_fun_decls stt1) (get_fun_decls stt2)) n1"; auto)

    have Func_eq : "funcs' = (n1, n2)#funs_t"
      using check_decls_fun_decls[OF Funs_t] Cons1.prems Cons2 X4 Y4 F1 F2 
        Funs_t Funs_body Gather1 Gather2
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
      by(auto split: option.split_asm)

    have Noshadow' : "map_of funs_t n1 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
      by(cases "map_of funs_t n1"; auto)

    have Noshadow_flip2 : "map_of (subst'_flip funs_t) n2 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Noshadow'
      by (cases "map_of (subst'_flip funs_t) n1"; auto)

    have Eqv' : "list_all2 (alpha_equiv_statement' (((pre @ [(n1, n2)]) @ funs_t) # fsubst)) stt1 stt2"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow' Noshadow_flip2
      by(auto)

    have Distinct1 : "distinct (map fst ((pre @ [(n1, n2)]) @ funs_t))"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
        Func_eq
      by(auto)

    have Distinct2 : "distinct (map snd ((pre @ [(n1, n2)]) @ funs_t))"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
        Func_eq
      by(auto)

    show ?thesis
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
      using Cons1.IH[OF Gather1 Gather2 Eqv' Funs_t Distinct1 Distinct2]
      using check_decls_fun_decls[OF Funs_t] 
      by(auto)
  next
  case (YulIf x51 x52)
    then show ?thesis using Cons1 Cons2
    by(cases sth2;auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case YulBreak
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case YulContinue
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case YulLeave
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulBlock x11)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  qed
qed

lemma subst_flip_flip :
  shows "subst_flip (subst_flip s) = s"
proof(induction s)
  case Nil
  then show ?case 
    by(auto simp add: subst_flip_def)
next
  case (Cons a s)

  have Is_id :
    "(\<lambda>(x, y). (y, x)) \<circ> (\<lambda>(x, y). (y, x)) = id"
    by(auto)

  show ?case using Cons
    by(auto simp add: subst_flip_def Is_id)
qed

(*
lemma subst_lookup_flip0 :
  assumes "subst_lookup (sh#st) x = Some y"
  shows "subst_lookup (subst_flip (sh#st)) y = Some x"
  using assms
proof(induction sh)
*)
(*
lemma subst_lookup_flip :
  assumes "distinct (map fst s)"
  assumes "distinct (map snd s)"
  assumes "subst_lookup s x = Some y"
  shows "subst_lookup (subst_flip s) y = Some x"
  using assms
proof(induction s arbitrary: x y)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons a s)
  then show ?case 
    apply(auto split: option.splits)
qed
*)
(*
lemma alpha_equiv_name_drop :
  assumes "alpha_equiv_name' ((pre1) # post2) x y"
  assumes "distinct (map fst (pre0 @ pre1))"
  assumes "distinct (map snd (pre0 @ pre1))"
  assumes "x \<notin> set (map fst pre0)"
  assumes "y \<notin> set (map snd pre0)"
  shows "(alpha_equiv_name' ((pre0 @ pre1) # post2)) x y"
  using assms
proof(induction pre1 arbitrary: x y )
  case Nil
  then show ?case
    apply(auto simp add: alpha_equiv_name'_def subst_flip_def)
next
  case (Cons p1h p1t)
(*
  have Conc1 : "alpha_equiv_name' ((pre0 @ p1h # p1t @ post1) # post2) (fst p1h)
     (snd p1h)"
    using Cons.prems
    apply(auto simp add: alpha_equiv_name'_def subst_flip_def)
*)
  then show ?case 
    apply(auto)
qed
*)
(*
  assumes "list_all2 (alpha_equiv_name' ((pre @ post1) # post2))
     (map fst pre) (map snd pre)"
  assumes "ph1 \<notin> set (map fst pre)"
  assumes "ph2 \<notin> set (map snd pre)"
  shows "list_all2 (alpha_equiv_name' (((ph1, ph2)#pre @ post1) # post2))
     (map fst pre) (map snd pre)"
  using assms
proof(induction pre arbitrary: ph1 ph2 post1 post2)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons ph pt)

  have Conc1 : "alpha_equiv_name' (((ph1, ph2) # ph # pt @ post1) # post2) (fst ph) (snd ph)"
    using Cons.prems
    by(cases ph; auto simp add: alpha_equiv_name'_def subst_flip_def)

  have Conc2 : "list_all2
     (alpha_equiv_name' (((ph1, ph2) # ph # pt @ post1) # post2))
     (map fst pt) (map snd pt)"
    using Cons

  show ?case using Cons
    apply(auto)
qed
*)

lemma alpha_equiv_name_after :
  fixes pre :: "(String.literal * String.literal) list"
  assumes Valid1 : "distinct (map fst (pre @ [xy]))"
  assumes Valid2 : "distinct (map snd (pre @ [xy]))"
  shows "alpha_equiv_name'
        ((pre @ xy # post1) # post2) (fst xy) (snd xy)"
  using assms
proof(induction pre arbitrary: post1 post2 xy)
  case Nil
  then show ?case 
    by(cases xy; auto simp add: alpha_equiv_name'_def subst_flip_def)
next
  case (Cons ph pt)

  obtain ph1 ph2 where PH : "ph = (ph1, ph2)"
    by(cases ph; auto)

  obtain x y where XY : "xy = (x, y)"
    by(cases xy; auto)

  have Distinct1 : "distinct (map fst (pt @ [xy]))"
    using Cons.prems by auto

  have Distinct2 : "distinct (map snd (pt @ [xy]))"
    using Cons.prems by auto

  show ?case using Cons.prems XY PH
      Cons.IH[OF Distinct1 Distinct2, of post1 post2]
    by(auto simp add: alpha_equiv_name'_def subst_flip_def)
qed

lemma alpha_equiv_name_prefix :
  assumes Valid1 : "distinct (map fst pre)"
  assumes Valid2 : "distinct (map snd pre)"
  shows "list_all2
     (alpha_equiv_name'
       ((pre @ post1) # post2))
       (map fst pre) (map snd pre)"
  using assms
proof(induction pre arbitrary: post1 post2)
  case Nil
  then show ?case by auto
next
  case (Cons ph pt)

  obtain ph1 ph2 where Ph : "ph = (ph1, ph2)"
    by(cases ph; auto)

  have Conc1 : "alpha_equiv_name' ((ph # pt @ post1) # post2) (fst ph) (snd ph)"
    using Ph
    by(auto simp add: alpha_equiv_name'_def subst_flip_def)

  have Conc2 : "list_all2 (alpha_equiv_name' ((ph # pt @ post1) # post2))
     (map fst pt) (map snd pt)"
  proof(rule list_all2_all_nthI)
    show "length (map fst pt) = length (map snd pt)"
      by auto
  next
    fix n
    assume N: "n < length (map fst pt)"

    then have N' : "n < length (map snd pt)"
      by auto

    have Noteq1 : "map fst pt ! n \<noteq> ph1"
    proof
      assume Contra : "map fst pt ! n = ph1"

      then have Contra' : "ph1 \<in> set (map fst pt)"
        using nth_mem[OF N]
        by auto

      then show False
        using Ph Cons.prems
        by(auto)
    qed

    have Noteq2 : "map snd pt ! n \<noteq> ph2"
    proof
      assume Contra : "map snd pt ! n = ph2"

      then have Contra' : "ph2 \<in> set (map snd pt)"
        using nth_mem[OF N']
        by auto

      then show False
        using Ph Cons.prems
        by(auto)
    qed


    have Ind : "list_all2
     (alpha_equiv_name' ((pt @ post1) # post2))
     (map fst pt) (map snd pt)"
      using Cons.IH Cons.prems
      by auto

    have Ind_n :
      "alpha_equiv_name' ((pt @ post1) # post2)
         (map fst pt ! n) (map snd pt ! n)"
      using list_all2_nthD[OF Ind N]
      by auto

    show "alpha_equiv_name' ((ph # pt @ post1) # post2)
          (map fst pt ! n) (map snd pt ! n)"
      using Ph Cons.prems Noteq1 Noteq2 Ind_n
      by(simp add: alpha_equiv_name'_def subst_flip_def)
  qed

  show ?case
    using Conc1 Conc2
    by auto
qed

(* list_all2 alpha_equiv_funs
 * as another premise?
 * (
 *)
lemma alpha_equiv_gather_functions :
assumes Hg1 : "gatherYulFunctions'
  (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1)) sts1 = Inl fs1"
assumes Hg2 : "gatherYulFunctions'
   (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2)) sts2 = Inl fs2"
assumes Heqv :  "list_all2 (alpha_equiv_statement' ((pre @ funcs') # fsubst)) sts1 sts2"
assumes Hcheck : "alpha_equiv_check_decls sts1 sts2 = Some (funcs')"
assumes Hpre1 : "distinct (map fst (pre @ funcs'))"
assumes Hpre2 : "distinct (map snd (pre @ funcs'))"
assumes Hfsubst : "list_all2 (alpha_equiv_fun fsubst) (funs r1) (funs r2) "
shows "list_all2 (alpha_equiv_fun ((pre @ zip (get_fun_decls sts1) (get_fun_decls sts2)) # fsubst))
     (combine_keep (funs r1)
       (map (\<lambda>(n, fs). (n, function_sig'.extend fs \<lparr>f_sig_visible = map fst pre @ map fst fs1\<rparr>)) fs1))
     (combine_keep (funs r2)
       (map (\<lambda>(n, fs). (n, function_sig'.extend fs \<lparr>f_sig_visible = map snd pre @ map fst fs2\<rparr>)) fs2))"
  using assms
proof(induction sts1 arbitrary: sts2 r1 fs1 r2 fs2 funcs' fsubst pre)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons sth1 stt1)

  obtain sth2 stt2 where Cons2 : "sts2 = sth2 # stt2"
    using Cons1.prems
    by(cases sts2; auto)

  then show ?case
  proof(cases sth1)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons1 Cons2
      by(cases sth2;auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case X4 : (YulFunctionDefinitionStatement x4)

    then obtain y4 where Y4 : "sth2 = YulFunctionDefinitionStatement y4"
      using Cons1.prems Cons2
      by(cases sth2; auto)

    obtain n1 args1 rets1 body1 where F1 :
      "x4 = YulFunctionDefinition n1 args1 rets1 body1"
      by(cases x4; auto)

    obtain n2 args2 rets2 body2 where F2 :
      "y4 = YulFunctionDefinition n2 args2 rets2 body2"
      by(cases y4; auto)

    obtain funs_t where Funs_t :
      "alpha_equiv_check_decls stt1 stt2 = Some funs_t"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls stt1 stt2"; auto)

    obtain funs_body where Funs_body :
      "alpha_equiv_check_decls body1 body2 = Some funs_body"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls body1 body2"; auto)

    obtain gather1 where Gather1 :
      "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1))
              stt1 = Inl gather1"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Funs_body
      by(cases "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r1))
              stt1"; auto)

    obtain gather2 where Gather2:
      "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2))
              stt2 = Inl gather2"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Funs_body
      by(cases "gatherYulFunctions'
              (map (\<lambda>(n, fs). (n, function_sig'.truncate fs)) (funs r2))
              stt2"; auto)

    have Gather1_None :
      "map_of gather1 n1 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2
      by(cases "map_of gather1 n1"; auto)

    have Gather2_None :
      "map_of gather2 n2 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2
      by(cases "map_of gather2 n2"; auto)

    have Funs1_None : "map_of (funs r1) n1 = None"
      using gatherYulFunctions'_notin[OF Gather1 Gather1_None]
      by auto

    have Funs2_None : "map_of (funs r2) n2 = None"
      using gatherYulFunctions'_notin[OF Gather2 Gather2_None]
      by auto

    have Noshadow : "map_of (zip (get_fun_decls stt1) (get_fun_decls stt2)) n1 = None"
      using check_decls_fun_decls[OF Funs_t] Cons1.prems Cons2 X4 Y4 F1 F2 
        Funs_t Funs_body Gather1 Gather2
        Gather1_None Gather2_None Funs1_None Funs2_None
      by(cases "map_of (zip (get_fun_decls stt1) (get_fun_decls stt2)) n1"; auto)

    have Noshadow' : "map_of funs_t n1 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
      by(cases "map_of funs_t n1"; auto)

    have Noshadow_flip2 : "map_of (subst'_flip funs_t) n2 = None"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Noshadow'
      by(auto)

    have Func_eq : "funcs' = (n1, n2)#funs_t"
      using check_decls_fun_decls[OF Funs_t] Cons1.prems Cons2 X4 Y4 F1 F2 
        Funs_t Funs_body Gather1 Gather2
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow Noshadow_flip2
      by(auto)

    have Eqv' : "list_all2 (alpha_equiv_statement' (((pre @ [(n1, n2)]) @ funs_t) # fsubst)) stt1 stt2"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow' Noshadow_flip2
      by(auto)

    have Distinct1 : "distinct (map fst ((pre @ [(n1, n2)]) @ funs_t))"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
        Func_eq
      by(auto)

    have Distinct2 : "distinct (map snd ((pre @ [(n1, n2)]) @ funs_t))"
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow
        Func_eq
      by(auto)

    have Distinct1_pre :
      "distinct (map fst pre)"
      using Distinct1 by auto

    have Distinct2_pre :
      "distinct (map snd pre)"
      using Distinct2 by auto

    have Distinct1_pre_n :
      "distinct (map fst (pre @ [(n1, n2)]))"
      using Distinct1 by auto

    have Distinct2_pre_n :
      "distinct (map snd (pre @ [(n1, n2)]))"
      using Distinct2 by auto

    have Conc_names :
      "list_all2
         (alpha_equiv_name'
           ((pre @
             (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
            fsubst))
         (map fst pre @ n1 # map fst gather1)
         (map snd pre @ n2 # map fst gather2)"
    proof(rule list_all2_appendI)
      show "list_all2
         (alpha_equiv_name'
           ((pre @
             (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
            fsubst))
         (map fst pre) (map snd pre)"
        using alpha_equiv_name_prefix[OF Distinct1_pre Distinct2_pre]
        by auto
    next
      have "list_all2
       (alpha_equiv_name'
         ((pre @
           (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
          fsubst))
       ([n1] @ map fst gather1) ([n2] @ map fst gather2)"
      proof(rule list_all2_appendI)
        show "list_all2
         (alpha_equiv_name'
           ((pre @
             (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
            fsubst))
             [n1] [n2]"
          using alpha_equiv_name_after[OF Distinct1_pre_n Distinct2_pre_n]
          by auto
      next

        show "list_all2
         (alpha_equiv_name'
           ((pre @
             (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
            fsubst))
         (map fst gather1) (map fst gather2)"

          using alpha_equiv_name_gather_functions[OF Cons1.prems]
          using Cons1.prems Cons2 X4 Y4 F1 F2
          by(auto)
      qed

      then show "list_all2
       (alpha_equiv_name'
         ((pre @
           (n1, n2) # zip (get_fun_decls stt1) (get_fun_decls stt2)) #
          fsubst))
       (n1 # map fst gather1) (n2 # map fst gather2)"
        by simp
    qed
  

    then show ?thesis
      using Cons1.prems Cons2 X4 Y4 F1 F2 Funs_t Funs_body Gather1 Gather2 
        Gather1_None Gather2_None Funs1_None Funs2_None Noshadow Noshadow_flip2
      using Cons1.IH[OF Gather1 Gather2 Eqv' Funs_t Distinct1 Distinct2]
      using check_decls_fun_decls[OF Funs_t] 
        by(auto simp add: alpha_equiv_fun_def alpha_equiv_function_sig'_scheme_def function_sig'.defs)
  next
    case (YulIf x51 x52)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case YulBreak
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case YulContinue
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case YulLeave
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
  case (YulBlock x11)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  qed
qed

lemma check_decls_distinct :
  assumes "alpha_equiv_check_decls sts1 sts2 = Some funcs'"
  shows "distinct (map fst funcs') \<and> distinct (map snd funcs')"
  using assms
proof(induction sts1 arbitrary: funcs' sts2)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons sth1 stt1)

  obtain sth2 stt2 where Cons2 : "sts2 = sth2 # stt2"
    using Cons1.prems
    by(cases sts2; auto)

  then show ?case
  proof(cases sth1)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case X4: (YulFunctionDefinitionStatement x4)

    then obtain y4 where Y4 : "sth2 = YulFunctionDefinitionStatement y4"
      using Cons1.prems Cons2
      by(cases sth2; auto)

    obtain n1 args1 rets1 body1 where F1 :
      "x4 = YulFunctionDefinition n1 args1 rets1 body1"
      by(cases x4; auto)

    obtain n2 args2 rets2 body2 where F2 :
      "y4 = YulFunctionDefinition n2 args2 rets2 body2"
      by(cases y4; auto)

    obtain funs_t where Funs_t :
      "alpha_equiv_check_decls stt1 stt2 = Some funs_t"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls stt1 stt2"; auto)

    have Notin1 : "map_of funs_t n1 = None"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t
      by(cases "map_of funs_t n1"; auto)

    have Notin2 : "map_of (subst'_flip funs_t) n2 = None"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Notin1
      by(cases "map_of (subst'_flip funs_t) n2"; auto)

    have Notin2' : "n2 \<notin> set (map snd funs_t)"
    proof
      assume Contra : "n2 \<in> set (map snd funs_t)"

      then obtain bad where Bad : "(bad, n2) \<in> set funs_t"
        by auto

      have Bad' : "(n2, bad) \<in> set (subst'_flip funs_t)"
        using Bad
        unfolding subst'_flip_def
        by(auto)

      have Bad'' : "n2 \<in> fst ` set (subst'_flip funs_t)"
        using imageI[OF Bad', of fst]
        by auto

      have Notin2_alt : "n2 \<notin> fst ` set (subst'_flip funs_t)"
        using Notin2
        unfolding map_of_eq_None_iff
        by auto

      show False using Notin2_alt Bad''
        by(auto)
    qed

    show ?thesis using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Notin1 Notin2 Notin2'
      by(auto)
  next
    case (YulIf x51 x52)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulBreak
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulContinue
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulLeave
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case (YulBlock x11)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  qed
qed

lemma check_decls_distinct1 :
  assumes "alpha_equiv_check_decls sts1 sts2 = Some funcs'"
  shows "distinct (map fst funcs')"
  using assms check_decls_distinct
  by auto

lemma check_decls_distinct2 :
  assumes "alpha_equiv_check_decls sts1 sts2 = Some funcs'"
  shows "distinct (map snd funcs')"
  using assms check_decls_distinct
  by auto

(*
lemma alpha_equiv_enter_function_stackEls :
  assumes Heqv : "alpha_equiv_check_decls sts1 sts2 = Some funcs'"
  assumes Hsts : "list_all2 (alpha_equiv_statement' (funcs' # fsubst)) sts1 sts2"
  assumes Hfuns : "list_all2 (alpha_equiv_fun fsubst) (fs1) (fs2)"
  assumes Htail : "list_all2 (alpha_equiv_stackEl' fsubst) c1t c2t"
  shows
    "list_all2
      (alpha_equiv_stackEl'
        (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst))
      (map EnterStatement sts1 @
       ExitStatement (YulBlock sts1) (l) (fs1) # c1t)
      (map EnterStatement sts2 @
       ExitStatement (YulBlock sts2) (l) (fs2) # c2t)"
  using assms
proof(induction sts1 arbitrary: sts2 funcs' fsubst fs1 fs2)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons sth1 stt1)

  obtain sth2 stt2 where Cons2 : "sts2 = sth2 # stt2"
    using Cons1.prems
    by(cases sts2; auto)

  then show ?case
  proof(cases sth1)
    case (YulFunctionCallStatement x1)
    then show ?thesis using Cons1 Cons2
      check_decls_fun_decls
      apply(cases sth2; auto)
  next
    case (YulAssignmentStatement x2)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulVariableDeclarationStatement x3)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case X4: (YulFunctionDefinitionStatement x4)

    then obtain y4 where Y4 : "sth2 = YulFunctionDefinitionStatement y4"
      using Cons1.prems Cons2
      by(cases sth2; auto)

    obtain n1 args1 rets1 body1 where F1 :
      "x4 = YulFunctionDefinition n1 args1 rets1 body1"
      by(cases x4; auto)

    obtain n2 args2 rets2 body2 where F2 :
      "y4 = YulFunctionDefinition n2 args2 rets2 body2"
      by(cases y4; auto)

    obtain funs_t where Funs_t :
      "alpha_equiv_check_decls stt1 stt2 = Some funs_t"
      using Cons1 Cons2 X4 Y4 F1 F2
      by (cases "alpha_equiv_check_decls stt1 stt2"; auto)

    have Notin1 : "map_of funs_t n1 = None"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t
      by(cases "map_of funs_t n1"; auto)

    have Notin2 : "map_of (subst'_flip funs_t) n2 = None"
      using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Notin1
      by(cases "map_of (subst'_flip funs_t) n2"; auto)

    have Notin2' : "n2 \<notin> set (map snd funs_t)"
    proof
      assume Contra : "n2 \<in> set (map snd funs_t)"

      then obtain bad where Bad : "(bad, n2) \<in> set funs_t"
        by auto

      have Bad' : "(n2, bad) \<in> set (subst'_flip funs_t)"
        using Bad
        unfolding subst'_flip_def
        by(auto)

      have Bad'' : "n2 \<in> fst ` set (subst'_flip funs_t)"
        using imageI[OF Bad', of fst]
        by auto

      have Notin2_alt : "n2 \<notin> fst ` set (subst'_flip funs_t)"
        using Notin2
        unfolding map_of_eq_None_iff
        by auto

      show False using Notin2_alt Bad''
        by(auto)
    qed

    show ?thesis using Cons1 Cons2 X4 Y4 F1 F2 Funs_t Notin1 Notin2 Notin2'
      by(auto)
  next
    case (YulIf x51 x52)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulSwitch x61 x62)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  next
    case (YulForLoop x71 x72 x73 x74)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulBreak
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulContinue
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case YulLeave
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)  
  next
    case (YulBlock x11)
    then show ?thesis using Cons1 Cons2
      by(cases sth2; auto)
  qed
qed
*)

lemma alpha_equiv_locals'_eq :
  shows "alpha_equiv_locals' fsubst x x"
proof(induction x arbitrary: fsubst)
  case Nil
  then show ?case
    by(auto simp add: alpha_equiv_locals'_def)
next
  case (Cons xh xt)
  then show ?case
    by(auto simp add: alpha_equiv_locals'_def)
qed

(*lemma*)
(* TODO: is this still true? *)
(*
lemma alpha_equiv_stackEls'_enter :
  assumes "list_all2 (alpha_equiv_statement' subst) sts1 sts2"
  shows
    "alpha_equiv_stackEls'
     (subst)
     (map EnterStatement sts1) (map EnterStatement sts2)"
  using assms
proof(induction sts1 arbitrary: subst sts2)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons st1h st1t)

  obtain st2h st2t where Cons2 :
    "sts2 = st2h # st2t"
    using Cons1.prems
    by(cases sts2; auto)

  show ?case using Cons1 Cons2
    by(cases st1h; cases st2h; auto)
qed
*)

lemma alpha_equiv_stackEls'_newsubst_enter :
  assumes "list_all2 (alpha_equiv_statement' subst) sts1 sts2"
  shows
    "alpha_equiv_stackEls'_newsubst
     (subst)
     (map EnterStatement sts1) (map EnterStatement sts2) = Some subst"
  using assms
proof(induction sts1 arbitrary: subst sts2)
  case Nil
  then show ?case 
    by(auto)
next
  case Cons1 : (Cons st1h st1t)

  obtain st2h st2t where Cons2 :
    "sts2 = st2h # st2t"
    using Cons1.prems
    by(cases sts2; auto)

  show ?case using Cons1 Cons2
    by(cases st1h; cases st2h; auto)
qed


definition min_prefix ::
  "('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"min_prefix P pre full \<equiv>
  (\<exists> post . full = pre @ post \<and> 
   P pre \<and>
   (\<forall> pre' post' . full = pre' @ post' \<longrightarrow> P pre' \<longrightarrow>
     (\<exists> mid . pre' = pre @ mid)))"

lemma min_prefixI :
  assumes Heq : "full = pre @ post"
  assumes HP : "P pre"
  assumes Hmin : "\<And> pre' post' . pre @ post = pre' @ post' \<Longrightarrow> P pre' \<Longrightarrow> 
    (\<exists> mid . pre' = pre @ mid)"
  shows "min_prefix P pre full"
  using assms
  by(auto simp add: min_prefix_def)

lemma min_prefixD0 :
  assumes H : "min_prefix P pre full"
  shows "\<exists> post . full = pre @ post"
  using assms unfolding min_prefix_def by auto

lemma min_prefixD1 :
  assumes H : "min_prefix P pre full"
  shows "P pre"
  using assms unfolding min_prefix_def by auto

lemma min_prefixD2 :
  assumes H : "min_prefix P pre full"
  assumes Heq' : "full = pre' @ post'"
  assumes HP : "P pre'"
  shows "\<exists> mid . pre' = pre @ mid"
  using assms unfolding min_prefix_def by auto


definition max_suffix ::
  "('a list \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where
"max_suffix P post full \<equiv>
  (\<exists> pre . full = pre @ post \<and> 
   P post \<and>
   (\<forall> pre' post' . full = pre' @ post' \<longrightarrow> P post' \<longrightarrow>
     (\<exists> mid . post = mid @ post')))"

lemma max_suffixI :
  assumes Heq : "full = pre @ post"
  assumes HP : "P post"
  assumes Hmin : "\<And> pre' post' . pre @ post = pre' @ post' \<Longrightarrow> P post' \<Longrightarrow> 
    (\<exists> mid . post = mid @ post')"
  shows "max_suffix P post full"
  using assms
  by(auto simp add: max_suffix_def)

lemma max_suffixD0 :
  assumes H : "max_suffix P post full"
  shows "\<exists> pre . full = pre @ post"
  using assms unfolding max_suffix_def by auto

lemma max_suffixD1 :
  assumes H : "max_suffix P post full"
  shows "P post"
  using assms unfolding max_suffix_def by auto

lemma max_suffixD2 :
  assumes H : "max_suffix P post full"
  assumes Heq' : "full = pre' @ post'"
  assumes HP : "P post'"
  shows "\<exists> mid . post = mid @ post'"
  using assms unfolding max_suffix_def by auto

(* TODO: figure out if we are properly restricting
   locals. I think we are.
*)
lemma yulBreak_result :
  assumes H : "yulBreak d c1 r1 = YulResult r1'"
  shows "global r1' = global r1 \<and>
         vals r1' = vals r1 \<and>
         locals r1' = locals r1 \<and>
         funs r1' = funs r1 \<and>
         (\<exists> c1pre . c1 = c1pre @ cont r1')"
  using assms
proof(induction c1 arbitrary: r1 r1')
case Nil
  then show ?case
    by(auto)
next
  case (Cons c1h c1t)
  show ?case
  proof(cases c1h)
    case C1h : (EnterStatement st1)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case C1h : (ExitStatement st1 locals1 funs1)
    show ?thesis
    proof(cases st1)
      case (YulFunctionCallStatement x1)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
      by(auto)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulVariableDeclarationStatement x3)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulIf x51 x52)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulSwitch x61 x62)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case YulBreak
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
    case YulContinue
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case YulLeave
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulBlock x11)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    qed
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case (Expression x5)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] 
      by(auto)
  qed
qed

(* this is actually kind of interesting. alpha equiv may not hold while in the middle
 * of skipping statements with YulBreak, but will hold by the end
 *)
(*
lemma yulBreak_result_equiv :
  assumes H1 : "yulBreak d c1 r1 = YulResult r1'"
  assumes H2 : "yulBreak d c2 r2 = YulResult r2'"
  assumes Halpha : "alpha_equiv_stackEls' fsubst c1 c2"
  shows "alpha_equiv_stackEls' fsubst (cont r1') (cont r2')"
  using assms
proof(induction c1 arbitrary: r1 r1' c2 r2 r2' fsubst)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons c1h c1t)

  obtain c2h c2t where Cons2 : "c2 = (c2h # c2t)"
    using Cons1.prems
    by(cases c2; auto)

  show ?case
  proof(cases c1h)
    case C1h : (EnterStatement st1)
    then show ?thesis using Cons1.prems Cons1.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1' c2t "(r2 \<lparr> cont := c2t \<rparr>)" r2'] Cons2
      apply(cases c2h; auto)
  next
    case C1h : (ExitStatement st1 locals1 funs1)
    show ?thesis
    proof(cases st1)
      case (YulFunctionCallStatement x1)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
      by(auto)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulVariableDeclarationStatement x3)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulIf x51 x52)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulSwitch x61 x62)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case YulBreak
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
    case YulContinue
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case YulLeave
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    next
      case (YulBlock x11)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
        by(auto)
    qed
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case (Expression x5)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] 
      by(auto)
  qed


    using Cons1 Cons2
    apply(auto)

    apply(auto)
qed
*)


(* need to characterize cont differently. *)
lemma yulContinue_result :
  assumes H : "yulContinue d c1 r1 = YulResult r1'"
(*  assumes Hr1 : "cont r1 = c1"*)
  shows "global r1' = global r1 \<and>
         vals r1' = vals r1 \<and>
         locals r1' = locals r1 \<and>
         funs r1' = funs r1 \<and>
         (\<exists> c1pre c1post pre cond1 cond post body fx cx .
            c1 = c1pre @ Expression cond1 # ExitStatement (YulForLoop pre cond post body) fx cx # c1post \<and>
            cont r1' = EnterStatement (YulBlock post) # Expression cond1 # ExitStatement (YulForLoop pre cond post body) fx cx # c1post)"
  using assms
proof(induction c1 arbitrary: r1 r1')
case Nil
  then show ?case
    by(auto)
next
  case (Cons c1h c1t)
  show ?case
  proof(cases c1h)
    case C1h : (EnterStatement st1)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case C1h : (ExitStatement st1 locals1 funs1)
      then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h
      by(auto)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1']
      by(auto)
  next
    case C1h : (Expression e1)
    show ?thesis
    proof(cases c1t)
      case Nil' : Nil
      then show ?thesis
        using Cons C1h 
        by(auto)
    next
      case Cons' : (Cons c1h' c1t')
      then show ?thesis
      proof(cases c1h')
        case (EnterStatement x1)
        then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h Cons'
          by(auto)
      next
        case C1h' : (ExitStatement st1' locals1' funs1')
        then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h Cons'
          by(cases st1'; auto)
      next
        case (EnterFunctionCall x31 x32)
        then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h Cons'
          by(auto)
      next
        case (ExitFunctionCall x41 x42 x43 x44 x45)
        then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h Cons'
          by(auto)
      next
        case (Expression x5)
        then show ?thesis using Cons.prems Cons.IH[of "(r1\<lparr>cont := c1t\<rparr>)" r1'] C1h Cons'
          by(auto)
      qed
    qed
  qed
qed

(* TODO: is it an issue that yulLeave
 * does not update state continuation on recursive calls?
 * Probably not, since program ends anyway
 *)
lemma yulLeave_result :
  assumes H : "yulLeave d c1 r1 = YulResult r1'"
  shows "global r1' = global r1 \<and>
         vals r1' = vals r1 \<and>
         locals r1' = locals r1 \<and>
         funs r1' = funs r1 \<and>
         (\<exists> c1pre . c1 = c1pre @ cont r1')"
  using assms
proof(induction c1 arbitrary: r1 r1')
case Nil
  then show ?case
    by(auto)
next
  case (Cons c1h c1t)
  show ?case
  proof(cases c1h)
    case C1h : (EnterStatement st1)
    then show ?thesis
      using Cons.prems Cons.IH[of r1 r1']
      by(auto)
  next
    case C1h : (ExitStatement st1 locals1 funs1)
    then show ?thesis
      using Cons.prems Cons.IH[of r1 r1']
      by(auto)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Cons.prems Cons.IH[of "r1" r1']
      by(auto)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Cons.prems Cons.IH[of r1 r1']
      by(auto)
  next
    case (Expression x5)
    then show ?thesis using Cons.prems Cons.IH[of r1 r1'] 
      by(auto)
  qed
qed


(*
lemma yulBreak_result :
  assumes H1c : "cont r1 = c1"
  (*assumes H1v : "vals r1 = []" *)
  assumes H1br : "yulBreak d c1 r1 = YulResult r1'"
  assumes H2c : "cont r2 = c2"
  assumes H2br : "yulBreak d c2 r2 = YulResult r2'"
  assumes Halpha : "alpha_equiv_stackEls' fsubst
*)

lemma alpha_equiv_expr_same_constructor :
  assumes H: "alpha_equiv_expr' fsubst e1 e2"
  shows "yul_expression_same_constructor e1 e2"
proof(cases e1)
  case (YulFunctionCallExpression x1)
  then show ?thesis using H
    by(cases e2; auto)
next
  case (YulIdentifier x2)
  then show ?thesis using H
    by(cases e2; auto)
next
  case (YulLiteralExpression x3)
  then show ?thesis using H
    by(cases e2; auto)
qed

lemma alpha_equiv_stackEls'_subst_update_cont_break :
  assumes "alpha_equiv_stackEls' fsubst l1 l2"
  assumes "subst_update_cont_break fsubst l1 l2 = Some (fsubst', l1', l2')"
  shows "alpha_equiv_stackEls' fsubst' l1' l2'"
  using assms
proof(induction l1 arbitrary: fsubst l2 fsubst' l1' l2')
  case Nil
  then show ?case
    by(cases l2; auto)
next
  case Cons1 : (Cons l1h l1t)

  obtain l2h l2t where Cons2 : "l2 = l2h # l2t"
    using Cons1.prems
    by(cases l2; auto)

  show ?case
  proof(cases l1h)
    case ES1 : (EnterStatement st1)

    then obtain st2 where ES2 : "l2h = EnterStatement st2"
      using Cons1.prems Cons2
      by(cases l2h; auto)

    show ?thesis
    proof(cases st1)
      case (YulFunctionCallStatement x1)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulVariableDeclarationStatement x3)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulFunctionDefinitionStatement x4)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulIf x51 x52)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulSwitch x61 x62)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case YulBreak
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case YulContinue
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case YulLeave
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    next
      case (YulBlock x11)
      then show ?thesis 
        using Cons1 Cons2 ES1 ES2
        by(cases st2; auto)
    qed
  next
    case XS1 : (ExitStatement a1 b1 c1)

    then obtain a2 b2 c2 where XS2: "l2h = ExitStatement a2 b2 c2"
      using Cons1.prems Cons2
      by (cases l2h; auto)

    show ?thesis
    proof(cases a1)
      case (YulFunctionCallStatement x1)
      then show ?thesis 
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case (YulAssignmentStatement x2)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case DS1 : (YulVariableDeclarationStatement d1)

      then obtain d2 where DS2 : "a2 = YulVariableDeclarationStatement d2"
        using Cons1.prems Cons2 XS1 XS2
        by(cases a2; auto)

      then show ?thesis
        using Cons1 Cons2 XS1 XS2 DS1
        by(cases d1; cases d2;  auto)
    next
    case (YulFunctionDefinitionStatement x4)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case (YulIf x51 x52)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case (YulSwitch x61 x62)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case (YulForLoop x71 x72 x73 x74)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case YulBreak
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
    case YulContinue
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case YulLeave
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; auto)
    next
      case BS1 : (YulBlock sts)
      then show ?thesis
        using Cons1 Cons2 XS1 XS2
        by(cases a2; cases fsubst; auto)
    qed
  next
    case (EnterFunctionCall x31 x32)

    then show ?thesis using Cons1.prems Cons1.IH[of fsubst l2t fsubst'] Cons2
      by(cases l2h; auto)
  next
    case XF1 : (ExitFunctionCall a1 b1 c1 d1 e1)

    then obtain a2 b2 c2 d2 e2 where
      XF2 : "l2h = ExitFunctionCall a2 b2 c2 d2 e2"
      using Cons1.prems Cons2
      by(cases l2h; auto)

    then show ?thesis using Cons1.prems Cons1.IH Cons2 XF1
      by(auto simp add:alpha_equiv_function_sig'_scheme_def split: option.splits YulFunctionBody.splits)
  next
    case (Expression x5)
    then show ?thesis using Cons1.prems Cons1.IH[of fsubst l2t fsubst'] Cons2
      by(cases l2h; auto split: if_splits)
  qed
qed
  

(* YOU ARE HERE. See if we still need the check_decls cases lemma. *)
lemma alpha_equiv_step :
  assumes Hc1 : "cont r1 = (c1h#c1t)"
  assumes Hc2 : "cont r2 = (c2h#c2t)"
  assumes Hinit : "alpha_equiv_results' fsubst r1 r2"
  assumes H1 : "evalYulStep d r1 = YulResult r1'"
  assumes H2 : "evalYulStep d r2 = YulResult r2'"
  assumes Hupd : "subst_update fsubst c1h c2h = Some (fsubst')"
  shows "alpha_equiv_results' fsubst' r1' r2'"
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
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
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
      using alpha_equiv_expr_same_constructor[of fsubst' e1 e2]
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
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
      by(cases eo1; cases eo2; 
          auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          intro: alpha_equiv_expr_same_constructor)
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
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
  next
    case I1 : (YulIf cond1 body1)

    obtain cond2 body2 where I2 :
      "x2 = YulIf cond2 body2"
      using ES1 ES2 I1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 I1 ES2 I2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          intro: alpha_equiv_expr_same_constructor)
  next
    case S1 : (YulSwitch cond1 body1)

    obtain cond2 body2 where S2 :
      "x2 = YulSwitch cond2 body2"
      using ES1 ES2 S1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 S1 ES2 S2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          intro: alpha_equiv_expr_same_constructor)
  next
    case L1 : (YulForLoop pre1 cond1 post1 body1)

    obtain pre2 cond2 post2 body2 where L2 :
      "x2 = YulForLoop pre2 cond2 post2 body2"
      using ES1 ES2 L1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    obtain funcs'_pre where Decls_pre :
      "alpha_equiv_check_decls pre1 pre2 = Some (funcs'_pre)"
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    obtain funcs'_body where Decls_body :
      "alpha_equiv_check_decls body1 body2 = Some (funcs'_body)"
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    obtain funcs'_post where Decls_post :
      "alpha_equiv_check_decls post1 post2 = Some (funcs'_post)"
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    show ?thesis
    proof(cases pre1)
      case Nil

      then show ?thesis
        using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd Decls_pre Decls_body Decls_post
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
    next

      case Cons1 : (Cons pre1h pre1t)

      obtain pre2h pre2t where Cons2 :
        "pre2 = pre2h # pre2t"
        using Cons1 ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd Decls_pre
        by(cases pre2; auto)

      show ?thesis
        using Cons1 Cons2 ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd Decls_pre Decls_body Decls_post
        apply(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
        sorry
    qed
(* I think we just need some lemmas about splitting
 * alpha_equiv_check_decls
 *)

(*
    show ?thesis
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd Decls_pre Decls_body Decls_post
      apply(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)


    have Distinct1 : "distinct (map fst funcs')"
      using check_decls_distinct1[OF Decls]
      by auto

    have Distinct2 : "distinct (map snd funcs')"
      using check_decls_distinct2[OF Decls]
      by auto

    have Decls_eq : "zip (get_fun_decls sts1) (get_fun_decls sts2) = funcs'"
      using check_decls_fun_decls[OF Decls]
      by auto

    show ?thesis
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      apply(auto simp add: alpha_equiv_results'_def)
      sorry
*)
(*
    show ?thesis
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      apply(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
*)

  next
    case B1 : YulBreak

    then have B2 : "x2 = YulBreak"
      using ES1 ES2 B1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then show ?thesis
    proof(cases "subst_update_cont_break fsubst' c1t c2t")
      case None
      then show ?thesis
        using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
    next
      case (Some r)

      then obtain fsubst' c1t' c2t' where
        R: "r = (fsubst', c1t', c2t')"
        by(cases r; auto)

      then show ?thesis 
        using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
        using alpha_equiv_stackEls'_subst_update_cont_break[OF _ Some[unfolded R]] Some R
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
    qed
  next
    case C1 : YulContinue
    then have C2 : "x2 = YulContinue"
      using ES1 ES2 C1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 C1 ES2 C2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
  next
    case L1 : YulLeave
    then have L2 : "x2 = YulLeave"
      using ES1 ES2 L1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    show ?thesis
      using ES1 L1 ES2 L2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
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

    obtain funcs' where Decls :
      "alpha_equiv_check_decls sts1 sts2 = Some (funcs')"
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    have Distinct1 : "distinct (map fst funcs')"
      using check_decls_distinct1[OF Decls]
      by auto

    have Distinct2 : "distinct (map snd funcs')"
      using check_decls_distinct2[OF Decls]
      by auto

    have Decls_eq : "zip (get_fun_decls sts1) (get_fun_decls sts2) = funcs'"
      using check_decls_fun_decls[OF Decls]
      by auto

    have Conc1 : "list_all2
       (alpha_equiv_fun (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst))
       (combine_keep (funs r1)
         (map (\<lambda>(n, fs).
                  (n, function_sig'.extend fs \<lparr>f_sig_visible = map fst fs1\<rparr>))
           fs1))
       (combine_keep (funs r2)
         (map (\<lambda>(n, fs).
                  (n, function_sig'.extend fs \<lparr>f_sig_visible = map fst fs2\<rparr>))
           fs2))"
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls Distinct1 Distinct2
      using alpha_equiv_gather_functions[OF Fs1 Fs2 _ Decls, of "[]" fsubst]
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def)

    have Conc2 :
      "alpha_equiv_stackEls' (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)
       (map EnterStatement sts1 @ ExitStatement (YulBlock sts1) (locals r2) (funs r1) # c1t)
       (map EnterStatement sts2 @ ExitStatement (YulBlock sts2) (locals r2) (funs r2) # c2t)"
    proof(rule alpha_equiv_stackEls'_split)
      show "alpha_equiv_stackEls'
       (zip (get_fun_decls sts1)
         (get_fun_decls sts2) #
        fsubst)
       (map EnterStatement sts1)
       (map EnterStatement sts2)"
        using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls Decls_eq
        using alpha_equiv_stackEls'_enter
        unfolding alpha_equiv_results'_def
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def alpha_equiv_locals'_eq)
    next
      show "alpha_equiv_stackEls'_newsubst
           (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)
           (map EnterStatement sts1) (map EnterStatement sts2) =
          Some (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)"
        using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls Decls_eq
        using alpha_equiv_stackEls'_newsubst_enter
        unfolding alpha_equiv_results'_def
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def alpha_equiv_locals'_eq)
    next
      show "alpha_equiv_stackEls'
     (zip (get_fun_decls sts1) (get_fun_decls sts2) # fsubst)
     (ExitStatement (YulBlock sts1) (locals r2) (funs r1) # c1t)
     (ExitStatement (YulBlock sts2) (locals r2) (funs r2) # c2t)"
        using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls Decls_eq
        unfolding alpha_equiv_results'_def
        by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def alpha_equiv_locals'_eq)
    qed

    show ?thesis
      using ES1 B1 ES2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Fs1 Fs2 Decls Conc1 Conc2
      unfolding alpha_equiv_results'_def
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def)
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
    case A1 : (YulAssignmentStatement a1)

    then obtain vs1 e1 where
      AS1 : "a1 = YulAssignment vs1 e1"
      by(cases a1; auto)

    obtain a2 where A2 :
      "x2 = YulAssignmentStatement a2"
      using XS1 XS2 A1 AS1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain vs2 e2 where
      AS2 : "a2 = YulAssignment vs2 e2"
      by(cases a2; auto)

    show ?thesis
      using XS1 A1 AS1 XS2 A2 AS2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split:if_split_asm option.split_asm)
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
      using XS1 D1 VD1 XS2 D2 VD2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(cases eo1; cases eo2; auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split: if_split_asm option.split_asm)
  next
    case F1 : (YulFunctionDefinitionStatement f1)

    then obtain names1 args1 rets1 body1 where
      FS1 : "f1 = YulFunctionDefinition names1 args1 rets1 body1"
      by(cases f1; auto)

    obtain f2 where F2 :
      "x2 = YulFunctionDefinitionStatement f2"
      using XS1 XS2 F1 FS1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    then obtain names2 args2 rets2 body2 where
      FS2 : "f2 = YulFunctionDefinition names2 args2 rets2 body2"
      by(cases f2; auto)

    show ?thesis
      using XS1 F1 FS1 XS2 F2 FS2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def)
  next
    case I1 : (YulIf x51 x52)
    then show ?thesis sorry
  next
    case S1 : (YulSwitch x61 x62)
    then show ?thesis sorry
  next
    case L1 : (YulForLoop x71 x72 x73 x74)
    then show ?thesis sorry
  next
    case B1 : YulBreak

    then have B2 : "x2 = YulBreak"
      using XS1 XS2 B1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    have Break1 : "yulBreak d c1t (r1\<lparr>cont := c1t, vals := []\<rparr>) = YulResult r1'"
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split: if_split_asm option.split_asm)      

    have Break2 : "yulBreak d c2t (r2\<lparr>cont := c2t, vals := []\<rparr>) = YulResult r2'"
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split: if_split_asm option.split_asm)      

    obtain c1pre c2pre where 
      Breaks : "alpha_equiv_stackEls' fsubst' (c1pre @ cont r1') (c2pre @ cont r2')"
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      using yulBreak_result[OF Break1] yulBreak_result[OF Break2]
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split: if_split_asm option.split_asm)      

(* YOU ARE HERE
 * we need to further characterize c1pre and c2pre. they need to be the earliest occurrence
 * of the thing we are looking for, but that may not be enough
 * maybe something about how if two stack element lists are alpha equivalent,
 * the suffixes returned by break will also be *)

(* this one might be sort of interesting... *)
    show ?thesis
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd
      using yulBreak_result[OF Break1] yulBreak_result[OF Break2] Breaks Break1 Break2
      apply(auto simp add: alpha_equiv_results'_def alpha_equiv_locals'_def
          split: if_split_asm option.split_asm)      
(*

  (* vals = [] ? *)
  yulBreak d c1t (r1 \<lparr> cont := c1t \<rparr>) = YulResult r1' \<Longrightarrow>
  yulBreak d c2t (r2 \<lparr> cont := c2t \<rparr>) = YulResult r2' \<Longrightarrow>
alpha_equiv_stackEls' fsubst' c1t c2t \<Longrightarrow> global r1' = global r2'

likewise for vals

for funs:
alpha_equiv_funs' fsubst (funs r1') (funs r2')

likewise for cont (interesting case)

alpha_equiv_stackEls' fsubst' (cont r1') (cont r2')

*)
      sorry
  next
    case C1 : YulContinue
    then show ?thesis sorry
  next
    case L1 : YulLeave
    then show ?thesis sorry
  next
    case B1: (YulBlock sts1)

    obtain sts2 where B2 :
      "x2 = YulBlock sts2"
      using XS1 XS2 B1 Hc1 Hc2 Hinit
      by(cases x2; auto simp add: alpha_equiv_results'_def)

    obtain funcs' where Decls :
      "alpha_equiv_check_decls sts1 sts2 = Some (funcs')"
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd 
      by(auto simp add: alpha_equiv_results'_def split: option.splits)

    have Distinct1 : "distinct (map fst funcs')"
      using check_decls_distinct1[OF Decls]
      by auto

    have Distinct2 : "distinct (map snd funcs')"
      using check_decls_distinct2[OF Decls]
      by auto

    have Decls_eq : "zip (get_fun_decls sts1) (get_fun_decls sts2) = funcs'"
      using check_decls_fun_decls[OF Decls]
      by auto

    have Locs_Eq : "alpha_equiv_locals' fsubst' locs1 locs2"
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Decls 
      unfolding alpha_equiv_results'_def
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def)

    show ?thesis
      using XS1 B1 XS2 B2 Hinit H1 H2 Hc1 Hc2 Hupd Decls Locs_Eq
      unfolding alpha_equiv_results'_def alpha_equiv_locals'_def
      by(auto simp add: alpha_equiv_results'_def alpha_equiv_funs'_def)
  qed
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