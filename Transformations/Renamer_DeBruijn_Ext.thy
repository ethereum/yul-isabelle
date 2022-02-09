theory Renamer_DeBruijn_Ext

imports Renamer
begin

(* gather declarations for a particular block-like context. *)
fun yul_gather_var_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> 't YulTypedName list" where
"yul_gather_var_declarations [] = []"
| "yul_gather_var_declarations
    (YulVariableDeclarationStatement (YulVariableDeclaration names expr) # t) =
    names @ yul_gather_var_declarations t"
| "yul_gather_var_declarations (h#t) = yul_gather_var_declarations t"

fun yul_gather_fun_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulFunctionDefinition list" where
"yul_gather_fun_declarations [] = []"
| "yul_gather_fun_declarations (YulFunctionDefinitionStatement fd # t) =
    fd # yul_gather_fun_declarations t"
| "yul_gather_fun_declarations (h#t) =
    yul_gather_fun_declarations t"

(* Looking at a De Bruijn representation of names to capture renaming 
 * Idea: at all binding sites, identifiers become the empty string
 * At usage sites, identifiers become the scope depth at which that variable name was bound.
 * Challenge: in any given scope, we can have multiple variables declared, at different points
 * in the scope. To deal with this, we will use a notion of "virtual scopes",
 * wherein binding a varaiable creates a new scope that lasts until the end of the block.
*)
(*
 * first index is the scope number relative to where we are
 * second index is the variable number in that scope (since there may be more than one)
 * functions and variables share a namespace
 *)
datatype DbIx = 
  DbB_V (* represents a (nameless) binder *)
  (* represents a variable reference. First argument is scope depth, second is
   * which variable within the scope we want *)
  | DbI_V (DbScope_V : nat) (DbVar_V : nat)


(* NB: function-local declarations (parameters and returns) handled separately
 *)
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

fun index_of :: "'a list \<Rightarrow> 'a \<Rightarrow> nat option" where
"index_of [] _ = None"
| "index_of (h#t) k =
   (if h = k then Some 0
    else (case index_of t k of
          None \<Rightarrow> None
          | Some n \<Rightarrow> Some (1 + n)))"

fun get_index ::
  "YulIdentifier list list \<Rightarrow> YulIdentifier \<Rightarrow> DbIx option" where
"get_index [] _ = None"
| "get_index (l1#llt) k =
   (case index_of l1 k of
    Some n \<Rightarrow> Some (DbI_V 0 n)
    | None \<Rightarrow>
    (case get_index llt k of
      Some (DbI_V scope var) \<Rightarrow> Some (DbI_V (1 + scope) var)
      | _ \<Rightarrow> None))"

fun yul_expr_to_deBruijn ::
  "YulIdentifier list list \<Rightarrow> ('v, 't) YulExpression \<Rightarrow> (DbIx, 'v, 't) YulExpression' option" where
"yul_expr_to_deBruijn _ (YulLiteralExpression x) = Some (YulLiteralExpression x)"
| "yul_expr_to_deBruijn scopes (YulIdentifier n) =
   (case get_index scopes n of
    None \<Rightarrow> None
    | Some i \<Rightarrow> Some (YulIdentifier i))"
| "yul_expr_to_deBruijn scopes
    (YulFunctionCallExpression (YulFunctionCall fn args)) =
    (case get_index scopes fn of
     None \<Rightarrow> None
     | Some fni \<Rightarrow>
      (case those (map (yul_expr_to_deBruijn scopes) args) of
       None \<Rightarrow> None
        | Some argsi \<Rightarrow> Some (YulFunctionCallExpression (YulFunctionCall fni argsi))))"


(* build a de-Bruijn representation of our Yul program,
 * assuming that we have done all the prior passes (pulling all declarations to front)
 * assume the order: funs, function-declared variables (if we are a function), then vars, then everything else
 *)
(* TODO: we still need to add back in the binders here after we are done. *)
fun yul_statement_to_deBruijn ::
  "(YulIdentifier list list) \<Rightarrow> ('v, 't) YulStatement \<Rightarrow>  (DbIx, 'v, 't) YulStatement' option" where
"yul_statement_to_deBruijn scopes (YulFunctionCallStatement (YulFunctionCall n args)) =
  (case get_index scopes n of
     None \<Rightarrow> None
    | Some i \<Rightarrow> 
      (case those (map (yul_expr_to_deBruijn scopes) args) of
        None \<Rightarrow> None
        | Some args' \<Rightarrow> Some (YulFunctionCallStatement (YulFunctionCall i args'))))"

| "yul_statement_to_deBruijn scopes (YulAssignmentStatement (YulAssignment ns e)) =
  (case yul_expr_to_deBruijn scopes e of
    None \<Rightarrow> None
    | Some e' \<Rightarrow> 
      (case those (map (get_index scopes) ns) of
        None \<Rightarrow> None
        | Some ns' \<Rightarrow> Some (YulAssignmentStatement (YulAssignment ns' e'))))"

(* fix this *)
(*
| "yul_statement_to_deBruijn scopes
    (YulVariableDeclarationStatement (YulVariableDeclaration ns e)) =
    (case e of
      Some _ \<Rightarrow> None
      | None \<Rightarrow> Some (YulVariableDeclarationStatement
        (YulVariableDeclaration (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) ns) None)))"
*)

| "yul_statement_to_deBruijn scopes
    (YulVariableDeclarationStatement (YulVariableDeclaration ns eo)) =
    (let ns' = (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) ns) in
      (case eo of
          Some e \<Rightarrow> 
            (case yul_expr_to_deBruijn scopes e of
              None \<Rightarrow> None
              | Some e' \<Rightarrow>
              Some (YulVariableDeclarationStatement (YulVariableDeclaration ns' (Some e'))))
          | None \<Rightarrow> 
          Some (YulVariableDeclarationStatement (YulVariableDeclaration ns' None))))"


(* NB: the function itself is already in the scope at this point.
 * so what we are handling here are the further extensions
 * (params, rets, + function body bindings) needed *)

| "yul_statement_to_deBruijn scopes
    (YulFunctionDefinitionStatement
      (YulFunctionDefinition name args rets body)) =
      (let fnscope = 
        ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args) @
         (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets))  in
            (let scopes' = (fnscope @ (get_var_decls body) @ (get_fun_decls body)) # scopes in
            (case those (map (yul_statement_to_deBruijn scopes') body) of
              None \<Rightarrow> None
              | Some body' \<Rightarrow> 
                Some (YulFunctionDefinitionStatement
                     (YulFunctionDefinition DbB_V
                      (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) args) 
                      (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) rets) body')))))"

| "yul_statement_to_deBruijn scopes (YulIf e body) =
   (case yul_expr_to_deBruijn scopes e of
    None \<Rightarrow> None
    | Some e' \<Rightarrow>
      (let scopes' = (get_var_decls body @ get_fun_decls body) # scopes in
      (case those (map (yul_statement_to_deBruijn scopes') body) of
        None \<Rightarrow> None
        | Some body' \<Rightarrow> Some (YulIf e' body'))))"

| "yul_statement_to_deBruijn scopes (YulSwitch e cases) =
   (case yul_expr_to_deBruijn scopes e of
    None \<Rightarrow> None
    | Some e' \<Rightarrow>
    (let ocases =
      (map (\<lambda> c . case c of (YulSwitchCase v body) \<Rightarrow>
        (let scopes' = ((get_var_decls body) @ (get_fun_decls body)) # scopes in
        (case those (map (yul_statement_to_deBruijn scopes') body) of
          None \<Rightarrow> None
          | Some body' \<Rightarrow> Some (YulSwitchCase v body')))) cases) in
    (case (those ocases) of
     None \<Rightarrow> None
     | Some cases' \<Rightarrow> Some (YulSwitch e' cases'))))"

(* TODO: Function definitions shouldn't be allowed in pre, IIRC.
 * Probably it makes sense to exclude them in a separate pass, though
 * since we are handling most other similar constraints on Yul code that way.*)

| "yul_statement_to_deBruijn scopes (YulForLoop pre cond post body) =
  (let decls_pre = get_var_decls pre in
  (case yul_expr_to_deBruijn (decls_pre # scopes) cond of
    None \<Rightarrow> None
    | Some cond' \<Rightarrow>
      (let opre = 
        (let scopes'_pre = decls_pre # scopes in
         those (map (yul_statement_to_deBruijn scopes'_pre) pre)) in
      (let opost =
        (let scopes'_post = (decls_pre @ get_var_decls post @ get_fun_decls post) # scopes in
        (those (map (yul_statement_to_deBruijn scopes'_post) post))) in
      (let obody =
        (let scopes'_body = (decls_pre @ get_var_decls body @ get_fun_decls body) # scopes in
        (those (map (yul_statement_to_deBruijn scopes'_body) body))) in
      (case (opre, opost, obody) of
        (Some pre', Some post', Some body') \<Rightarrow>
          Some (YulForLoop pre' cond' post' body')
        | _ \<Rightarrow> None))))))"

| "yul_statement_to_deBruijn scopes YulBreak = Some YulBreak"
| "yul_statement_to_deBruijn scopes YulContinue = Some YulContinue"
| "yul_statement_to_deBruijn scopes YulLeave = Some YulLeave"

| "yul_statement_to_deBruijn scopes (YulBlock body)  =
    (let scopes' = (get_var_decls body @ get_fun_decls body) # scopes in
    (case those (map (yul_statement_to_deBruijn scopes') body) of
      None \<Rightarrow> None
      | Some body' \<Rightarrow> Some (YulBlock body')))"

(* entry point for yul_statement_to_deBruijn - 
 * for a whole program, start with empty scope.
 *)
definition yul_program_to_deBruijn ::
  "('v, 't) YulStatement \<Rightarrow>  (DbIx, 'v, 't) YulStatement' option" where
"yul_program_to_deBruijn p = (yul_statement_to_deBruijn [] p)"

(* this is probably not as useful *)
definition yul_program_expr_to_deBruijn ::
  "('v, 't) YulExpression \<Rightarrow> (DbIx, 'v, 't) YulExpression' option" where
"yul_program_expr_to_deBruijn p = (yul_expr_to_deBruijn [] p)"

(* tests *)

term \<open>YUL{
{
                    let x := 1
}
                    }\<close>

definition rename_test1 :: "(256 word, unit) YulStatement" where
  "rename_test1 \<equiv>
    (YUL{
    { let y : uint256
    {
    let z : uint256 
    let x : uint256
    function print(x : uint256) -> l  { l := x}
    x := 1
    y := 2
    let z : uint256 := 3
    print(z)
    }
    }})
    "

value "rename_test1"

definition rename_test1' :: "(256 word, unit) YulStatement list" where
"rename_test1' =
  (case rename_test1 of (YulBlock x) \<Rightarrow> x)"

value "get_var_decls rename_test1'"

value "yul_statement_to_deBruijn [] rename_test1"

end