theory Renamer_DeBruijn

imports Renamer
begin

(*
 * To make an index-based approach more workable, we need to do a couple of transformations:
 * 1. Pull out for loop "pre"
 * 2. Pre-declare all variables (assumes variables are valid 
 *)

(*

YulFunctionCallStatement "('v, 't) YulFunctionCall" |
  YulAssignmentStatement "('v, 't) YulAssignment" |
  YulVariableDeclarationStatement "('v, 't) YulVariableDeclaration" |
  YulFunctionDefinitionStatement "('v, 't) YulFunctionDefinition" |
  YulIf (YulIfCondition: "('v, 't) YulExpression") (YulIfBody: "('v, 't) YulStatement list") |
  YulSwitch (YulSwitchExpression: "('v, 't) YulExpression") 
            (YulSwitchCases: "('v, 't) YulSwitchCase list") |
  YulForLoop (YulForLoopPre: "('v, 't) YulStatement list") 
             (YulForLoopCondition: "('v, 't) YulExpression") 
             (YulForLoopPost: "('v, 't) YulStatement list") 
             (YulForLoopBody: "('v, 't) YulStatement list")|
  YulBreak |
  YulContinue |
  YulLeave |
  YulBlock (YulBlockStatements: "('v, 't) YulStatement list")
and ('v, 't) YulSwitchCase = YulSwitchCase (YulSwitchCaseValue: "('v, 't) YulLiteral option")
                                           (YulSwitchCaseBody: "('v, 't) YulStatement list")
and ('v, 't) YulFunctionDefinition = YulFunctionDefinition
                                      (YulFunctionDefinitionName: YulIdentifier)
                                      (YulFunctionDefinitionArguments: "'t YulTypedName list")
                                      (YulFunctionDefinitionReturnValues: "'t YulTypedName list")
                                      (YulFunctionDefinitionBody: "('v, 't) YulStatement list")
*)

(*datatype 
  ('v, 't) YulFunctionCall =
  YulFunctionCall (YulFunctionCallName: YulIdentifier) 
                  (YulFunctionCallArguments: "('v, 't) YulExpression list")
and ('v, 't) YulExpression = YulFunctionCallExpression "('v, 't) YulFunctionCall"
     | YulIdentifier YulIdentifier
     | YulLiteralExpression "('v, 't) YulLiteral"

*)

fun yul_pull_for_pre ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement" where
"yul_pull_for_pre (YulFunctionDefinitionStatement (YulFunctionDefinition n args rets body)) =
  (YulFunctionDefinitionStatement (YulFunctionDefinition n args rets (map yul_pull_for_pre body)))"
| "yul_pull_for_pre (YulIf e body) = (YulIf e (map yul_pull_for_pre body))"
| "yul_pull_for_pre (YulSwitch e cs) =
   YulSwitch e (map (\<lambda> c . case c of (YulSwitchCase v b) \<Rightarrow>
                      (YulSwitchCase v (map yul_pull_for_pre b))) cs)"
| "yul_pull_for_pre (YulBlock body) =
   (YulBlock (map yul_pull_for_pre body))"
(* the nil-pre case isn't necessary, but makes this a noop if the pre is already empty *)
| "yul_pull_for_pre (YulForLoop [] cond post body) =
   YulForLoop [] cond (map yul_pull_for_pre post) (map yul_pull_for_pre body)"
| "yul_pull_for_pre (YulForLoop pre cond post body) =
   YulBlock (
    pre @
    [YulForLoop [] cond (map yul_pull_for_pre post) (map yul_pull_for_pre body)]
   )"
| "yul_pull_for_pre x = x"

(* gather declarations for a particular block-like context.
 * this way we can pre-declare them. *)
fun yul_gather_var_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> 't YulTypedName list" where
"yul_gather_var_declarations [] = []"
| "yul_gather_var_declarations
    (YulVariableDeclarationStatement (YulVariableDeclaration names expr) # t) =
    names @ yul_gather_var_declarations t"
| "yul_gather_var_declarations (h#t) = yul_gather_var_declarations t"

(* turn all variable declarations into assignments (or remove them, if nothing is being
 * assigned *)
fun yul_clean_var_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list" where
"yul_clean_var_declarations [] = []"
| "yul_clean_var_declarations (YulVariableDeclarationStatement (YulVariableDeclaration _ None) # t) =
   yul_clean_var_declarations t"
| "yul_clean_var_declarations (YulVariableDeclarationStatement (YulVariableDeclaration ty_names (Some x)) # t) =
   YulAssignmentStatement (YulAssignment (map (\<lambda> tyn . case tyn of YulTypedName s _ \<Rightarrow> s) ty_names) x) #
   yul_clean_var_declarations t"
| "yul_clean_var_declarations (h#t) = h # yul_clean_var_declarations t"

(* TODO: this may not work if there are no variable declarations in some scope
 * (since we would then construct (YulVariableDeclaration [] None))
 *)
fun yul_pre_declare ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement" where
"yul_pre_declare (YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body)) =
  (let body' = map yul_pre_declare body in
  (let decls = yul_gather_var_declarations body' in
  (let clean = yul_clean_var_declarations body' in
  (YulFunctionDefinitionStatement 
    (YulFunctionDefinition name args rets
    (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))))))"
| "yul_pre_declare (YulIf e body) =
  (let body' = map yul_pre_declare body in
  (let decls = yul_gather_var_declarations body' in
  (let clean = yul_clean_var_declarations body' in
  (YulIf e
    (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean)))))"
(* TODO: double check this case *)
| "yul_pre_declare (YulSwitch e cs) =
   YulSwitch e 
    (map (\<lambda> c . case c of (YulSwitchCase v body) \<Rightarrow>
      (let body' = map yul_pre_declare body in
      (let decls = yul_gather_var_declarations body' in
      (let clean = yul_clean_var_declarations body' in
        YulSwitchCase v (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))))) cs)"
| "yul_pre_declare (YulBlock body) =
   (let body' = map yul_pre_declare body in
   (let decls = yul_gather_var_declarations body' in
   (let clean = yul_clean_var_declarations body' in
   (YulBlock 
    (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean)))))"
| "yul_pre_declare (YulForLoop pre cond post body) =
   YulForLoop
    (let pre' = map yul_pre_declare pre in
     let decls = yul_gather_var_declarations pre' in
     let clean = yul_clean_var_declarations pre' in
     (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))
    cond
    (let post' = map yul_pre_declare post in
     let decls = yul_gather_var_declarations post' in
     let clean = yul_clean_var_declarations post' in
     (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))
    (let body' = map yul_pre_declare body in
     let decls = yul_gather_var_declarations body' in
     let clean = yul_clean_var_declarations body' in
     (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))
   "
| "yul_pre_declare x = x"

fun yul_gather_fun_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulFunctionDefinition list" where
"yul_gather_fun_declarations [] = []"
| "yul_gather_fun_declarations (YulFunctionDefinitionStatement fd # t) =
    fd # yul_gather_fun_declarations t"
| "yul_gather_fun_declarations (h#t) =
    yul_gather_fun_declarations t"

fun yul_clean_fun_declarations ::
  "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulStatement list" where
"yul_clean_fun_declarations [] = []"
| "yul_clean_fun_declarations (YulFunctionDefinitionStatement fd # t) = t"
| "yul_clean_fun_declarations (h#t) = h#yul_clean_fun_declarations t"

fun yul_pre_declare_funs ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement" where
(* TODO: double check this case
 * need to make sure we don't run into issues with function declarations
 * being inside other function declarations
 *)
"yul_pre_declare_funs (YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body)) =
  (let body' = map yul_pre_declare_funs body in
   let decls = yul_gather_fun_declarations body' in
   let clean = yul_clean_fun_declarations body' in
   (YulFunctionDefinitionStatement
     (YulFunctionDefinition name args rets
     (map YulFunctionDefinitionStatement decls @ clean))))"
| "yul_pre_declare_funs (YulIf e body) =
  (let body' = map yul_pre_declare_funs body in
   let decls = yul_gather_fun_declarations body' in
   let clean = yul_clean_fun_declarations body' in
   (YulIf e
     (map YulFunctionDefinitionStatement decls @ clean)))"
(* TODO: double check this case *)
| "yul_pre_declare_funs (YulSwitch e cs) =
   YulSwitch e 
    (map (\<lambda> c . case c of (YulSwitchCase v body) \<Rightarrow>
      (let body' = map yul_pre_declare_funs body in
      (let decls = yul_gather_fun_declarations body' in
      (let clean = yul_clean_fun_declarations body' in
        YulSwitchCase v (map YulFunctionDefinitionStatement decls @ clean))))) cs)"
| "yul_pre_declare_funs (YulBlock body) =
    (let body' = map yul_pre_declare_funs body in
     let decls = yul_gather_fun_declarations body' in
     let clean = yul_clean_fun_declarations body' in
     (YulBlock
       (map YulFunctionDefinitionStatement decls @ clean)))"
| "yul_pre_declare_funs (YulForLoop pre cond post body) =
   YulForLoop
    (let pre' = map yul_pre_declare_funs pre in
     let decls = yul_gather_fun_declarations pre' in
     let clean = yul_clean_fun_declarations pre' in
     (map YulFunctionDefinitionStatement decls @ clean))
    cond
    (let post' = map yul_pre_declare_funs post in
     let decls = yul_gather_fun_declarations post' in
     let clean = yul_clean_fun_declarations post' in
     (map YulFunctionDefinitionStatement decls @ clean))
    (let body' = map yul_pre_declare_funs body in
     let decls = yul_gather_fun_declarations body' in
     let clean = yul_clean_fun_declarations body' in
     (map YulFunctionDefinitionStatement decls @ clean))
   "
| "yul_pre_declare_funs x = x"
  


(*
 the next thing we need: a way to represent de bruijn indices
 - we should generalize our syntax definition to allow other types
*)

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
 *)
datatype DbIx = 
  DbB_V
  | DbI_V (DbScope_V : nat) (DbVar_V : nat)
  | DbB_F
  | DbI_F (DbScope_F : nat) (DbVar_F : nat)

(* NB: assuming decls have been consolidated into one statement
 * we are still going to miss function-local variables.
 *)
fun get_var_decls ::
  "('v, 't) YulStatement list \<Rightarrow> 
   (YulIdentifier list * nat)" where
"get_var_decls [] = ([], 0)"
| "get_var_decls ((YulVariableDeclarationStatement (YulVariableDeclaration decls None))#t) =
   ((map (\<lambda> x . case x of (YulTypedName n _) \<Rightarrow> n) decls), 1)"
| "get_var_decls (h#t) = ([], 0)"

(* natural number tracks how many statements we are consuming *)
fun get_fun_decls ::
"('v, 't) YulStatement list \<Rightarrow>
 (YulIdentifier list * nat)" where
"get_fun_decls [] = ([], 0)"
| "get_fun_decls ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t) =
   (case get_fun_decls t of
     (rest, n) \<Rightarrow> 
     (name # rest
     , (1+n)))"
| "get_fun_decls (h#t) = ([], 0)"

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

(* convert a block to de Bruijn.
 * note that we aren't doing the recursive bit yet.
 *)

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

(*
  ('n, 'v, 't) YulFunctionCall' =
  YulFunctionCall (YulFunctionCallName: 'n) 
                  (YulFunctionCallArguments: "('n, 'v, 't) YulExpression' list")
and ('n, 'v, 't) YulExpression' = YulFunctionCallExpression "('n, 'v, 't) YulFunctionCall'"
     | YulIdentifier 'n
     | YulLiteralExpression "('v, 't) YulLiteral"
*)

(*
fun yul_statements_to_deBruijn_norec ::
  "(YulIdentifier list list) \<Rightarrow> ('v, 't) YulStatement list \<Rightarrow> (DbIx, 'v, 't) YulStatement' list option" where
*)

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
| "yul_statement_to_deBruijn scopes
    (YulVariableDeclarationStatement (YulVariableDeclaration ns e)) =
    (case e of
      Some _ \<Rightarrow> None
      | None \<Rightarrow> Some (YulVariableDeclarationStatement
        (YulVariableDeclaration (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) ns) None)))"

(* NB: the function itself is already in the scope at this point.
 * so what we are handling here are the further extensions
 * (params, rets, + function body bindings) needed *)

| "yul_statement_to_deBruijn scopes
    (YulFunctionDefinitionStatement
      (YulFunctionDefinition name args rets body)) =
      (let fnscope = 
        ((map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) args) @
         (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> n) rets))  in
        (case get_var_decls body of
             (vds, vn) \<Rightarrow>
             (case get_fun_decls (drop vn body) of
              (fds, fn) \<Rightarrow>
                (let scopes' = (fnscope @ vds @ fds) # scopes in
                (case those (map (yul_statement_to_deBruijn scopes') body) of
                  None \<Rightarrow> None
                  | Some body' \<Rightarrow> 
                    Some (YulFunctionDefinitionStatement
                         (YulFunctionDefinition DbB_V
                          (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) args) 
                          (map (\<lambda> x . case x of (YulTypedName n t) \<Rightarrow> YulTypedName DbB_V t) rets) body')))))))"

| "yul_statement_to_deBruijn scopes (YulIf e body) =
   (case yul_expr_to_deBruijn scopes e of
    None \<Rightarrow> None
    | Some e' \<Rightarrow>
    (case get_var_decls body of
     (vds, vn) \<Rightarrow>
     (case get_fun_decls (drop vn body) of
      (fds, fn) \<Rightarrow>
        (let scopes' = (vds @ fds) # scopes in
        (case those (map (yul_statement_to_deBruijn scopes') body) of
          None \<Rightarrow> None
          | Some body' \<Rightarrow> Some (YulIf e' body'))))))"

| "yul_statement_to_deBruijn scopes (YulSwitch e cases) =
   (case yul_expr_to_deBruijn scopes e of
    None \<Rightarrow> None
    | Some e' \<Rightarrow>
    (let ocases =
      (map (\<lambda> c . case c of (YulSwitchCase v body) \<Rightarrow>
        (case get_var_decls body of
         (vds, vn) \<Rightarrow>
         (case get_fun_decls (drop vn body) of
          (fds, fn) \<Rightarrow>
            (let scopes' = (vds @ fds) # scopes in
            (case those (map (yul_statement_to_deBruijn scopes') body) of
              None \<Rightarrow> None
              | Some body' \<Rightarrow> Some (YulSwitchCase v body')))))) cases) in
    (case (those ocases) of
     None \<Rightarrow> None
     | Some cases' \<Rightarrow> Some (YulSwitch e' cases'))))"

| "yul_statement_to_deBruijn scopes (YulForLoop [] cond post body) =
   (case yul_expr_to_deBruijn scopes cond of
    None \<Rightarrow> None
    | Some cond' \<Rightarrow>
    (let opost =
      (case get_var_decls post of
        (vds_post, vn_post) \<Rightarrow>
        (case get_fun_decls (drop vn_post post) of
          (fds_post, fn_post) \<Rightarrow>
            (let scopes'_post = (vds_post @ fds_post) # scopes in
            (those (map (yul_statement_to_deBruijn scopes'_post) post))))) in
    (let obody =
      (case get_var_decls body of
        (vds_body, vn_body) \<Rightarrow>
        (case get_fun_decls (drop vn_body body) of
          (fds_body, fn_body) \<Rightarrow>
            (let scopes'_body = (vds_body @ fds_body) # scopes in
            (those (map (yul_statement_to_deBruijn scopes'_body) body))))) in
    (case (opost, obody) of
      (Some post', Some body') \<Rightarrow>
        Some (YulForLoop [] cond' post' body')
      | _ \<Rightarrow> None))))"

| "yul_statement_to_deBruijn scopes (YulForLoop (h#t) cond post body) = None"

| "yul_statement_to_deBruijn scopes YulBreak = Some YulBreak"
| "yul_statement_to_deBruijn scopes YulContinue = Some YulContinue"
| "yul_statement_to_deBruijn scopes YulLeave = Some YulLeave"

| "yul_statement_to_deBruijn scopes (YulBlock body)  =
  (case get_var_decls body of
   (vds, vn) \<Rightarrow>
   (case get_fun_decls (drop vn body) of
    (fds, fn) \<Rightarrow>
      (let scopes' = (vds @ fds) # scopes in
      (case those (map (yul_statement_to_deBruijn scopes') \<comment> \<open> (drop (fn + vn) body)) \<close> body) of
        None \<Rightarrow> None
        | Some body' \<Rightarrow> Some (YulBlock body')))))"
(*
          (case yul_statements_to_deBruijn_norec body' scopes' of
            None \<Rightarrow> None
            | Some body'' \<Rightarrow> Some (YulBlock body''))))))"
*)
(*| "yul_statement_to_deBruijn _ x = Some x"*)


(* to convert to de Bruijn, we need to carry around some extra data.
 * list of scopes
 * depth = how many scopes we have to go through to find our target
 *)
end