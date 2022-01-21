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
(* i think this case is wrong *)
| "yul_pre_declare (YulSwitch e cs) =
   YulSwitch e 
    (map (\<lambda> c . case c of (YulSwitchCase v body) \<Rightarrow>
      (let body' = map yul_pre_declare body in
      (let decls = yul_gather_var_declarations body' in
      (let clean = yul_clean_var_declarations body' in
        YulSwitchCase v (YulVariableDeclarationStatement (YulVariableDeclaration decls None) # clean))))) cs)"
| "yul_pre_declare (YulBlock body) =
   (YulBlock (map yul_pull_for_pre body))"
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

(*
 the next thing
*)

(* Looking at a De Bruijn representation of names to capture renaming 
 * Idea: at all binding sites, identifiers become the empty string
 * At usage sites, identifiers become the scope depth at which that variable name was bound.
 * Challenge: in any given scope, we can have multiple variables declared, at different points
 * in the scope. To deal with this, we will use a notion of "virtual scopes",
 * wherein binding a varaiable creates a new scope that lasts until the end of the block.
*)

fun yul_statement_to_deBruijn ::
  "('v, 't) YulStatement \<Rightarrow> ('v, 't) YulStatement option" where

end