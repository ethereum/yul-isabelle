theory YulSemanticsSingleStep imports "YulSemantics"
begin

(* For functions: search through a list of locals
   (corresponding to successive scopes) *)
(* Perhaps we don't need this, going to see if we can do without *)

(* Idea: a "small-step" executable semantics, where we describe transitions
   in terms of small increments. *)

(* stack used to represent computation remaining after this step *)
datatype stackEl =
  SeStatement "YulStatement"
  | SeStatements "YulStatement list"
  | SeExpr "YulExpression"
  | SeExprs "YulExpression list"
  | SeSwitchCases "YulSwitchCase list"
  (* separate pass to handle function scope correctly *)
  | SeGatherFuns "YulStatement list"
  (* Following a defunctionalization approach, these commands represent
     situations where we must run a subexpression during evaluation of an expression,
     and then resume *)
  | SeFinishBlock
  | SeFinishAssign
  | SeFinishIf "YulStatement list"
  | SeFinishForLoop "YulStatement list" "YulStatement list"
  | SeFinishForLoopPre "YulStatement list"
  (* after evaluating condition of switch, we need to track
     - remaining cases
     - default case (if seen so far) *)
  | SeFinishSwitch "YulSwitchCase list" "YulStatement list option"
  (* once we're done evaluating function arguments *)
  | SeFinishFunctionCall "YulIdentifier"

type_synonym errf = "String.literal option"


datatype ('g, 'v) result =
  StResult "'g" "'v local" "function_sig local" mode "stackEl list"
  | ExpResult "'g" "'v local" "function_sig local" "'v list" "stackEl list"
  | ErrorResult "String.literal"

type_synonym ('g, 'v) cont = "('g * 'v local * function_sig local * mode)"

locale YulSemS =
  fixes local_var :: "'v itself"
  fixes local_type :: "'t itself"
  fixes global_state :: "'g itself"

  fixes parseType :: "String.literal \<Rightarrow> 't option"
  fixes parseLiteral :: "String.literal \<Rightarrow> 'v option"

fixes defaultValue :: "'v"

  fixes error :: "String.literal \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes getError :: "'g \<Rightarrow> String.literal option"

  assumes error_isError :
    "\<And> msg G . getError (error msg G) = Some msg"

begin

fun isError :: "'g \<Rightarrow> bool" where
"isError G =
  (case getError G of
    None \<Rightarrow> False
    | Some _ \<Rightarrow> True)"

fun evalYulStatement ::
"YulStatement \<Rightarrow> ('g, 'v) result \<Rightarrow>
  ('g, 'v) result" where

"evalYulStatement _ (ErrorResult emsg) = (ErrorResult emsg)"

(* blocks need cleanup of variable scopes *)
(* NB: mode handling is done in evalYulStatements. *)
| "evalYulStatement (YulBlock sl) (StResult G L F _ cont) =
    StResult G L F Regular ((SeStatements sl) # SeFinishBlock # cont)"
| "evalYulStatement (YulBlock sl) _ =
    (ErrorResult (STR ''invalid eval context (YulBlock)''))"
    
(* function defs handled in a separate pass *)
| "evalYulStatement (YulFunctionDefinitionStatement _)
                    (StResult G L F _ cont) =
  StResult G L F Regular cont"
| "evalYulStatement (YulFunctionDefinitionStatement _) _ =
    ErrorResult (STR ''invalid eval context (YulFunctionDefinition)'')"

(* function calls *)
| "evalYulStatement (YulFunctionCallStatement fc)
    (StResult G L F _ cont) =
      StResult G L F Regular (SeExpr (YulFunctionCallExpression fc) # cont)"
| "evalYulStatement (YulFunctionCallStatement fc) _ =
    (ErrorResult (STR ''invalid eval context (YulFunctionCallExpression)''))"

(* variable declaration/definition *)
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration names None))
    (StResult G L F _ cont) =
    (case put_values L (strip_id_types names) (List.replicate (length names) defaultValue) of
      None \<Rightarrow> ErrorResult (STR ''should be dead code'')
      | Some L1 \<Rightarrow> StResult G L1 F Regular cont)"
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration names (Some expr)))
    (StResult G L F _ cont) =
      StResult G L F Regular
        (SeStatement (YulAssignmentStatement (YulAssignment (strip_id_types names) expr))#cont)"
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration _ _)) _ =
      ErrorResult (STR ''invalid eval context (YulVariableDeclaration)'')"

(* assignment *)
| "evalYulStatement
    (YulAssignmentStatement (YulAssignment ids expr))
    (StResult G L F _ cont) =
      StResult G L F Regular (SeExpr expr # SeFinishAssign # cont)"
| "evalYulStatement
    (YulAssignmentStatement _) _ =
      ErrorResult (STR ''invalid eval context (YulAssignmentStatement)'')"

(* if *)
| "evalYulStatement
    (YulIf cond body) (StResult G L F _ cont) =
    StResult G L F Regular
      (SeExpr cond # SeFinishIf body # cont)"
| "evalYulStatement (YulIf _ _) _ = ErrorResult (STR ''invalid eval context (YulIf)'')"

(* for loops with empty pre *)
| "evalYulStatement
    (YulForLoop [] cond post body) (StResult G L F _ cont) =
    StResult G L F Regular
      (SeExpr cond # SeFinishForLoop post body # cont)"
(* for loop with non empty pre *)
| "evalYulStatement
    (YulForLoop pre cond post body) (StResult G L F _ cont) =
    StResult G L F Regular
      (SeFinishForLoopPre pre # (SeStatement (YulForLoop [] cond post body)) # cont)"
| "evalYulStatement
    (YulForLoop _ _ _ _) _ =
    ErrorResult (STR ''invalid eval context (YulForLoop)'')"

(* switch *)
| "evalYulStatement (YulSwitch cond cases) (StResult G L F _ cont) =
    StResult G L F Regular
      (SeExpr cond # SeFinishSwitch cases None # cont)"
| "evalYulStatement (YulSwitch _ _) _ =
    ErrorResult (STR ''invalid eval context (YulSwitch)'')"

(* break *)
| "evalYulStatement YulBreak (StResult G L F _ cont) =
    StResult G L F Break cont"
| "evalYulStatement YulBreak _ =
    ErrorResult (STR ''invalid eval context (YulBreak)'')"

(* continue *)
| "evalYulStatement YulContinue (StResult G L F _ cont) =
    StResult G L F Continue cont"
| "evalYulStatement YulContinue _ =
    ErrorResult (STR ''invalid eval context (YulContinue)'')"

(* leave *)
| "evalYulStatement YulLeave (StResult G L F _ cont) =
    StResult G L F Leave cont"
| "evalYulStatement YulLeave _ =
    ErrorResult (STR ''invalid eval context (YulLeave)'')"

(* sequencing Yul statements *)
fun evalYulStatements :: "YulStatement list \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulStatements [] (StResult G L F mode cont) = StResult G L F mode cont"
| "evalYulStatements (s#st) (StResult G L F Regular cont) =
   StResult G L F Regular ((SeStatement s)#(SeStatements st)#cont)"
| "evalYulStatements (s#st) (StResult G L F mode cont) =
   StResult G L F mode cont"
| "evalYulStatements _ _ =
   ErrorResult (STR ''invalid eval context (statement-cons)'')"

(* convenience code for expressions that need to work for both Expr and Statement
   result types *)
fun unpackResult :: "('g, 'v) result \<Rightarrow> 
  (('g * 'v local * function_sig local * 'v list * stackEl list) +
   String.literal)" where
"unpackResult (StResult G L F _ cont) =
  (Inl (G, L, F, [], cont))"
| "unpackResult (ExpResult G L F vs cont) =
    (Inl (G, L, F, vs, cont))"
| "unpackResult (ErrorResult s) = Inr s"
(* | "unpackResult _ = Inr (STR ''unpacked bad result type'')" *)

fun evalYulExpression ::
"YulExpression \<Rightarrow> ('g, 'v) result \<Rightarrow>
  ('g, 'v) result" where
"evalYulExpression _ (ErrorResult emsg) = (ErrorResult emsg)"
| "evalYulExpression (YulIdentifier i) r =
   (case unpackResult r of
      Inr s \<Rightarrow> ErrorResult s
      | Inl (G, L, F, vs, cont) \<Rightarrow>
       (case (L i) of
        None \<Rightarrow> ErrorResult (STR ''Undeclared variable '' @@ i)
        | Some v \<Rightarrow> ExpResult G L F (vs @ [v]) cont))"
| "evalYulExpression (YulLiteralExpression (YulLiteral value type)) r =
   (case unpackResult r of
      Inr s \<Rightarrow> ErrorResult s
      | Inl (G, L, F, vs, cont) \<Rightarrow>
       (case (parseLiteral value) of
        None \<Rightarrow> ErrorResult (STR ''Bad literal '' @@ value)
        | Some v \<Rightarrow> ExpResult G L F (vs @ [v]) cont))"
| "evalYulExpression (YulFunctionCallExpression (YulFunctionCall name args)) r =
    (case unpackResult r of
      Inr s \<Rightarrow> ErrorResult s
      | Inl (G, L, F, vs, cont) \<Rightarrow>
          ExpResult G L F vs (SeExprs args # SeFinishFunctionCall name # cont))"

(* evaluating multiple Yul expressions and concatenating the results
   TODO: this is probably too permissive w/r/t function argument arities *)

fun evalYulExpressions :: "YulExpression list \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulExpressions [] (StResult G L F _ cont) =
  (ExpResult G L F [] cont)"
| "evalYulExpressions [] (ExpResult G L F vs cont) =
  (ExpResult G L F vs cont)"
| "evalYulExpressions (e#es) (StResult G L F _ cont) =
  (ExpResult G L F [] (SeExpr e # SeExprs es # cont))"
| "evalYulExpressions (e#es) (ExpResult G L F vs cont) =
  (ExpResult G L F vs (SeExpr e # SeExprs es # cont))"
| "evalYulExpressions _ _ = 
   ErrorResult (STR ''invalid eval context (expr-cons)'')"

(* need to gather funs at top of any compound statement.
   but this means we need to do the recursion on statement sequences differently. *)
fun dispatchYulStep :: "stackEl \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"dispatchYulStep (SeStatement s) r = evalYulStatement s r"
| "dispatchYulStep (SeStatements s) r = evalYulStatements s r"
| "dispatchYulStep (SeExpr e) r = evalYulExpression e r"
| "dispatchYulStep (SeExprs e) r = evalYulExpressions e r"
(* | "dispatchYulStep (SeSwitchCases sw) r = evalYulSwitchCases sw r" *)
(* | "dispatchYulStep (SeGatherFuns *)

fun evalYulStep :: "('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulStep r =
  (case unpackResult r of
    Inr s \<Rightarrow> ErrorResult s
    | Inl (_, _, _, _, []) \<Rightarrow> r
    | Inl (_, _, _, _, (ch#ct)) \<Rightarrow>
      (let r' = (case r of
          ExpResult G L F vs _ \<Rightarrow> ExpResult G L F vs ct
          | StResult G L F mode _ \<Rightarrow> StResult G L F mode ct
          | _ \<Rightarrow> r) in
         dispatchYulStep ch r'))"
       

(*
fun evalYul :: "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> stackEl \<Rightarrow> result"
  where
"evalYul G L F (SeStatement
*)

(*
  fun YulSemCPS :: "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow>
    YulStatement \<Rightarrow> (('g, 'v) cont)" where
*)  

end
end