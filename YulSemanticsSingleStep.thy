theory YulSemanticsSingleStep imports "YulSemanticsCommon"
begin

(* For functions: search through a list of locals
   (corresponding to successive scopes) *)
(* Perhaps we don't need this, going to see if we can do without *)

(* Idea: a "small-step" executable semantics, where we describe transitions
   in terms of small increments. *)

(* stack used to represent computation remaining after this step *)
datatype StackEl =
  SeStatement "YulStatement"
  | SeStatements "YulStatement list"
  | SeExpr "YulExpression"
  | SeExprs "YulExpression list"
  (* Following a defunctionalization approach, these commands represent
     situations where we must run a subexpression during evaluation of an expression,
     and then resume *)
  | SeBlock "YulStatement list"
  | SeEnterBlock "YulStatement list"
  | SeExitBlock
  | SeFinishAssign "YulIdentifier list"
  | SeFinishIf "YulStatement list"
  | SeFinishForLoop "YulExpression" "YulStatement list" "YulStatement list"
  (* after evaluating condition of switch, we need to track
     - remaining cases
     - default case (if seen so far) *)
  | SeFinishSwitch "YulSwitchCase list" "YulStatement list option"
  (* once we're done evaluating function arguments *)
  | SeEnterFunctionCall "YulIdentifier"
  | SeExitFunctionCall "YulIdentifier"

type_synonym errf = "String.literal option"

(*
datatype ('g, 'v) result =
  StResult "'g" "'v local" "function_sig local" mode "stackEl list"
  | ExpResult "'g" "'v local" "function_sig local" "'v list" "stackEl list"
  | ErrorResult "String.literal"
*)

(* Result = 
    global state g
    list of local state (variable \<rightarrow> value) frames
    list of function signature frames
    optional mode (for statement results)
    optional value list (for expression results)
*)

type_synonym ('g, 'v) result =
  "('g, 'v) YulResult * StackEl list"

(*
type_synonym ('g, 'v) cont = "('g * 'v local * function_sig local * mode)"
*)
locale YulSemS =
  fixes local_var :: "'v itself"
  fixes local_type :: "'t itself"
  fixes global_state :: "'g itself"

  fixes parseType :: "String.literal \<Rightarrow> 't option"
  fixes parseLiteral :: "String.literal \<Rightarrow> 'v option"

fixes isTruthy :: "'v \<Rightarrow> bool"

fixes defaultValue :: "'v"
(* global starting state *)
fixes G0 :: "'g"

(* starting function bindings - i.e., pre-defined *)
fixes F0 :: "function_sig locals"

begin

(* convenient package errors with a dummy empty continuation *)
abbreviation ErrorResult' where
"ErrorResult' emsg \<equiv> (ErrorResult emsg, [])"

(* TODO: review the way mode is being threaded *)
(* TODO: some of the places where we are swapping between "yul expression states"
   (that contain a list of accumulated variables) and "yul statement states"
   (that don't, but that do have a mode) are incorrect here. *)
fun evalYulStatement ::
"YulStatement \<Rightarrow> ('g, 'v) result \<Rightarrow>
  ('g, 'v) result" where

"evalYulStatement _ (ErrorResult emsg) = (ErrorResult emsg)"

(* blocks need cleanup of variable scopes *)
(* NB: mode handling is done in evalYulStatements. *)
| "evalYulStatement (YulBlock sl) (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some mode) None ((SeBlock sl) # cont)"
| "evalYulStatement (YulBlock sl) _ =
    (ErrorResult (STR ''invalid eval context (YulBlock)''))"
    
(* function defs handled in a separate pass *)
| "evalYulStatement (YulFunctionDefinitionStatement _)
                    (YulResult G L F (Some mode) _ cont) =
  YulResult G L F (Some mode) None cont"
| "evalYulStatement (YulFunctionDefinitionStatement _) _ =
    ErrorResult (STR ''invalid eval context (YulFunctionDefinition)'')"

(* function calls *)
| "evalYulStatement (YulFunctionCallStatement fc)
    (YulResult G L F (Some mode) _ cont) =
      YulResult G L F (Some mode) None (SeExpr (YulFunctionCallExpression fc) # cont)"
| "evalYulStatement (YulFunctionCallStatement fc) _ =
    (ErrorResult (STR ''invalid eval context (YulFunctionCallExpression)''))"

(* variable declaration/definition *)
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration names None))
    (YulResult G (L#Lt) F (Some mode) _ cont) =
    (case put_values L (strip_id_types names) (List.replicate (length names) defaultValue) of
      None \<Rightarrow> ErrorResult (STR ''should be dead code'')
      | Some L1 \<Rightarrow> YulResult G (L1#Lt) F (Some mode) None cont)"
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration names (Some expr)))
    (YulResult G L F (Some mode) _ cont) =
      YulResult G L F (Some mode) None
        (SeStatement (YulAssignmentStatement (YulAssignment (strip_id_types names) expr))#cont)"
| "evalYulStatement
    (YulVariableDeclarationStatement (YulVariableDeclaration _ _)) _ =
      ErrorResult (STR ''invalid eval context (YulVariableDeclaration)'')"

(* assignment *)
| "evalYulStatement
    (YulAssignmentStatement (YulAssignment ids expr))
    (YulResult G L F (Some mode) _ cont) =
      YulResult G L F (Some mode) None (SeExpr expr # SeFinishAssign ids # cont)"
| "evalYulStatement
    (YulAssignmentStatement _) _ =
      ErrorResult (STR ''invalid eval context (YulAssignmentStatement)'')"

(* if *)
| "evalYulStatement
    (YulIf cond body) (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some mode) None
      (SeExpr cond # SeFinishIf body # cont)"
| "evalYulStatement (YulIf _ _) _ = ErrorResult (STR ''invalid eval context (YulIf)'')"

(* for loops with empty pre *)
| "evalYulStatement
    (YulForLoop [] cond post body) (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some mode) None
      (SeExpr cond # SeFinishForLoop cond post body # cont)"
(* for loop with non empty pre *)
(* note that pre uses SeStatements because we need its values to be accessible inside
   of the loop's inner scope. we could also handle the check that functions cannot
   occur here (or do it as a syntactic check, already implemented in YulSemantics.thy *)
(* TODO: this doesn't correctly handle leave/continue/break. *)
| "evalYulStatement
    (YulForLoop pre cond post body) (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some mode) None
      (SeEnterBlock [] # SeStatements pre # (SeStatement (YulForLoop [] cond post body)) 
        # SeExitBlock # cont)"
| "evalYulStatement
    (YulForLoop _ _ _ _) _ =
    ErrorResult (STR ''invalid eval context (YulForLoop)'')"

(* switch *)
| "evalYulStatement (YulSwitch cond cases) (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some mode) None
      (SeExpr cond # SeFinishSwitch cases None # cont)"
| "evalYulStatement (YulSwitch _ _) _ =
    ErrorResult (STR ''invalid eval context (YulSwitch)'')"

(* break *)
| "evalYulStatement YulBreak (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some Break) None cont"
| "evalYulStatement YulBreak _ =
    ErrorResult (STR ''invalid eval context (YulBreak)'')"

(* continue *)
| "evalYulStatement YulContinue (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some Continue) None cont"
| "evalYulStatement YulContinue _ =
    ErrorResult (STR ''invalid eval context (YulContinue)'')"

(* leave *)
| "evalYulStatement YulLeave (YulResult G L F (Some mode) _ cont) =
    YulResult G L F (Some Leave) None cont"
| "evalYulStatement YulLeave _ =
    ErrorResult (STR ''invalid eval context (YulLeave)'')"

(* sequencing Yul statements
   TODO: need to split this into an initial and recursive version
   initial version must also call gather *)
fun evalYulStatements :: "YulStatement list \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulStatements [] (YulResult G L F (Some mode) _ cont) =
   YulResult G L F (Some mode) None cont"
| "evalYulStatements (s#st) (YulResult G L F (Some Regular) _ cont) =
   YulResult G L F (Some Regular) None ((SeStatement s)#(SeStatements st)#cont)"
| "evalYulStatements (s#st) (YulResult G L F (Some notreg) _ cont) =
   YulResult G L F (Some notreg) None cont"
| "evalYulStatements _ _ =
   ErrorResult (STR ''invalid eval context (statement-cons)'')"

(* where/how do enter/exit block go? *)
fun evalYulBlock :: "YulStatement list \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulBlock sts (YulResult G L F m x cont) =
  YulResult G L F m x (SeEnterBlock sts # SeStatements sts # SeExitBlock # cont)"
| "evalYulBlock _ _ =
  ErrorResult (STR ''invalid eval context (evalYulBlock)'')"

fun evalYulExpression ::
"YulExpression \<Rightarrow> ('g, 'v) result \<Rightarrow>
  ('g, 'v) result" where
"evalYulExpression _ (ErrorResult emsg) = (ErrorResult emsg)"
| "evalYulExpression (YulIdentifier i) (YulResult G (L#Lt) F m (Some vs) cont) =
   (case (L i) of
        None \<Rightarrow> ErrorResult (STR ''Undeclared variable '' @@ i)
        | Some v \<Rightarrow> YulResult G (L#Lt) F m (Some (vs @ [v])) cont)"
| "evalYulExpression (YulIdentifier i) (YulResult _ _ _ _ _ _) =
    ErrorResult (STR ''no variable context (identifier evaluation)'')"
| "evalYulExpression (YulLiteralExpression (YulLiteral value type)) (YulResult G L F m vs cont) =
   (case (parseLiteral value) of
      None \<Rightarrow> ErrorResult (STR ''Bad literal '' @@ value)
      | Some v \<Rightarrow> 
        (case vs of
          None \<Rightarrow> YulResult G L F m (Some [v]) cont
          | Some vs' \<Rightarrow> YulResult G L F m (Some (vs' @ [v])) cont))"
| "evalYulExpression (YulFunctionCallExpression (YulFunctionCall name args)) 
                     (YulResult G L F m vs cont)  =
    YulResult G L F m vs (SeExprs args # SeEnterFunctionCall name # SeExitFunctionCall name # cont)"


(* evaluating multiple Yul expressions and concatenating the results
   TODO: this is probably too permissive w/r/t function argument arities *)
fun evalYulExpressions :: "YulExpression list \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulExpressions [] (YulResult G L F m None cont) =
  (YulResult G L F m (Some []) cont)"
| "evalYulExpressions [] (YulResult G L F m (Some vs) cont) =
  (YulResult G L F m (Some vs) cont)"
| "evalYulExpressions (e#es) (YulResult G L F m vs cont) =
  (YulResult G L F m vs (SeExpr e # SeExprs es # cont))"
| "evalYulExpressions _ _ = 
   ErrorResult (STR ''invalid eval context (expr-cons)'')"

(* need to gather funs at top of any compound statement.
   but this means we need to do the recursion on statement sequences differently. *)
fun dispatchYulStep :: "stackEl \<Rightarrow> ('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"dispatchYulStep (SeStatement s) r = evalYulStatement s r"
| "dispatchYulStep (SeStatements s) r = evalYulStatements s r"
| "dispatchYulStep (SeExpr e) r = evalYulExpression e r"
| "dispatchYulStep (SeExprs e) r = evalYulExpressions e r"
| "dispatchYulStep (SeBlock sts) r = evalYulBlock sts r"

| "dispatchYulStep (SeEnterBlock sts) (YulResult G L F m vs cont) =
    (let L' = (case L of [] \<Rightarrow> [local_empty] | (Lh # Lt) \<Rightarrow> Lh#L) in
     (let F' = (case F of [] \<Rightarrow> [local_empty] | (Fh # Ft) \<Rightarrow> Fh#F) in
      gatherYulFunctions sts (YulResult G L' F' m vs cont)))"
| "dispatchYulStep (SeEnterBlock _) _ =
   ErrorResult (STR ''Bad state (dispatching SeEnterBlock)'')"

| "dispatchYulStep (SeExitBlock) (YulResult G (L1#L2#L) (Fh#F) m vs cont) =
   YulResult G ((restrict L1 L2)#L) F m vs cont"
| "dispatchYulStep (SeExitBlock) _ =
   ErrorResult (STR ''Bad state (dispatching SeExitBlock)'')"

| "dispatchYulStep (SeFinishAssign ids) (YulResult G (Lh#L) F m (Some vs) cont) =
    (case put_values Lh ids (vs) of
      None \<Rightarrow> ErrorResult (STR ''bad assignment arity'')
      | Some L1 \<Rightarrow> YulResult G (L1#L) F m None cont)"
| "dispatchYulStep (SeFinishAssign _) _ =
   ErrorResult (STR ''Bad state (dispatching SeFinishAssign)'')"

| "dispatchYulStep (SeFinishIf sts) (YulResult G L F m (Some [vh]) cont) =
    (if isTruthy vh then YulResult G L F m None (SeBlock sts # cont)
     else YulResult G L F m None cont)"
| "dispatchYulStep (SeFinishIf _) _ =
   ErrorResult (STR ''Bad state (dispatching SeFinishIf)'')"

| "dispatchYulStep (SeFinishForLoop cond post body) (YulResult G L F m (Some [vh]) cont) =
    (if isTruthy vh then
      YulResult G L F m None (SeBlock body # SeExpr cond # SeFinishForLoop cond post body # cont)
     else
      YulResult G L F m None ((SeBlock post)#cont))"
| "dispatchYulStep (SeFinishForLoop _ _ _) _ =
   ErrorResult (STR ''Bad state (dispatching SeFinishForLoop)'')"

| "dispatchYulStep (SeFinishSwitch [] None) _ =
  ErrorResult (STR ''No matching switch case and no default'')"
| "dispatchYulStep (SeFinishSwitch [] (Some dfl)) (YulResult G L F m (Some [vh]) cont) =
  YulResult G L F m None (SeBlock dfl # cont)"
| "dispatchYulStep (SeFinishSwitch ((YulSwitchCase None body)#ct) None) 
                                   (YulResult G L F m x cont) =
    (YulResult G L F m x ((SeFinishSwitch ct (Some body))#cont))"
| "dispatchYulStep (SeFinishSwitch ((YulSwitchCase None body)#ct) (Some _))
                                   (YulResult  _ _ _ _ _ _) =
    ErrorResult (STR ''Multiple default cases (SeFinishSwitch)'')"
| "dispatchYulStep (SeFinishSwitch ((YulSwitchCase (Some (YulLiteral t v)) body)#ct) d)
                   (YulResult G L F m (Some [vh]) cont) =
    (case parseLiteral v  of
      None \<Rightarrow> ErrorResult (STR ''Bad literal '' @@ v)
      | Some vlit \<Rightarrow>
          (if vlit = vh
            then YulResult G L F m None (SeBlock body # cont)
            else YulResult G L F m None (SeFinishSwitch ct d # cont)))"

| "dispatchYulStep (SeFinishSwitch _ _) _ =
    ErrorResult (STR ''Bad state (dispatching SeFinishSwitch)'')"

(* set up new local state with arguments and return values, then call *)
| "dispatchYulStep (SeEnterFunctionCall f) (YulResult G (Lh#Lt) (Fh#Ft) m (Some vs) cont) =
   (case (Fh f) of
    None \<Rightarrow> ErrorResult (STR ''Undefined function (entering) '' @@ f)
    | Some (YulFunctionSig argNames rets body) \<Rightarrow>
      (case put_values Lh (strip_id_types argNames) vs of
       None \<Rightarrow> ErrorResult (STR ''Bad function argument arity'')
       | Some Lh' \<Rightarrow>
        (case put_values Lh' 
          (strip_id_types rets)
          (List.replicate (length rets) defaultValue) of
            None \<Rightarrow> ErrorResult (STR ''Should be dead code'')
            | Some Lh'' \<Rightarrow> 
              (YulResult G (Lh''#Lh#Lt) (Fh#Ft) m None ((SeBlock body) # cont)))))"
| "dispatchYulStep (SeEnterFunctionCall _) _ =
   ErrorResult (STR ''Bad state (dispatching SeEnterFunctionCall)'')"

| "dispatchYulStep (SeExitFunctionCall f) (YulResult G (Lh#Lt) (Fh#Ft) m _ cont) =
   (case (Fh f) of
    None \<Rightarrow> ErrorResult (STR ''Undefined function (exiting) '' @@ f)
    | Some (YulFunctionSig _ rets _) \<Rightarrow>
      (case get_values Lh (strip_id_types rets) of
        None \<Rightarrow> ErrorResult (STR ''Return arity mismatch on exit; should be dead code'')
        | Some vs \<Rightarrow>
          (YulResult G Lt (Fh#Ft) m (Some vs) cont)))"
| "dispatchYulStep (SeExitFunctionCall _) _ =
   ErrorResult (STR ''Bad state (dispatching SeExitFunctionCall)'')"

fun evalYulStep :: "('g, 'v) result \<Rightarrow> ('g, 'v) result" where
"evalYulStep (YulResult G L F m x []) = (YulResult G L F m x [])"
| "evalYulStep (YulResult G L F m x (ch#ct)) =
    dispatchYulStep ch (YulResult G L F m x (ct))"
| "evalYulStep r = r"

fun evalYul' :: "('g, 'v) result \<Rightarrow> int \<Rightarrow> ('g, 'v) result" where
"evalYul' r n =
  (if n \<le> 0 then r
   else evalYul' (evalYulStep r) (n - 1))"

fun evalYul :: "YulStatement \<Rightarrow> int \<Rightarrow> ('g, 'v) result" where
"evalYul s n =
  evalYul' (YulResult G0 [local_empty] [F0] (Some Regular) None [SeStatement s]) n"

fun evalYuls :: "YulStatement list \<Rightarrow> int \<Rightarrow> ('g, 'v) result" where
"evalYuls ss n =
  evalYul' (YulResult G0 [local_empty] [F0] (Some Regular) None [SeStatements ss]) n"

fun evalYulE :: "YulExpression \<Rightarrow> int \<Rightarrow> ('g, 'v) result" where
"evalYulE e n =
  evalYul' (YulResult G0 [local_empty] [F0] None (Some []) [SeExpr e]) n"

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