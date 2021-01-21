theory YulSemanticsSingleStep imports "YulSemanticsCommon"
begin

(* For functions: search through a list of locals
   (corresponding to successive scopes) *)
(* Perhaps we don't need this, going to see if we can do without *)

(* Idea: a "small-step" executable semantics, where we describe transitions
   in terms of small increments. *)

(* stack used to represent computation remaining after this step *)
(* need to handle block *)
datatype ('v, 't) StackEl =
  SeStatement "('v, 't) YulStatement"
  | SeStatements "('v, 't) YulStatement list"
  | SeExpr "('v, 't) YulExpression"
  | SeExprs "('v, 't) YulExpression list"
  (* Following a defunctionalization approach, these commands represent
     situations where we must run a subexpression during evaluation of an expression,
     and then resume *)
  (* SeBlock is used when we want to cause evaluation of a block from within the execution
     of a different instruction. This way we are never generating new statements from
     the execution of stack elements *)
  | SeBlock "('v, 't) YulStatement list"
  | SeEnterBlock "('v, 't) YulStatement list"
  | SeExitBlock
  | SeEnterFunctionCall "YulIdentifier"
  | SeExitFunctionCall "YulIdentifier"
  | SeBuiltin "YulIdentifier"
  | SeAssign "YulIdentifier list"
  | SeIf "('v, 't) YulStatement list"
  | SeForLoop "('v, 't) YulExpression" "('v, 't) YulStatement list" "('v, 't) YulStatement list"
  | SeSwitch "('v, 't) YulSwitchCase list" "('v, 't) YulStatement list option"
(*
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
*)

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

record ('g, 'v, 't) result =
  "('g, 'v, 't) YulSemanticsCommon.result" +
  cont :: "('v, 't) StackEl list"

type_synonym ('g, 'v, 't) YulResult =
  "('g, 'v, 't, \<lparr>cont :: ('v, 't) StackEl list\<rparr>) YulResult"

(* TODO: review the way mode is being threaded *)
(* TODO: some of the places where we are swapping between "yul expression states"
   (that contain a list of accumulated variables) and "yul statement states"
   (that don't, but that do have a mode) are incorrect here. *)
fun evalYulStatement ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulStatement \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
  ('g, 'v, 't) YulResult" where

"evalYulStatement _ _ (ErrorResult emsg x) = (ErrorResult emsg x)"

(* blocks need cleanup of variable scopes *)
(* NB: mode handling is done in evalYulStatements. *)
| "evalYulStatement _ (YulBlock sl) (YulResult r) =
    YulResult (r \<lparr> cont := (SeBlock sl # cont r) \<rparr>)"

(*
| "evalYulStatement _ (YulBlock sl) (YulResult r) =
    YulResult (r \<lparr> cont := (SeEnterBlock sl # 
                           (SeStatements sl) #
                            SeExitBlock  # cont r) \<rparr>)"
*)
(* function defs handled in a separate pass *)
| "evalYulStatement _ (YulFunctionDefinitionStatement _) (YulResult r) =
(YulResult r)"

(* function calls *)
| "evalYulStatement _ (YulFunctionCallStatement fc) (YulResult r) =
       YulResult (r \<lparr> cont := SeExpr (YulFunctionCallExpression fc)#cont r\<rparr>)"

(* variable declaration/definition *)
| "evalYulStatement D
    (YulVariableDeclarationStatement (YulVariableDeclaration names None)) (YulResult r) =
    (case locals r of
      [] \<Rightarrow> ErrorResult (STR ''empty local value state stack'') (Some r)
      | L#Lt \<Rightarrow>
      (case put_values L (strip_id_types names) (List.replicate (length names) (default_val D)) of
        None \<Rightarrow> ErrorResult (STR ''arity mismatch in var declaration (should be dead code)'')
                            (Some r)
        | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1#Lt \<rparr>)))"
| "evalYulStatement _
    (YulVariableDeclarationStatement (YulVariableDeclaration names (Some expr)))
    (YulResult r) =
    (YulResult (r \<lparr> cont := SeStatement (YulAssignmentStatement
                                        (YulAssignment (strip_id_types names) expr))#cont r\<rparr>))"

(* assignment *)
| "evalYulStatement _
    (YulAssignmentStatement (YulAssignment ids expr))
    (YulResult r) =
      YulResult (r \<lparr> cont := SeExpr expr # 
                             SeAssign ids # cont r \<rparr>)"

(* if *)
| "evalYulStatement _
    (YulIf cond body) (YulResult r) =
    YulResult (r \<lparr> cont := SeExpr cond # SeIf body # cont r \<rparr>)"

(* for loops with empty pre *)
| "evalYulStatement _
    (YulForLoop [] cond post body) (YulResult r) =
    YulResult (r \<lparr> cont :=
      (SeExpr cond # SeForLoop cond post body # cont r)\<rparr>)"
(* for loop with non empty pre *)
(* note that pre uses SeStatements because we need its values to be accessible inside
   of the loop's inner scope. we could also handle the check that functions cannot
   occur here (or do it as a syntactic check, already implemented in YulSemantics.thy *)
(* TODO: this doesn't correctly handle leave/continue/break. *)
(* here we rely on a syntactic check to ensure functions are not defined
   in the "pre" (init) section of the loop" *)
| "evalYulStatement _
    (YulForLoop pre cond post body) (YulResult r) =
    YulResult (r \<lparr> cont := 
      (SeEnterBlock [] # SeStatements pre # (SeStatement (YulForLoop [] cond post body)) 
        # SeExitBlock # cont r)\<rparr>)"

(* switch *)
| "evalYulStatement _ (YulSwitch cond cases) (YulResult r) =
    YulResult (r \<lparr> cont := (SeExpr cond # SeSwitch cases None # cont r )\<rparr>)"

(* break *)
| "evalYulStatement _ YulBreak (YulResult r) =
    YulResult (r \<lparr> mode := Break \<rparr>)"

(* continue *)
| "evalYulStatement _ YulContinue (YulResult r) =
    YulResult (r \<lparr> mode := Continue \<rparr>)"

(* leave *)
| "evalYulStatement _ YulLeave (YulResult r) =
    YulResult (r \<lparr> mode := Leave \<rparr>)"

(* sequencing Yul statements
   TODO: need to split this into an initial and recursive version
   initial version must also call gather *)
fun evalYulStatements :: "('g, 'v, 't) YulDialect \<Rightarrow>
                          ('v, 't) YulStatement list \<Rightarrow>
                          ('g, 'v, 't) YulResult \<Rightarrow>
                          ('g, 'v, 't) YulResult" where
"evalYulStatements _ _ (ErrorResult e x) = ErrorResult e x"
| "evalYulStatements _ [] (YulResult r) = YulResult r"
| "evalYulStatements _ (s#st) (YulResult r) =
  (case mode r of
    Regular \<Rightarrow> YulResult (r \<lparr> cont := ((SeStatement s)#(SeStatements st)#cont r)\<rparr>)
    | _ \<Rightarrow> YulResult r)"

(* where/how do enter/exit block go? *)
fun evalYulBlock :: "('g, 'v, 't) YulDialect \<Rightarrow>
                     ('v, 't) YulStatement list \<Rightarrow>
                     ('g, 'v, 't) YulResult \<Rightarrow>
                     ('g, 'v, 't) YulResult" where
"evalYulBlock _ _ (ErrorResult e x) = ErrorResult e x"
| "evalYulBlock _ sts (YulResult r) =
    YulResult (r \<lparr> cont :=  (SeEnterBlock sts # SeStatements sts # SeExitBlock # cont r)\<rparr>)"

fun evalYulExpression ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulExpression \<Rightarrow>
 ('g, 'v, 't) YulResult \<Rightarrow>
 ('g, 'v, 't) YulResult" where
"evalYulExpression _ _ (ErrorResult e x) = (ErrorResult e x)"
| "evalYulExpression _ (YulIdentifier i) (YulResult r) =
  (case locals r of
    [] \<Rightarrow> ErrorResult (STR ''Empty locals environment stack'') (Some r)
    | (L#Lt) \<Rightarrow>
       (case (L i) of
          None \<Rightarrow> ErrorResult (STR ''Undeclared variable '' @@ i) (Some r)
          | Some v \<Rightarrow> YulResult (r \<lparr> stack := v # (stack r)\<rparr>)))"
| "evalYulExpression _ (YulLiteralExpression (YulLiteral value type)) (YulResult r) =
   YulResult (r \<lparr> stack := value # stack r \<rparr>)"
| "evalYulExpression _ (YulFunctionCallExpression (YulFunctionCall name args)) 
                       (YulResult r)  =
    (case funs r of
      [] \<Rightarrow> ErrorResult (STR ''Empty function context during function expression eval'') (Some r)
      | Fh#Ft \<Rightarrow>
      (case Fh name of
        None \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ name) (Some r)
        | Some (YulFunctionSig _ _ (YulBuiltin _)) \<Rightarrow>
          YulResult (r \<lparr> cont := (SeExprs args # SeBuiltin name # cont r)\<rparr>)
        | Some (YulFunctionSig _ _ (YulFunction _)) \<Rightarrow>
            YulResult (r \<lparr> cont := (SeExprs args # SeEnterFunctionCall name # 
                                    SeExitFunctionCall name # cont r) \<rparr>)))"

(* evaluating multiple Yul expressions and concatenating the results
   TODO: this is probably too permissive w/r/t function argument arities
   however we believe this can be resolved with a static check. *)
fun evalYulExpressions :: "('g, 'v, 't) YulDialect \<Rightarrow>
                           ('v, 't) YulExpression list \<Rightarrow> 
                           ('g, 'v, 't) YulResult \<Rightarrow>
                           ('g, 'v, 't) YulResult" where
"evalYulExpressions _ _ (ErrorResult e x) = ErrorResult e x"
| "evalYulExpressions _ [] (YulResult r) =
   (YulResult r)"
| "evalYulExpressions _ (e#es) (YulResult r) =
  (YulResult (r \<lparr> cont := (SeExpr e # SeExprs es # cont r)\<rparr>))"

fun dispatchYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow>
                        ('v, 't) StackEl \<Rightarrow> 
                        ('g, 'v, 't) YulResult \<Rightarrow>
                        ('g, 'v, 't) YulResult" where
"dispatchYulStep _ _ (ErrorResult e x) = ErrorResult e x"

| "dispatchYulStep D (SeStatement s) (YulResult r) = evalYulStatement D s (YulResult r)"
| "dispatchYulStep D (SeStatements s) (YulResult r) = evalYulStatements D s (YulResult r)"
| "dispatchYulStep D (SeExpr e) (YulResult r) = evalYulExpression D e (YulResult r)"
| "dispatchYulStep D (SeExprs es) (YulResult r) = evalYulExpressions D es (YulResult r)"

| "dispatchYulStep _ (SeBlock sts) (YulResult r) =
   (YulResult (r \<lparr> cont := SeEnterBlock sts # SeStatements sts # SeExitBlock # cont r \<rparr>))"

| "dispatchYulStep D (SeEnterBlock sts) (YulResult r) =
    (case locals r of
      [] \<Rightarrow> ErrorResult (STR ''Bad locals stack (dispatching SeEnterBlock)'') (Some r)
      | Lh#Lt \<Rightarrow>
      (case funs r of
        [] \<Rightarrow> ErrorResult (STR ''Bad funs stack (dispatching SeEnterBlock)'') (Some r)
        | Fh#Ft \<Rightarrow> gatherYulFunctions sts 
                    (YulResult (r \<lparr> locals := Lh#Lh#Lt, funs := Fh#Fh#Ft \<rparr>))))"

| "dispatchYulStep _ (SeExitBlock) (YulResult r) =
    (case locals r of
      (L1#L2#L) \<Rightarrow>
        (case funs r of
          Fh#F \<Rightarrow> YulResult (r \<lparr> locals := (restrict L1 L2)#L, funs := F \<rparr>)
          | _ \<Rightarrow> ErrorResult (STR ''Bad funs stack (dispatching SeExitBlock)'') (Some r))
      | _ \<Rightarrow> ErrorResult (STR ''Bad locals stack (dispatching SeExitBlock)'') (Some r))"

| "dispatchYulStep _ (SeAssign ids) (YulResult r) =
    (case locals r of
      [] \<Rightarrow> ErrorResult (STR ''Bad locals stack (dispatching SeAssign)'') (Some r)
      | Lh#L \<Rightarrow>
      (case put_values Lh ids (rev (take (length ids) (stack r))) of
        None \<Rightarrow> ErrorResult (STR ''bad assignment arity'') (Some r)
        | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1#L, stack := (drop (length ids) (stack r))\<rparr>)))"

| "dispatchYulStep D (SeIf sts) (YulResult r) =
    (case stack r of
      [] \<Rightarrow> ErrorResult (STR ''empty stack (dispatching SeIf)'') (Some r)
      | vh#vs \<Rightarrow>
      (if is_truthy D vh then 
        YulResult (r \<lparr> stack := vs, cont := (SeBlock sts) # (cont r)\<rparr>)
       else YulResult (r \<lparr> stack := vs \<rparr>)))"

| "dispatchYulStep D (SeForLoop cond post body) (YulResult r) =
    (case stack r of
      [] \<Rightarrow> ErrorResult (STR ''empty stack (dispatching SeForLoop)'') (Some r)
      | vh#vs \<Rightarrow>
      (if is_truthy D vh then
        YulResult (r \<lparr> stack := vs
                     , cont := (SeBlock body # SeExpr cond # 
                                SeForLoop cond post body # cont r) \<rparr>)
       else
        YulResult (r \<lparr> stack := vs, cont := ((SeBlock post)#cont r) \<rparr>)))"

| "dispatchYulStep _ (SeSwitch [] None) (YulResult r) =
  ErrorResult (STR ''No matching switch case and no default'') (Some r)"
| "dispatchYulStep _ (SeSwitch [] (Some dfl)) (YulResult r) =
    (case stack r of
      [] \<Rightarrow> ErrorResult (STR ''empty stack (dispatching SeSwitch)'') (Some r)
      | vh#vs \<Rightarrow> YulResult (r \<lparr> stack := vs, cont := SeBlock dfl # cont r \<rparr>))"
| "dispatchYulStep _ (SeSwitch ((YulSwitchCase None body)#ct) None)
                               (YulResult r) =
    (YulResult (r \<lparr> cont := ((SeSwitch ct (Some body))#cont r) \<rparr>))"
| "dispatchYulStep _ (SeSwitch ((YulSwitchCase None body)#ct) (Some _))
                               (YulResult  r) =
    ErrorResult (STR ''Multiple default cases (SeSwitch)'') (Some r)"
| "dispatchYulStep _ (SeSwitch ((YulSwitchCase (Some (YulLiteral vlit t)) body)#ct) d)
                     (YulResult r) =
    (case stack r of
      [] \<Rightarrow> ErrorResult (STR ''empty stack (dispatching SeSwitch)'') (Some r)
      | vh#vs \<Rightarrow>
      (if vlit = vh
        then YulResult (r \<lparr> stack := vs, cont := (SeBlock body) # cont r \<rparr>)
        else YulResult (r \<lparr> cont := (SeSwitch ct d # cont r) \<rparr>)))"

(* set up new local state with arguments and return values, then call *)
| "dispatchYulStep D (SeEnterFunctionCall f) (YulResult r) =
    (case locals r of
      [] \<Rightarrow> ErrorResult (STR ''empty locals stack (dispatching SeEnterFunctionCall)'') (Some r)
      | Lh#Lt \<Rightarrow>
      (case funs r of
        [] \<Rightarrow> ErrorResult (STR ''empty function stack (dispatching SeEnterFunctionCall)'') (Some r)
        | Fh#Ft \<Rightarrow>
        (case Fh f of
          Some (YulFunctionSig argNames rets (YulFunction body)) \<Rightarrow>
            (case put_values Lh (strip_id_types argNames)
                                (rev (take (length argNames) (stack r))) of
             None \<Rightarrow> ErrorResult (STR ''Bad function argument arity'') (Some r)
             | Some Lh' \<Rightarrow>
              (case put_values Lh' 
                (strip_id_types rets)
                (List.replicate (length rets) (default_val D)) of
                  None \<Rightarrow> ErrorResult (STR ''Should be dead code'') (Some r)
                  | Some Lh'' \<Rightarrow> 
                    (YulResult (r \<lparr> locals := (Lh''#Lh#Lt)
                                  , stack := drop (length argNames) (stack r)
                                  , cont := ((SeBlock body) # cont r) \<rparr>))))
          | _ \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ f) (Some r))))"

(* TODO: double check returning onto stack is correct here (I am pretty sure it is) *)
| "dispatchYulStep _ (SeExitFunctionCall f) (YulResult r) =
  (case locals r of
    [] \<Rightarrow> ErrorResult (STR ''empty locals stack (dispatching SeExitFunctionCall)'') (Some r)
    | Lh#Lt \<Rightarrow>
    (case funs r of
      [] \<Rightarrow> ErrorResult (STR ''empty function stack (dispatching SeExitFunctionCall)'') (Some r)
      | Fh#Ft \<Rightarrow>
      (case Fh f of
        Some (YulFunctionSig _ rets (YulFunction _)) \<Rightarrow>
          (case get_values Lh (strip_id_types rets) of
            None \<Rightarrow> ErrorResult (STR ''Return arity mismatch on exit; should be dead code'') (Some r)
            | Some vs \<Rightarrow> YulResult (r \<lparr> locals := Lt, stack := (rev vs) @ stack r \<rparr>))
         | _ \<Rightarrow> ErrorResult (STR ''Undefined function (exiting) '' @@ f) (Some r))))"

| "dispatchYulStep _ (SeBuiltin f) (YulResult r) =
    (case locals r of
      [] \<Rightarrow> ErrorResult (STR ''empty locals stack (dispatching SeBuiltin)'') (Some r)
      | Lh#Lt \<Rightarrow>
      (case funs r of
        [] \<Rightarrow> ErrorResult (STR ''empty function stack (dispatching SeBuiltin)'') (Some r)
        | Fh#Ft \<Rightarrow>
        (case Fh f of
          Some (YulFunctionSig argNames rets (YulBuiltin f_impl)) \<Rightarrow>
            (case f_impl (global r) (rev (take (length argNames) (stack r))) of
              Inr msg \<Rightarrow> ErrorResult (STR ''Failure in builtin '' @@ (f @@
                         (STR '' with message '' @@ msg))) (Some r)
              | Inl (G', vs') \<Rightarrow>
                YulResult (r \<lparr> global := G', stack := vs' @ drop (length argNames) (stack r) \<rparr>))
          | _ \<Rightarrow> ErrorResult (STR ''Undefined builtin '' @@ f) (Some r))))"


fun evalYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"evalYulStep D (YulResult r)=
  (case cont r of
    [] \<Rightarrow> YulResult r
    | ch#ct \<Rightarrow> dispatchYulStep D ch (YulResult (r \<lparr> cont := ct \<rparr>)))"
| "evalYulStep _ r = r"

fun evalYul' :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) YulResult \<Rightarrow> 
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYul' D (YulResult r) n =
  (if n \<le> 0 then (YulResult r)
   else evalYul' D (evalYulStep D (YulResult r)) (n - 1))"
| "evalYul' _ (ErrorResult msg x) _ =
    ErrorResult msg x"

fun yulInit :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v,'t) result" where
"yulInit D = \<lparr> global = init_state D
             , locals = [locals_empty]
             , stack = []
             , funs = [builtins D]
             , mode = Regular
             , cont = []\<rparr>"

fun evalYul :: "('g, 'v, 't) YulDialect \<Rightarrow>
                ('v, 't) YulStatement \<Rightarrow>
                int \<Rightarrow>
                ('g, 'v, 't) YulResult" where
"evalYul D s n =
  evalYul' D (YulResult ((yulInit D) \<lparr> cont := [SeStatement s] \<rparr>)) n"

fun evalYuls :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulStatement list \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYuls D ss n =
  evalYul' D (YulResult ((yulInit D) \<lparr> cont := [SeStatements ss] \<rparr>)) n"

fun evalYulE :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulExpression \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYulE D e n =
  evalYul' D (YulResult ((yulInit D) \<lparr> cont := [SeExpr e] \<rparr>)) n"

end