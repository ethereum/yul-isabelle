theory YulSemanticsSingleStep imports "YulSemanticsCommon"
begin

(* TODOS:
   - change locals representation to state map + visible vars
   - add a function frames component to state (will capture locals + value stack)

*)

(* For functions: search through a list of locals
   (corresponding to successive scopes) *)
(* Perhaps we don't need this, going to see if we can do without *)

(* Idea: a "small-step" executable semantics, where we describe transitions
   in terms of small increments. *)

(* stack used to represent computation remaining after this step *)
(* 'v locals parameter handles scope restriction 
   (i.e. what locals looked like in terms of declared vars,
    before this expression was entered)
   'v function_sig locals is the same, but for function sigs
   perhaps we also need one for resetting the value stack
*)
datatype ('g, 'v, 't) StackEl =
  EnterStatement "('v, 't) YulStatement"
  (* on statement exit, we restore the old function scope and restrict
     the locals scope to forget block-local variables 

     on function exit, we restore the old function scope, push return values,
     and restore (not restrict) the old locals scope.
     the YulIdentifier list option distinguishes these cases
*)
  | ExitStatement "('v, 't) YulStatement" "'v locals" "('g, 'v, 't) function_sig locals" "(YulIdentifier list * 'v list) option"
  | EnterExpression "('v, 't) YulExpression"
  (* on expression exit, we restore the old stack *)
  | ExitExpression "('v, 't) YulExpression" "'v list"
(*  | ExitScope "vset" *)

type_synonym errf = "String.literal option"

record ('g, 'v, 't) result =
  "('g, 'v, 't) YulSemanticsCommon.result" +
  cont :: "('g, 'v, 't) StackEl list"

type_synonym ('g, 'v, 't) YulResult =
  "('g, 'v, 't, \<lparr>cont :: ('g, 'v, 't) StackEl list\<rparr>) YulResult"

(* we need to have a stack element for cleaning up fun ctxt *)


fun evalYulStatement ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulStatement \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
  ('g, 'v, 't) YulResult" where

"evalYulStatement _ _ (ErrorResult emsg x) = (ErrorResult emsg x)"

| "evalYulStatement D st (YulResult r) =
   YulResult (r \<lparr> cont := EnterStatement st # ExitStatement st (locals r) (funs r) None # cont r \<rparr>)"

fun evalYulExpression ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulExpression \<Rightarrow>
 ('g, 'v, 't) YulResult \<Rightarrow>
 ('g, 'v, 't) YulResult" where
"evalYulExpression _ _ (ErrorResult e x) = (ErrorResult e x)"
| "evalYulExpression _ e (YulResult r) =
   YulResult (r \<lparr> cont := EnterExpression e # ExitExpression e (vals r) # cont r \<rparr>)"

(* StackEl list is always the same as the YulResult's continuation parameter
   this makes termination easy to prove - there is definitely a more elegant way
    to express this though. *)

(* TODO: make sure that this is correctly handling function context. I believe
   ExitStatement (YulBlock []) is doing the right thing but we should be sure *)

fun yulBreak :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulResult \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"yulBreak D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulBreak D [] (YulResult r) = ErrorResult (STR ''Break outside loop body'') (Some r)"
| "yulBreak D (EnterExpression cond1 # ExitExpression cond2 _ # 
      ExitStatement (YulForLoop pre cond post body) c' f' _ # ct) (YulResult r) =
      YulResult (r \<lparr> cont := ExitStatement (YulBlock []) c' f' None # ct \<rparr>)"
| "yulBreak D (ch#ct) (YulResult r) = yulBreak D ct (YulResult (r \<lparr> cont := ct \<rparr>))"

fun yulContinue :: "('g, 'v, 't) YulDialect \<Rightarrow>
                    ('g, 'v, 't) StackEl list \<Rightarrow>
                    ('g, 'v, 't) YulResult \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"yulContinue D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulContinue D [] (YulResult r) = ErrorResult (STR ''Continue outside loop body'') (Some r)"
| "yulContinue D (EnterExpression cond1 # ExitExpression cond2 v2 # 
      ExitStatement (YulForLoop pre cond post body) f' c' _ # ct)  (YulResult r) =
   YulResult (r \<lparr> cont := ((EnterExpression cond1 # ExitExpression cond2 v2 # 
      ExitStatement (YulForLoop pre cond post body) f' c' None # ct))\<rparr>)"
| "yulContinue D (ch#ct) (YulResult r) = yulContinue D ct (YulResult (r \<lparr> cont := ct \<rparr>))"

(* TODO: should we keep the exit from YulFunctionCallExpression here? *)
fun yulLeave :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulResult \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"yulLeave D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulLeave D [] (YulResult r) = ErrorResult (STR ''Leave outside function body'') (Some r)"
| "yulLeave D ((ExitExpression (YulFunctionCallExpression fc) v' )#ct) (YulResult r) =
   YulResult (r \<lparr> cont := ((ExitExpression (YulFunctionCallExpression fc) v')#ct) \<rparr>)"
| "yulLeave D (ch#ct) r = yulLeave D ct r"

fun evalYulEnterStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                              ('v, 't) YulStatement \<Rightarrow> 
                              ('g, 'v, 't) YulResult \<Rightarrow>
                              ('g, 'v, 't) YulResult"
  where
"evalYulEnterStatement _ _ (ErrorResult e msg) = ErrorResult e msg"

(* fun call \<Rightarrow> noop (delegate to expression) *)

| "evalYulEnterStatement D (YulAssignmentStatement (YulAssignment ids e)) (YulResult r) =
  YulResult (r \<lparr> cont := EnterExpression e # 
                         ExitExpression e (vals r) # cont r\<rparr>)"

| "evalYulEnterStatement D (YulVariableDeclarationStatement 
                           (YulVariableDeclaration ids (Some e))) (YulResult r) =
  YulResult (r \<lparr> cont := EnterExpression e # ExitExpression e (vals r) # cont r \<rparr>)"

| "evalYulEnterStatement D (YulIf cond body) (YulResult r) =
  YulResult (r \<lparr> cont := EnterExpression cond # ExitExpression cond (vals r) # cont r \<rparr>)"

| "evalYulEnterStatement D (YulSwitch cond cases) (YulResult r) =
  YulResult (r \<lparr> cont := EnterExpression cond # ExitExpression cond (vals r) # cont r \<rparr>)"

(* TODO: make sure we are handling the special case of pre correctly
   (we need to make sure that we are opening a special scope before pre,
    and closing it after post *)
| "evalYulEnterStatement D (YulForLoop pre cond post body) (YulResult r) = 
  YulResult (r \<lparr> cont := concat (map (\<lambda> s . [EnterStatement s, ExitStatement s (locals r) (funs r) None]) pre)
                           @ [EnterExpression cond, ExitExpression cond (vals r)] 
                           @ cont r \<rparr>)"

| "evalYulEnterStatement D (YulBlock sl) (YulResult r) =
  (case gatherYulFunctions (funs r) sl of
    Inr fbad \<Rightarrow> ErrorResult (STR ''Duplicate function declaration: '' @@ fbad) (Some r)
    | Inl F \<Rightarrow> YulResult (r \<lparr> funs := F \<rparr>))"

| "evalYulEnterStatement _ _ (YulResult r) = (YulResult r)"

(* helper functions for switch statements *)
fun getDefault ::
  "('v, 't) YulSwitchCase list \<Rightarrow> ('v, 't) YulSwitchCase option"
  where
"getDefault [] = None"
| "getDefault ((YulSwitchCase (Some _) _)#t) = getDefault t"
| "getDefault ((YulSwitchCase None body)#_) =
   Some (YulSwitchCase None body)"

fun nextCase ::
  "('v, 't) YulSwitchCase list \<Rightarrow> (('v, 't) YulSwitchCase option * ('v, 't) YulSwitchCase list)" where
"nextCase [] = (None, [])"
| "nextCase ((YulSwitchCase None body)#t) =
   (case nextCase t of
    (x, t') \<Rightarrow> (x, (YulSwitchCase None body)#t'))"
| "nextCase ((YulSwitchCase (Some c) body)#t) =
   (Some (YulSwitchCase (Some c) body), t)"
   


(* exit statement:
   - do actual statement effect
   - scoping clean-up
*)

(* should we always force an empty stack after a statement? *)
fun evalYulExitStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                             ('v, 't) YulStatement \<Rightarrow> 
                             'v locals \<Rightarrow>
                             ('g, 'v, 't) function_sig locals \<Rightarrow>
                             (YulIdentifier list * 'v list) option \<Rightarrow>
                             ('g, 'v, 't) YulResult \<Rightarrow>
                             ('g, 'v, 't) YulResult"
  where
"evalYulExitStatement _ _ _ _ _ (ErrorResult e msg) = ErrorResult e msg"

| "evalYulExitStatement D (YulAssignmentStatement (YulAssignment ids e)) _ _ _ (YulResult r) = 
  (case put_values (locals r) ids (rev (take (length ids) (vals r))) of
    None \<Rightarrow> ErrorResult (STR ''Arity mismatch (exiting assignment)'') (Some r)
    | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>))"

| "evalYulExitStatement D (YulVariableDeclarationStatement (YulVariableDeclaration ids exo)) _ _ _
                        (YulResult r) =
  (case exo of
    None \<Rightarrow>
      (case insert_values (locals r) (strip_id_types ids) (replicate (length ids) (default_val D)) of
        None \<Rightarrow> ErrorResult (STR ''Should be dead code (exiting variable declaration)'') (Some r)
        | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>))
    | Some _ \<Rightarrow>
        (case insert_values (locals r) (strip_id_types ids) (rev (take (length ids) (vals r))) of
          None \<Rightarrow> ErrorResult (STR ''Arity mismatch (exiting variable declaration)'') (Some r)
          | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>)))"

| "evalYulExitStatement D (YulIf cond body) _ _ _ (YulResult r) =
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then 
      YulResult (r \<lparr> vals := []
                   , cont := EnterStatement (YulBlock body) #
                             ExitStatement (YulBlock body) (locals r) (funs r) None # (cont r)\<rparr>)
     else YulResult (r \<lparr> vals := [] \<rparr>))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting if)'') (Some r))"

| "evalYulExitStatement D (YulSwitch exp scs) _ _ _ (YulResult r) =
  (case vals r of
    [vh] \<Rightarrow>
     (case nextCase scs of
      (None, _) \<Rightarrow>
        (case getDefault scs of
          Some (YulSwitchCase None body) \<Rightarrow>
            YulResult (r \<lparr> vals := []
                         , cont := EnterStatement (YulBlock body) #
                                   ExitStatement (YulBlock body) (locals r) (funs r) None #
                                   cont r \<rparr>)
          | _ \<Rightarrow> ErrorResult (STR ''No default switch case'') (Some r))
      | (Some (YulSwitchCase (Some (YulLiteral vcond _)) body), scs') \<Rightarrow>
        (if vh = vcond then
          YulResult (r \<lparr> vals := []
                         , cont := EnterStatement (YulBlock body) #
                                   ExitStatement (YulBlock body) (locals r) (funs r) None #
                                   cont r \<rparr>)
         else YulResult (r \<lparr> cont := ExitStatement (YulSwitch exp scs') (locals r) (funs r) None #
                                   cont r \<rparr>))
      | _ \<Rightarrow> ErrorResult (STR ''Should be dead code'') (Some r))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting switch statement)'') (Some r))"

(* we have already dealt with pre at this point *)
| "evalYulExitStatement D (YulForLoop pre cond post body) _ _ _ (YulResult r) = 
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then
      YulResult (r \<lparr> vals := []
                   , cont := (EnterStatement (YulBlock body) # 
                              ExitStatement (YulBlock body) (locals r) (funs r) None # 
                              EnterExpression cond # 
                              ExitExpression cond (vals r) #
                              ExitStatement (YulForLoop pre cond post body) (locals r) (funs r) None #
                              cont r) \<rparr>)
     else
       (YulResult (r \<lparr> vals := []
                     , cont := (EnterStatement (YulBlock post) #
                                              ExitStatement (YulBlock post) (locals r) (funs r) None # cont r) \<rparr>)))
     | _ \<Rightarrow> ErrorResult (STR ''Invalid value stack (exiting ForLoop i.e. entering body)'') (Some r))"

| "evalYulExitStatement D (YulFunctionCallStatement fc) _ _ _ (YulResult r) =
  (YulResult (r \<lparr> cont := EnterExpression (YulFunctionCallExpression fc) #
                          ExitExpression (YulFunctionCallExpression fc) (vals r)  #
                          cont r \<rparr>))"

| "evalYulExitStatement D YulBreak _ _ _ (YulResult r) =
   yulBreak D (cont r) (YulResult r)"

| "evalYulExitStatement D YulContinue _ _ _ (YulResult r) =
   yulContinue D (cont r) (YulResult r)"

| "evalYulExitStatement D YulLeave _ _ _ (YulResult r) =
   yulLeave D (cont r) (YulResult r) "

(* Exit from blocks that do not correspond to a function exit *)
| "evalYulExitStatement D (YulBlock sl) L F None (YulResult r) =
  (YulResult (r \<lparr> locals := restrict (locals r) L
                , funs := F \<rparr>))"

(* Exit from blocks corresponding to a function exit *)
| "evalYulExitStatement D (YulBlock sl) L F (Some (rets, old_vals)) (YulResult r) =
   (case get_values (locals r) rets of
    None \<Rightarrow> ErrorResult (STR ''Should be dead code (post-function cleanup)'') (Some r)
    | Some vs \<Rightarrow>
      (YulResult (r \<lparr> locals := L
                    , funs := F
                    , vals := rev vs @ old_vals  \<rparr>)))"


| "evalYulExitStatement _ _ _ _ _ (YulResult r) = (YulResult r)"

fun evalYulEnterExpression :: "('g, 'v, 't) YulDialect \<Rightarrow>
                               ('v, 't) YulExpression \<Rightarrow> 
                               ('g, 'v, 't) YulResult \<Rightarrow>
                               ('g, 'v, 't) YulResult"
  where
"evalYulEnterExpression _ _(ErrorResult e msg) = ErrorResult e msg"

| "evalYulEnterExpression D (YulFunctionCallExpression (YulFunctionCall name args)) (YulResult r) = 
   YulResult (r \<lparr> cont := concat (map (\<lambda> e . [EnterExpression e, ExitExpression e (vals r)]) args) @
                         cont r \<rparr>)"

| "evalYulEnterExpression _ _ (YulResult r) = YulResult r"

(* TODO: handle function exit/multiple-expression exit correctly *)
(* we also need to make sure we reset locals to empty state on function entry. *)
(* need to handle marshalling function arguments in/out correctly *)
(* function entry:
   - build an empty scope
   - parameters = pull from top of stack
   - returns = 0
   - empty stack
*)
(* function exit:
  - restore old stack, minus stack values used, plus returned values
*)
(* one idea here:
   - add a new continuation type
     (or, add a new set of arguments to existing continuation)
   - ok, so when we exit a block, we need to either
    (current things)
      - restrict locals
      - restore old funs
    (new things)
      - remap locals into returns
      - restore locals to what they were before function call
        (the issue is that we need to actually store those?)
*)

(*
\<lparr> f_sig_arguments = args
           , f_sig_rets = rets
           , f_sig_body = (YulBuiltin impl) \<rparr> 
*)

fun evalYulExitExpression :: "('g, 'v, 't) YulDialect \<Rightarrow>
                              ('v, 't) YulExpression \<Rightarrow> 
                              'v list \<Rightarrow>
                              ('g, 'v, 't) YulResult \<Rightarrow>
                              ('g, 'v, 't) YulResult"
  where
"evalYulExitExpression _ _ _ (ErrorResult e msg) = ErrorResult e msg"

(* for function case:
   - create new locals
     - empty; args get arg values; rets get 0
   - derive funs context
     - use visible names from fsig to restrict F
*)
(* TODO: for builtins we are not doing arity checking on returns *)
(* TODO: on return from function, restore vals (this must also go in exit statement *)
| "evalYulExitExpression D (YulFunctionCallExpression (YulFunctionCall name _)) old_vals (YulResult r) = 
   (case map_of (funs r) name of
    None \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ name) (Some r)
    | Some fsig \<Rightarrow>
      (case (f_sig_body fsig) of
       YulBuiltin impl \<Rightarrow>
          (case impl (global r) (rev (take (length (f_sig_arguments fsig)) (vals r))) of
            Inr err \<Rightarrow> ErrorResult (STR ''Error in builtin '' @@ (name @@ (STR '' : '' @@ err))) (Some r)
            | Inl (G', vals') \<Rightarrow>
              YulResult (r \<lparr> global := G', vals := rev vals' @ drop (length (f_sig_arguments fsig)) (vals r)  \<rparr>))
       | YulFunction sts \<Rightarrow>
          (case put_values (locals_empty) (strip_id_types (f_sig_arguments fsig)) (rev (take (length (f_sig_arguments fsig)) (vals r))) of
            None \<Rightarrow> ErrorResult (STR ''Argument arity mismatch for function '' @@ (name)) (Some r)
            | Some L1 \<Rightarrow> 
              (case put_values L1 (strip_id_types (f_sig_returns fsig)) (replicate (length (f_sig_returns fsig)) (default_val D)) of
                None \<Rightarrow>  ErrorResult (STR ''Name collision for returns in function '' @@ name) (Some r)
                | Some L2 \<Rightarrow>
                 YulResult (r \<lparr> locals := L2
                              , vals := []
                              , funs := restrict (funs r) (map (\<lambda> n . (n, ())) (f_sig_visible fsig))
                              , cont := EnterStatement (YulBlock sts) # 
                                        ExitStatement (YulBlock sts) (locals r) (funs r) (Some (strip_id_types (f_sig_returns fsig), old_vals)) # cont r \<rparr>)))))"

| "evalYulExitExpression D (YulIdentifier idn) old_vals (YulResult r) =
   (case map_of (locals r) idn of
    None \<Rightarrow> ErrorResult (STR ''Undefined variable '' @@ idn) (Some r)
    | Some v \<Rightarrow>
      YulResult (r \<lparr> vals := v # old_vals \<rparr>))"

| "evalYulExitExpression D (YulLiteralExpression (YulLiteral v _)) old_vals (YulResult r) =
   YulResult (r \<lparr> vals := v # old_vals \<rparr>)"


fun evalYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"evalYulStep D (YulResult r)=
  (case cont r of
    [] \<Rightarrow> YulResult r
    | (EnterStatement st)#ct \<Rightarrow> evalYulEnterStatement D st (YulResult (r \<lparr> cont := ct \<rparr>))
    | (ExitStatement st L F arg_o)#ct \<Rightarrow> evalYulExitStatement D st L F arg_o (YulResult (r \<lparr> cont := ct \<rparr>))
    | (EnterExpression e)#ct \<Rightarrow> evalYulEnterExpression D e (YulResult (r \<lparr> cont := ct \<rparr>))
    | (ExitExpression e vs)#ct \<Rightarrow> evalYulExitExpression D e vs (YulResult (r \<lparr> cont := ct \<rparr>))
)"
| "evalYulStep _ r = r"

(*
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

(* TODO: insert mode check logic at the beginning here, to make sure we stop running
   the body *)
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
            | Some vs \<Rightarrow> YulResult (r \<lparr> locals := Lt 
                                      , mode :=
                                        (case mode r of 
                                          Leave \<Rightarrow> Regular
                                          | _ \<Rightarrow> mode r)
                                      , stack := (rev vs) @ stack r \<rparr>))
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
*)
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
             , locals = locals_empty
             , vals = []
             , funs = builtins D
             , cont = []\<rparr>"

fun evalYul :: "('g, 'v, 't) YulDialect \<Rightarrow>
                ('v, 't) YulStatement \<Rightarrow>
                int \<Rightarrow>
                ('g, 'v, 't) YulResult" where
"evalYul D s n =
  (let r = yulInit D in
   evalYul' D (YulResult (r \<lparr> cont := [EnterStatement s, ExitStatement s (locals r) (funs r) None] \<rparr>)) n)"

fun evalYuls :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulStatement list \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYuls D ss n =
  (let r = yulInit D in
    evalYul' D (YulResult 
                  (r
                   \<lparr> cont := concat (map (\<lambda> s. [EnterStatement s, ExitStatement s (locals r) (funs r) None]) ss)\<rparr>)) 
                n)"

fun evalYulE :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulExpression \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYulE D e n =
  (let r = yulInit D in
  evalYul' D (YulResult (r \<lparr> cont := [EnterExpression e, ExitExpression e (vals r)] \<rparr>)) n)"

end