theory YulSemanticsSingleStep imports "YulSemanticsCommon"
begin


(* stack used to represent computation remaining after this step *)
datatype ('g, 'v, 't) StackEl =
  EnterStatement "('v, 't) YulStatement"
  (* on statement exit, we restore the old function scope and restrict
     the locals scope to forget block-local variables 

     on function exit, we restore the old function scope, push return values,
     and restore (not restrict) the old locals scope.
  *)
  | ExitStatement "('v, 't) YulStatement" "'v locals" "('g, 'v, 't) function_sig locals" 
  (* TODO: we may not need all the parameters we have for enter/exit function *)
  (* when entering functions, we remember the function signature and name
      *)

  | EnterFunctionCall "YulIdentifier" 
                      "('g, 'v, 't) function_sig"

(*
  | EnterFunctionCall "YulIdentifier" "('v, 't) YulExpression list" 
                      "'v list" 
                      "'v locals" "('g, 'v, 't) function_sig locals" 
                      "('g, 'v, 't) function_sig"
*)
  (* when exiting functions, we remember
     - function name
     - function argument expressions
     - old stack
     - old locals
     - old functions context
     - signature of function being called *)
  | ExitFunctionCall "YulIdentifier" "('v, 't) YulExpression list" 
                     "'v list" 
                     "'v locals" "('g, 'v, 't) function_sig locals" 
                     "('g, 'v, 't) function_sig"
  | Expression "('v, 't) YulExpression"


type_synonym errf = "String.literal option"

record ('g, 'v, 't) result =
  "('g, 'v, 't) YulSemanticsCommon.result" +
  cont :: "('g, 'v, 't) StackEl list"

type_synonym ('g, 'v, 't) YulResult =
  "('g, 'v, 't, \<lparr>cont :: ('g, 'v, 't) StackEl list\<rparr>) YulResult"


fun evalYulStatement ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulStatement \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
  ('g, 'v, 't) YulResult" where

"evalYulStatement _ _ (ErrorResult emsg x) = (ErrorResult emsg x)"

| "evalYulStatement D st (YulResult r) =
   YulResult (r \<lparr> cont := EnterStatement st # cont r \<rparr>)"


fun evalYulExpression ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulExpression \<Rightarrow>
 ('g, 'v, 't) YulResult \<Rightarrow>
 ('g, 'v, 't) YulResult" where
"evalYulExpression _ _  (ErrorResult e x) = (ErrorResult e x)"
| "evalYulExpression D (YulIdentifier idn) (YulResult r) =
   (case map_of (locals r) idn of
    None \<Rightarrow> ErrorResult (STR ''Undefined variable '' @@ idn) (Some r)
    | Some v \<Rightarrow>
      YulResult (r \<lparr> vals := v # vals r\<rparr>))"

| "evalYulExpression D (YulLiteralExpression (YulLiteral v _)) (YulResult r) =
   YulResult (r \<lparr> vals := v # vals r \<rparr>)"

| "evalYulExpression D (YulFunctionCallExpression (YulFunctionCall name args)) (YulResult r) =
   (case map_of (funs r) name of
    None \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ name) (Some r)
    | Some fsig \<Rightarrow>
      YulResult (r \<lparr> cont := map Expression (rev args) @ 
                                   EnterFunctionCall name fsig #
                                   ExitFunctionCall name args (vals r) (locals r) (funs r) fsig #
                                   cont r \<rparr>))"


fun yulBreak :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulResult \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"yulBreak D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulBreak D [] (YulResult r) = ErrorResult (STR ''Break outside loop body'') (Some r)"
| "yulBreak D (Expression cond1 # 
      ExitStatement (YulForLoop pre cond post body) c' f' # ct) (YulResult r) =
      YulResult (r \<lparr> cont := ct \<rparr>)"
| "yulBreak D (ch#ct) (YulResult r) = yulBreak D ct (YulResult (r \<lparr> cont := ct \<rparr>))"

fun yulContinue :: "('g, 'v, 't) YulDialect \<Rightarrow>
                    ('g, 'v, 't) StackEl list \<Rightarrow>
                    ('g, 'v, 't) YulResult \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"yulContinue D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulContinue D [] (YulResult r) = ErrorResult (STR ''Continue outside loop body'') (Some r)"
| "yulContinue D (Expression cond1 # 
      ExitStatement (YulForLoop pre cond post body) f' c' # ct)  (YulResult r) =
   YulResult (r \<lparr> cont := ((Expression cond1 #
      ExitStatement (YulForLoop pre cond post body) f' c' # ct))\<rparr>)"
| "yulContinue D (ch#ct) (YulResult r) = yulContinue D ct (YulResult (r \<lparr> cont := ct \<rparr>))"

fun yulLeave :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulResult \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"yulLeave D _ (ErrorResult e msg) = ErrorResult e msg"
| "yulLeave D [] (YulResult r) = ErrorResult (STR ''Leave outside function body'') (Some r)"
| "yulLeave D ((ExitFunctionCall idn args vals_old locals_old funs_old body )#ct) (YulResult r) =
   YulResult (r \<lparr> cont := ((ExitFunctionCall idn args vals_old locals_old funs_old body)#ct) \<rparr>)"
| "yulLeave D (ch#ct) r = yulLeave D ct r"

(* TODO: could check for invalid stack here as well as on exit *)
fun evalYulEnterStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                              ('v, 't) YulStatement \<Rightarrow> 
                              ('g, 'v, 't) YulResult \<Rightarrow>
                              ('g, 'v, 't) YulResult"
  where
"evalYulEnterStatement _ _ (ErrorResult e msg) = ErrorResult e msg"

(* TODO: reset vals to [] after statements? *)

| "evalYulEnterStatement D (YulAssignmentStatement (YulAssignment ids e)) (YulResult r) =
  YulResult (r \<lparr> cont := Expression e #
                        ExitStatement (YulAssignmentStatement (YulAssignment ids e)) (locals r) (funs r) #
                        cont r\<rparr>)"

| "evalYulEnterStatement D (YulVariableDeclarationStatement 
                           (YulVariableDeclaration ids (Some e))) (YulResult r) =
  YulResult (r \<lparr> cont := Expression e # 
                         ExitStatement (YulVariableDeclarationStatement 
                           (YulVariableDeclaration ids (Some e))) (locals r) (funs r) #
                         cont r \<rparr>)"

| "evalYulEnterStatement D (YulIf cond body) (YulResult r) =
  YulResult (r \<lparr> cont := Expression cond #
                          ExitStatement (YulIf cond body) (locals r) (funs r) #
                          cont r \<rparr>)"

| "evalYulEnterStatement D (YulSwitch cond cases) (YulResult r) =
  YulResult (r \<lparr> cont := Expression cond  #
                         ExitStatement (YulSwitch cond cases) (locals r) (funs r) #
                         cont r \<rparr>)"

(* empty pre = proceed with for loop *)
| "evalYulEnterStatement D (YulForLoop [] cond post body) (YulResult r) = 
    YulResult (r \<lparr> cont := ExitStatement (YulForLoop [] cond post body) (locals r) (funs r) #
                            cont r \<rparr>)"

(* non empty pre *)
| "evalYulEnterStatement D (YulForLoop pre cond post body) (YulResult r) = 
    YulResult (r \<lparr> cont := EnterStatement
                              (YulBlock (
                                pre @ [YulForLoop [] cond post body])
                              ) #
                            cont r \<rparr>)"

| "evalYulEnterStatement D (YulFunctionCallStatement fc) (YulResult r) =
  (YulResult (r \<lparr> vals := []
                , cont := Expression (YulFunctionCallExpression fc)  #
                          ExitStatement (YulFunctionCallStatement fc) (locals r) (funs r) #
                          cont r \<rparr>))"


(* does enterStatement need function scope argument? *)
| "evalYulEnterStatement D (YulBlock sl) (YulResult r) =
  (case gatherYulFunctions (funs r) sl of
    Inr fbad \<Rightarrow> ErrorResult (STR ''Duplicate function declaration: '' @@ fbad) (Some r)
    | Inl F \<Rightarrow> YulResult (r \<lparr> funs := F
                            , cont := map EnterStatement sl @ 
                                      ExitStatement (YulBlock sl) (locals r) (funs r) #
                                      cont r
 \<rparr>))"

| "evalYulEnterStatement _ st (YulResult r) = (YulResult (r \<lparr> cont := ExitStatement st (locals r) (funs r) # cont r \<rparr>))"

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
   

(* TODO: should we always force an empty stack after a statement? *)
fun evalYulExitStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                             ('v, 't) YulStatement \<Rightarrow> 
                             'v locals \<Rightarrow>
                             ('g, 'v, 't) function_sig locals \<Rightarrow>
                             ('g, 'v, 't) YulResult \<Rightarrow>
                             ('g, 'v, 't) YulResult"
  where
"evalYulExitStatement _ _ _ _ (ErrorResult e msg) = ErrorResult e msg"

| "evalYulExitStatement D (YulAssignmentStatement (YulAssignment ids e)) _ _ (YulResult r) = 
  (if length (vals r) \<noteq> length ids then ErrorResult (STR ''Arity mismatch (exiting assignment)'') (Some r)
   else
    (case put_values (locals r) ids (rev (take (length ids) (vals r))) of
      None \<Rightarrow> ErrorResult (STR ''Should be dead code (exiting assignment)'') (Some r)
      | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>)))"

| "evalYulExitStatement D (YulVariableDeclarationStatement (YulVariableDeclaration ids exo)) _ _ 
                          (YulResult r) =
  (case exo of
    None \<Rightarrow>
      (if length (vals r) = 0 then
        (case insert_values (locals r) (strip_id_types ids) (replicate (length ids) (default_val D)) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some r)
          | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>))
       else ErrorResult (STR ''Invalid stack (variable declaration)'') (Some r))
    | Some _ \<Rightarrow>
      (if length (vals r) \<noteq> length ids then ErrorResult (STR ''Arity mismatch (variable declaration + assignment)'') (Some r)
       else
        (case insert_values (locals r) (strip_id_types ids) (rev (take (length ids) (vals r))) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some r)
          | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>))))"

| "evalYulExitStatement D (YulIf cond body) _ _ (YulResult r) =
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then 
      YulResult (r \<lparr> vals := []
                   , cont := EnterStatement (YulBlock body) # (cont r)\<rparr>)
     else YulResult (r \<lparr> vals := [] \<rparr>))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting if)'') (Some r))"

| "evalYulExitStatement D (YulSwitch exp scs) _ _ (YulResult r) =
  (case vals r of
    [vh] \<Rightarrow>
     (case nextCase scs of
      (None, _) \<Rightarrow>
        (case getDefault scs of
          Some (YulSwitchCase None body) \<Rightarrow>
            YulResult (r \<lparr> vals := []
                         , cont := EnterStatement (YulBlock body) #
                                   cont r \<rparr>)
          | _ \<Rightarrow> ErrorResult (STR ''No default switch case'') (Some r))
      | (Some (YulSwitchCase (Some (YulLiteral vcond _)) body), scs') \<Rightarrow>
        (if vh = vcond then
          YulResult (r \<lparr> vals := []
                         , cont := EnterStatement (YulBlock body) #
                                   cont r \<rparr>)
         else YulResult (r \<lparr> cont := ExitStatement (YulSwitch exp scs') (locals r) (funs r) #
                                   cont r \<rparr>))
      | _ \<Rightarrow> ErrorResult (STR ''Should be dead code'') (Some r))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting switch statement)'') (Some r))"

(* we have already dealt with pre at this point *)
| "evalYulExitStatement D (YulForLoop pre cond post body) _ _ (YulResult r) = 
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then
      YulResult (r \<lparr> vals := []
                   , cont := (EnterStatement (YulBlock body) # 
                              Expression cond # 
                              ExitStatement (YulForLoop pre cond post body) (locals r) (funs r) #
                              cont r) \<rparr>)
     else
       (YulResult (r \<lparr> vals := []
                     , cont := (EnterStatement (YulBlock post) # cont r) \<rparr>)))
     | _ \<Rightarrow> ErrorResult (STR ''Invalid value stack (exiting ForLoop i.e. entering body)'') (Some r))"

| "evalYulExitStatement D (YulFunctionCallStatement fc) _ _ (YulResult r) =
  (case vals r of
    _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function call statement'') (Some r)
    | [] \<Rightarrow> YulResult r)"

| "evalYulExitStatement D YulBreak _ _ (YulResult r) =
   yulBreak D (cont r) (YulResult (r \<lparr> vals := [] \<rparr>))"

| "evalYulExitStatement D YulContinue _ _ (YulResult r) =
   yulContinue D (cont r) (YulResult (r \<lparr> vals := [] \<rparr>))"

| "evalYulExitStatement D YulLeave _ _ (YulResult r) =
   yulLeave D (cont r) (YulResult (r \<lparr> vals := [] \<rparr>))"

| "evalYulExitStatement D (YulBlock sl) L F (YulResult r) =
  (YulResult (r \<lparr> locals := restrict (locals r) L
                , vals := []
                , funs := F \<rparr>))"

| "evalYulExitStatement _ _ _ _ (YulResult r) = (YulResult (r \<lparr> vals := [] \<rparr>))"

(* TODO: make sure we are handling parameter ordering correctly (w/r/t reversal) *)
fun evalYulEnterFunctionCall :: "('g, 'v, 't) YulDialect \<Rightarrow>
                                 YulIdentifier \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) YulResult \<Rightarrow>
                                ('g, 'v, 't) YulResult" where
"evalYulEnterFunctionCall _ _ _ (ErrorResult e msg) = ErrorResult e msg"

| "evalYulEnterFunctionCall D name fsig (YulResult r) = 
  (case f_sig_body fsig of
    YulBuiltin impl \<Rightarrow>
     (case impl (global r) (rev (take (length (f_sig_arguments fsig)) (vals r))) of
           Inr err \<Rightarrow> ErrorResult (STR ''Error in builtin '' @@ (name @@ (STR '' : '' @@ err))) (Some r)
           | Inl (G', vals') \<Rightarrow>
                YulResult (r \<lparr> global := G', vals := rev vals' @ drop (length (f_sig_arguments fsig)) (vals r)  \<rparr>))
     | YulFunction body \<Rightarrow>
       (case insert_values locals_empty (strip_id_types (f_sig_arguments fsig)) (rev (take (length (f_sig_arguments fsig)) (vals r))) of
        None \<Rightarrow> ErrorResult (STR ''Arity error when calling function '' @@ name) (Some r)
        | Some L1 \<Rightarrow>
          (case insert_values L1 (strip_id_types (f_sig_returns fsig)) (replicate (length (f_sig_returns fsig)) (default_val D)) of
           None \<Rightarrow> ErrorResult (STR ''Name collision for returns in function '' @@ name) (Some r)
           | Some L2 \<Rightarrow>
             YulResult (r \<lparr> locals := L2
                          , vals := []
                          , funs := restrict (funs r) (map (\<lambda> n . (n, ())) (f_sig_visible fsig))
                          , cont := EnterStatement (YulBlock body) #
                                    cont r \<rparr>))))"

fun evalYulExitFunctionCall :: "('g, 'v, 't) YulDialect \<Rightarrow>
                                 YulIdentifier \<Rightarrow> 
                                 ('v, 't) YulExpression list \<Rightarrow>
                                'v list \<Rightarrow>
                                'v locals \<Rightarrow> 
                                ('g, 'v, 't) function_sig locals \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) YulResult \<Rightarrow>
                                ('g, 'v, 't) YulResult" 
  where
"evalYulExitFunctionCall _ _ _ _ _ _ _ (ErrorResult e msg) = ErrorResult e msg"

| "evalYulExitFunctionCall D name args vals_old locals_old funs_old fsig (YulResult r) =
  (case f_sig_body fsig of
    YulBuiltin _ \<Rightarrow> YulResult r
    | YulFunction _ \<Rightarrow>
    (case vals r of
      _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function '' @@ name) (Some r)
      | _ \<Rightarrow>
        (case get_values (locals r) (strip_id_types (f_sig_returns fsig)) of
         None \<Rightarrow> ErrorResult (STR ''Uninintialized returns for function '' @@ name) (Some r)
         | Some vs \<Rightarrow> YulResult (r \<lparr> locals := locals_old
                                   , vals := rev (vs) @ vals_old
                                   , funs := funs_old \<rparr>))))"


fun evalYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v, 't) YulResult \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"evalYulStep D (YulResult r)=
  (case cont r of
    [] \<Rightarrow> YulResult r
    | (EnterStatement st)#ct \<Rightarrow> evalYulEnterStatement D st (YulResult (r \<lparr> cont := ct \<rparr>))
    | (ExitStatement st L F)#ct \<Rightarrow> evalYulExitStatement D st L F  (YulResult (r \<lparr> cont := ct \<rparr>))
    | (Expression e)#ct \<Rightarrow> evalYulExpression D e (YulResult (r \<lparr> cont := ct \<rparr>))
    | (EnterFunctionCall name fsig)#ct \<Rightarrow> 
       evalYulEnterFunctionCall D name fsig 
        (YulResult (r \<lparr> cont := ct \<rparr>))
    | (ExitFunctionCall name args vals_old locals_old funs_old fsig)#ct \<Rightarrow> 
       evalYulExitFunctionCall D name args vals_old locals_old funs_old fsig
        (YulResult (r \<lparr> cont := ct \<rparr>))
)"
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
   evalYul' D (YulResult (r \<lparr> cont := [EnterStatement s] \<rparr>)) n)"

fun evalYulE :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulExpression \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYulE D e n =
  (let r = yulInit D in
  evalYul' D (YulResult (r \<lparr> cont := [Expression e] \<rparr>)) n)"

end