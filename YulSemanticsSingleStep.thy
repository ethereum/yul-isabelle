theory YulSemanticsSingleStep imports "YulSemanticsCommon"
begin


(* stack used to represent computation remaining after this step *)
datatype ('g, 'v, 't) StackEl =
  EnterStatement "('v, 't) YulStatement"
  (* When exiting statements, we remember the old local-vars and function contexts
     (used when exiting blocks)
  *)
  | ExitStatement "('v, 't) YulStatement" "'v locals" "('g, 'v, 't) function_sig locals" 

  (* when entering functions, we remember the function name (for error reporting)
     and function signature
  *)
  | EnterFunctionCall "YulIdentifier" 
                      "('g, 'v, 't) function_sig"
  (* when exiting functions, we remember
     - function name
     - old stack
     - old locals
     - old functions context
     - signature of function being called *)
  | is_ExitFunctionCall: ExitFunctionCall "YulIdentifier"
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

type_synonym ('g, 'v, 't) YulInput =
  "('g, 'v, 't) result"

fun evalYulStatement ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulStatement \<Rightarrow> ('g, 'v, 't) YulInput \<Rightarrow>
  ('g, 'v, 't) YulResult" where
 "evalYulStatement D st r =
   YulResult (r \<lparr> cont := EnterStatement st # cont r \<rparr>)"

fun evalYulExpression ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulExpression \<Rightarrow>
 ('g, 'v, 't) YulInput \<Rightarrow>
 ('g, 'v, 't) YulResult" where
  "evalYulExpression D (YulIdentifier idn) r =
   (case map_of (locals r) idn of
    None \<Rightarrow> ErrorResult (STR ''Undefined variable '' @@ idn) (Some r)
    | Some v \<Rightarrow>
      YulResult (r \<lparr> vals :=  v # vals r \<rparr>))"

| "evalYulExpression D (YulLiteralExpression (YulLiteral v _)) r =
   YulResult (r \<lparr> vals := v # vals r \<rparr>)"

| "evalYulExpression D YUL_EXPR{ \<guillemotleft>name\<guillemotright>(\<guillemotleft>args\<guillemotright>) } r =
   (case map_of (funs r) name of
    None \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ name) (Some r)
    | Some fsig \<Rightarrow>
      YulResult (r \<lparr> cont := map Expression (rev args) @ 
                             EnterFunctionCall name fsig #
                             ExitFunctionCall name (vals r) (locals r) (funs r) fsig #
                             cont r \<rparr>))"

fun yulBreak :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulInput \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
 "yulBreak D [] r = ErrorResult (STR ''Break outside loop body'') (Some r)"
| "yulBreak D (ExitFunctionCall _ _ _ _ _ # _) r =
    ErrorResult (STR ''Break outside loop body (inside function body)'') (Some r)"
| "yulBreak D (ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } c' f' # ct) r =
      YulResult (r \<lparr>cont := ct \<rparr>)"
| "yulBreak D (ch#ct) r = yulBreak D ct (r \<lparr> cont := ct \<rparr>)"


fun yulContinue :: "('g, 'v, 't) YulDialect \<Rightarrow>
                    ('g, 'v, 't) StackEl list \<Rightarrow>
                    ('g, 'v, 't) YulInput \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
  "yulContinue D [] r = ErrorResult (STR ''Continue outside loop body'') (Some r)"
| "yulContinue D (ExitFunctionCall _ _ _ _ _ # _) r =
    ErrorResult (STR ''Continue outside loop body (inside function body)'') (Some r)"
| "yulContinue D (Expression cond1 # 
                  ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } f' c' # ct) r =
   YulResult (r \<lparr> cont := Expression cond1 #
                          ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } f' c' 
                          # ct \<rparr>)"

| "yulContinue D (ch#ct) r = yulContinue D ct (r \<lparr> cont := ct \<rparr>)"

fun yulLeave :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) StackEl list \<Rightarrow>
                 ('g, 'v, 't) YulInput \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
  "yulLeave D [] r = ErrorResult (STR ''Leave outside function body'') (Some r)"
| "yulLeave D (ch#ct) r = (if is_ExitFunctionCall ch then YulResult (r \<lparr> cont := ch#ct \<rparr>) 
                           else yulLeave D ct r)"

(* TODO: could check to ensure stack is empty here *)
fun evalYulEnterStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                              ('v, 't) YulStatement \<Rightarrow> 
                              ('g, 'v, 't) YulInput \<Rightarrow>
                              ('g, 'v, 't) YulResult"
  where
  "evalYulEnterStatement D YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } r =
  YulResult (r \<lparr> cont := (Expression e # 
                         ExitStatement YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } (locals r) (funs r) # 
                         cont r) \<rparr>)"

| "evalYulEnterStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } r =
  YulResult (r \<lparr> cont := Expression e # 
                         ExitStatement YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } (locals r) (funs r) #
                         cont r \<rparr>)"

| "evalYulEnterStatement D YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } r =
  YulResult (r \<lparr> cont := Expression cond #
                         ExitStatement YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } (locals r) (funs r) # 
                         cont r \<rparr>)"

| "evalYulEnterStatement D YUL_STMT{ switch \<guillemotleft>cond\<guillemotright> \<guillemotleft>cases\<guillemotright> } r =
  YulResult (r \<lparr> cont := Expression cond #
                         ExitStatement YUL_STMT{ switch \<guillemotleft>cond\<guillemotright> \<guillemotleft>cases\<guillemotright> } (locals r) (funs r) #
                         cont r\<rparr>)"

(* empty pre = proceed with for loop *)
| "evalYulEnterStatement D YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } r = 
    YulResult (r \<lparr> cont := Expression cond # 
                           ExitStatement YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } (locals r) 
                                                                                     (funs r) # 
                           cont r \<rparr>)"

(* non empty pre *)
| "evalYulEnterStatement D YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } r = 
    YulResult (r \<lparr> cont := EnterStatement 
                            (YulBlock (pre@[YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} }])) # 
                           cont r \<rparr>)"

| "evalYulEnterStatement D YUL_STMT{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) } r =
  (YulResult (r \<lparr> vals := []
                , cont := Expression YUL_EXPR{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) } # 
                          ExitStatement YUL_STMT{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) } (locals r) (funs r) # 
                          cont r \<rparr>))"

(* does enterStatement need function scope argument? *)
| "evalYulEnterStatement D YUL_STMT{ {\<guillemotleft>sl\<guillemotright>} } r =
  (case gatherYulFunctions (funs r) sl of
    Inr fbad \<Rightarrow> ErrorResult (STR ''Duplicate function declaration: '' @@ fbad) (Some r)
    | Inl F \<Rightarrow> YulResult (r \<lparr> funs := F
                            , cont := map EnterStatement sl @ 
                                      ExitStatement YUL_STMT{ {\<guillemotleft>sl\<guillemotright>} } (locals r) (funs r) #
                                      cont r \<rparr>))"

| "evalYulEnterStatement _ st r =
    (YulResult (r \<lparr> cont := ExitStatement st (locals r) (funs r) # cont r \<rparr>))"

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
                             ('g, 'v, 't) YulInput \<Rightarrow>
                             ('g, 'v, 't) YulResult"
  where
  "evalYulExitStatement D YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>_\<guillemotright> } _ _ r = 
  (if length (vals r) \<noteq> length ids then ErrorResult (STR ''Arity mismatch (exiting assignment)'') (Some r)
   else
    (case put_values (locals r) ids  (take (length ids) (vals r)) of
      None \<Rightarrow> ErrorResult (STR ''Should be dead code (exiting assignment)'') (Some r)
      | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>)))"

| "evalYulExitStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> } _ _ r = (if length (vals r) = 0 then
        (case insert_values (locals r) (strip_id_types ids) (replicate (length ids) (default_val D)) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some r)
          | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>))
       else ErrorResult (STR ''Invalid stack (variable declaration)'') (Some r))
  "
| "evalYulExitStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>_\<guillemotright> } _ _ r =
  (if length (vals r) \<noteq> length ids then ErrorResult (STR ''Arity mismatch (variable declaration + assignment)'') (Some r)
       else
        (case insert_values (locals r) (strip_id_types ids) (take (length ids) (vals r)) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some r)
          | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1, vals := []\<rparr>)))"

| "evalYulExitStatement D YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } _ _ r =
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then 
      YulResult (r \<lparr> vals := [], cont := EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} } # (cont r)\<rparr>)
     else YulResult (r \<lparr> vals := [] \<rparr>))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting if)'') (Some r))"

| "evalYulExitStatement D YUL_STMT{ switch \<guillemotleft>exp\<guillemotright> \<guillemotleft>scs\<guillemotright> } _ _ r =
  (case vals r of
    [vh] \<Rightarrow>
     (case nextCase scs of
      (None, _) \<Rightarrow>
        (case getDefault scs of
          Some YUL_SWITCH_CASE{ default {\<guillemotleft>body\<guillemotright>} } \<Rightarrow>
            YulResult (r \<lparr> vals := []
                         , cont := EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} } #
                                   cont r \<rparr>)
          | _ \<Rightarrow> ErrorResult (STR ''No default switch case'') (Some r))
      | (Some YUL_SWITCH_CASE{ case \<guillemotleft>YulLiteral vcond _\<guillemotright> {\<guillemotleft>body\<guillemotright>} }, scs') \<Rightarrow>
        (if vh = vcond then
          YulResult (r \<lparr> vals := []
                         , cont := EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} } #
                                   cont r \<rparr>)
         else YulResult (r \<lparr> cont := ExitStatement YUL_STMT{ switch \<guillemotleft>exp\<guillemotright> \<guillemotleft>scs'\<guillemotright> } (locals r) (funs r) #
                                   cont r \<rparr>))
      | _ \<Rightarrow> ErrorResult (STR ''Should be dead code'') (Some r))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting switch statement)'') (Some r))"

(* we have already dealt with pre at this point *)
| "evalYulExitStatement D YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } _ _ r = 
  (case vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then
      YulResult (r \<lparr> vals := []
                   , cont := (EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} } # EnterStatement YUL_STMT{ {\<guillemotleft>post\<guillemotright>} } #
                              Expression cond # 
                              ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } (locals r) (funs r) #
                              cont r) \<rparr>)
     else
       (YulResult (r \<lparr> vals := []
                     , cont := (cont r) \<rparr>)))
     | _ \<Rightarrow> ErrorResult (STR ''Invalid value stack (exiting ForLoop i.e. entering body)'') (Some r))"

| "evalYulExitStatement D YUL_STMT{ \<guillemotleft>_\<guillemotright>(\<guillemotleft>_\<guillemotright>) } _ _ r =
  (case vals r of
    _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function call statement'') (Some r)
    | [] \<Rightarrow> YulResult r)"

| "evalYulExitStatement D YUL_STMT{ break } _ _ r =
   yulBreak D (cont r) (r \<lparr> vals := [] \<rparr>)"

| "evalYulExitStatement D YUL_STMT{ continue } _ _ r =
   yulContinue D (cont r) (r \<lparr> vals := [] \<rparr>)"

| "evalYulExitStatement D YUL_STMT{ leave } _ _ r =
   yulLeave D (cont r) (r \<lparr> vals := [] \<rparr>)"

| "evalYulExitStatement D YUL_STMT{ {\<guillemotleft>_\<guillemotright>} } L F r =
  (YulResult (r \<lparr> locals := restrict (locals r) L
                , vals := []
                , funs := F \<rparr>))"

| "evalYulExitStatement _ _ _ _ r = (YulResult (r \<lparr> vals := [] \<rparr>))"

(* TODO: make sure we are handling parameter ordering correctly (w/r/t reversal) *)
fun evalYulEnterFunctionCall :: "('g, 'v, 't) YulDialect \<Rightarrow>
                                 YulIdentifier \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) YulInput \<Rightarrow>
                                ('g, 'v, 't) YulResult" where
  "evalYulEnterFunctionCall D name fsig r = 
  (case f_sig_body fsig of
    YulBuiltin impl \<Rightarrow>
     (case impl (take (length (f_sig_arguments fsig)) (vals r)) (global r)  of
           Inr err \<Rightarrow> ErrorResult (STR ''Error in builtin '' @@ (name @@ (STR '' : '' @@ err))) (Some r)
           | Inl (G', vals') \<Rightarrow>
                YulResult (r \<lparr> global := G', vals := vals' @ drop (length (f_sig_arguments fsig)) (vals r)  \<rparr>))
     | YulFunction body \<Rightarrow>
       (case insert_values locals_empty (strip_id_types (f_sig_arguments fsig)) (take (length (f_sig_arguments fsig)) (vals r)) of
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
                                'v list \<Rightarrow>
                                'v locals \<Rightarrow> 
                                ('g, 'v, 't) function_sig locals \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) YulInput \<Rightarrow>
                                ('g, 'v, 't) YulResult" 
  where
  "evalYulExitFunctionCall D name vals_old locals_old funs_old fsig r =
  (case f_sig_body fsig of
    YulBuiltin _ \<Rightarrow> YulResult r
    | YulFunction _ \<Rightarrow>
    (case vals r of
      _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function '' @@ name) (Some r)
      | _ \<Rightarrow>
        (case get_values (locals r) (strip_id_types (f_sig_returns fsig)) of
         None \<Rightarrow> ErrorResult (STR ''Uninintialized returns for function '' @@ name) (Some r)
         | Some vs \<Rightarrow> YulResult (r \<lparr> locals := locals_old
                                   , vals := vs @ vals_old
                                   , funs := funs_old \<rparr>))))"


fun evalYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v, 't) YulInput \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"evalYulStep D r =
  (case cont r of
    [] \<Rightarrow> YulResult r
    | (EnterStatement st)#ct \<Rightarrow> evalYulEnterStatement D st (r \<lparr> cont := ct \<rparr>)
    | (ExitStatement st L F)#ct \<Rightarrow> evalYulExitStatement D st L F  (r \<lparr> cont := ct \<rparr>)
    | (Expression e)#ct \<Rightarrow> evalYulExpression D e (r \<lparr> cont := ct \<rparr>)
    | (EnterFunctionCall name fsig)#ct \<Rightarrow> 
       evalYulEnterFunctionCall D name fsig 
        (r \<lparr> cont := ct \<rparr>)
    | (ExitFunctionCall name vals_old locals_old funs_old fsig)#ct \<Rightarrow> 
       evalYulExitFunctionCall D name vals_old locals_old funs_old fsig
        (r \<lparr> cont := ct \<rparr>)
)"

fun evalYul' :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) YulInput \<Rightarrow> 
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYul' D r n =
  (if n \<le> 0 then (YulResult r)
   else (case evalYulStep D r of (ErrorResult msg x) \<Rightarrow> ErrorResult msg x | YulResult r \<Rightarrow> evalYul' D r (n - 1)))"

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
   evalYul' D (r \<lparr> cont := [EnterStatement s] \<rparr>) n)"

fun evalYulE :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulExpression \<Rightarrow>
                 int \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYulE D e n =
  (let r = yulInit D in
  evalYul' D (r \<lparr> cont := [Expression e] \<rparr>) n)"

end