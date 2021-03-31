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

(*
record ('g, 'v, 't) result =
  "('g, 'v, 't) YulSemanticsCommon.result" +
  cont :: "('g, 'v, 't) StackEl list"

type_synonym ('g, 'v, 't) YulResult =
  "('g, 'v, 't) YulResult"

type_synonym ('g, 'v, 't) YulInput =
  "('g, 'v, 't) result"
*)


type_synonym ('g, 'v, 't) result' = "('g, 'v, 't) YulSemanticsCommon.result"

record ('g, 'v, 't) result =
  result :: "('g, 'v, 't) YulSemanticsCommon.result"
  cont :: "('g, 'v, 't) StackEl list"

(* convenience abbreviations to let us pretend like result is an extended record *)
abbreviation global where
"global \<equiv> r_global o result"
abbreviation global_update where
"global_update \<equiv> result_update o r_global_update"

abbreviation locals where
"locals \<equiv> r_locals o result"
abbreviation locals_update where
"locals_update \<equiv> result_update o r_locals_update"

abbreviation vals where
"vals \<equiv> r_vals o result"
abbreviation vals_update where
"vals_update \<equiv> result_update o r_vals_update"

abbreviation funs where
"funs \<equiv> r_funs o result"
abbreviation funs_update where
"funs_update \<equiv> result_update o r_funs_update"

abbreviation mode where
"mode \<equiv> r_mode o result"
abbreviation mode_update where
"mode_update \<equiv> result_update o r_mode_update"

(* idea: for each step, we return a new prefix to add on to the continuation *)
type_synonym ('g, 'v, 't) YulStepResult =
  "(('g, 'v, 't) result' * ('g, 'v, 't) StackEl list) YulResult"

type_synonym ('g, 'v, 't) YulResult =
  "(('g, 'v, 't) result) YulResult"

fun evalYulStatement ::
 "('g, 'v, 't) YulDialect \<Rightarrow>
  ('v, 't) YulStatement \<Rightarrow> 
  ('g, 'v, 't) result' \<Rightarrow>
  ('g, 'v, 't) YulStepResult" where
 "evalYulStatement D st r =
   YulResult (r, [EnterStatement st])"

fun evalYulExpression ::
"('g, 'v, 't) YulDialect \<Rightarrow>
 ('v, 't) YulExpression \<Rightarrow>
 ('g, 'v, 't) result' \<Rightarrow>
 ('g, 'v, 't) YulStepResult" where
  "evalYulExpression D (YulIdentifier idn) r =
   (case map_of (r_locals r) idn of
    None \<Rightarrow> ErrorResult (STR ''Undefined variable '' @@ idn) (Some (r, []))
    | Some v \<Rightarrow>
      YulResult ((r \<lparr> r_vals :=  v # r_vals r \<rparr>), []))"

| "evalYulExpression D (YulLiteralExpression (YulLiteral v _)) r =
   YulResult (r \<lparr> r_vals := v # r_vals r \<rparr>, [])"

| "evalYulExpression D YUL_EXPR{ \<guillemotleft>name\<guillemotright>(\<guillemotleft>args\<guillemotright>) } r =
   (case map_of (r_funs r) name of
    None \<Rightarrow> ErrorResult (STR ''Undefined function '' @@ name) (Some (r, []))
    | Some fsig \<Rightarrow>
      YulResult (r, (map Expression (rev args) @ 
                     [EnterFunctionCall name fsig,
                      ExitFunctionCall name (r_vals r) (r_locals r) (r_funs r) fsig])))"

(*
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
   YulResult (r \<lparr> cont := EnterStatement YUL_STMT{ {\<guillemotleft>post\<guillemotright>} } #
                          Expression cond1 #
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
*)


(* TODO: could check to ensure stack is empty here *)
fun evalYulEnterStatement :: "('g, 'v, 't) YulDialect \<Rightarrow>
                              ('v, 't) YulStatement \<Rightarrow> 
                              ('g, 'v, 't) result' \<Rightarrow>
                              ('g, 'v, 't) YulStepResult"
  where
  "evalYulEnterStatement D YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } r =
  YulResult (r,  [Expression e, 
                  ExitStatement YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } (r_locals r) (r_funs r)])"

| "evalYulEnterStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } r =
  YulResult (r, [Expression e,
                 ExitStatement YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>e\<guillemotright> } (r_locals r) (r_funs r)])"

| "evalYulEnterStatement D YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } r =
  YulResult (r, [Expression cond,
                 ExitStatement YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } (r_locals r) (r_funs r)])"

| "evalYulEnterStatement D YUL_STMT{ switch \<guillemotleft>cond\<guillemotright> \<guillemotleft>cases\<guillemotright> } r =
  YulResult (r, [Expression cond,
                 ExitStatement YUL_STMT{ switch \<guillemotleft>cond\<guillemotright> \<guillemotleft>cases\<guillemotright> } (r_locals r) (r_funs r)])"

(* empty pre = proceed with for loop *)
| "evalYulEnterStatement D YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } r = 
    YulResult (r, 
      [Expression cond,
       ExitStatement YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } (r_locals r) (r_funs r)])"

(* for loop with non empty pre *)
| "evalYulEnterStatement D YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } r = 
    YulResult (r, [EnterStatement (YulBlock (pre@[YUL_STMT{ for {} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} }]))])"

| "evalYulEnterStatement D YUL_STMT{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) } r =
  (YulResult (r, [Expression YUL_EXPR{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) }, 
                  ExitStatement YUL_STMT{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) } (r_locals r) (r_funs r)]))"

(* does enterStatement need function scope argument? *)
| "evalYulEnterStatement D YUL_STMT{ {\<guillemotleft>sl\<guillemotright>} } r =
  (case gatherYulFunctions (r_funs r) sl of
    Inr fbad \<Rightarrow> ErrorResult (STR ''Duplicate function declaration: '' @@ fbad) (Some (r, []))
    | Inl F \<Rightarrow> YulResult ((r \<lparr> r_funs := F \<rparr>),
                  map EnterStatement sl @
                  [ExitStatement YUL_STMT{ {\<guillemotleft>sl\<guillemotright>} } (r_locals r) (r_funs r)]))"

| "evalYulEnterStatement _ st r =
    (YulResult (r, [ExitStatement st (r_locals r) (r_funs r)]))"

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
                             ('g, 'v, 't) result' \<Rightarrow>
                             ('g, 'v, 't) YulStepResult"
  where
  "evalYulExitStatement D YUL_STMT{ \<guillemotleft>ids\<guillemotright> := \<guillemotleft>_\<guillemotright> } _ _ r = 
  (if length (r_vals r) \<noteq> length ids
   then ErrorResult (STR ''Arity mismatch (exiting assignment)'') (Some (r, []))
   else
    (case put_values (r_locals r) ids  (take (length ids) (r_vals r)) of
      None \<Rightarrow> ErrorResult (STR ''Should be dead code (exiting assignment)'') (Some (r, []))
      | Some L1 \<Rightarrow> YulResult (r \<lparr> r_locals := L1, r_vals := []\<rparr>, [])))"

| "evalYulExitStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> } _ _ r = (if length (r_vals r) = 0 then
        (case insert_values (r_locals r) (strip_id_types ids) 
                            (replicate (length ids) (default_val D)) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some (r, []))
          | Some L1 \<Rightarrow> YulResult (r \<lparr> r_locals := L1, r_vals := []\<rparr>, []))
       else ErrorResult (STR ''Invalid stack (variable declaration)'') (Some (r, [])))
  "
| "evalYulExitStatement D YUL_STMT{ let \<guillemotleft>ids\<guillemotright> := \<guillemotleft>_\<guillemotright> } _ _ r =
  (if length (r_vals r) \<noteq> length ids 
       then ErrorResult (STR ''Arity mismatch (variable declaration + assignment)'') (Some (r, []))
       else
        (case insert_values (r_locals r) (strip_id_types ids) (take (length ids) (r_vals r)) of
          None \<Rightarrow> ErrorResult (STR ''Duplicate variable declaration'') (Some (r, []))
          | Some L1 \<Rightarrow> YulResult (r \<lparr> r_locals := L1, r_vals := []\<rparr>, [])))"

| "evalYulExitStatement D YUL_STMT{ if \<guillemotleft>cond\<guillemotright> {\<guillemotleft>body\<guillemotright>} } _ _ r =
  (case r_vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then 
      YulResult (r \<lparr> r_vals := [] \<rparr>, [EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} }])
     else YulResult (r \<lparr> r_vals := [] \<rparr>, []))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting if)'') (Some (r, [])))"

| "evalYulExitStatement D YUL_STMT{ switch \<guillemotleft>exp\<guillemotright> \<guillemotleft>scs\<guillemotright> } _ _ r =
  (case r_vals r of
    [vh] \<Rightarrow>
     (case nextCase scs of
      (None, _) \<Rightarrow>
        (case getDefault scs of
          Some YUL_SWITCH_CASE{ default {\<guillemotleft>body\<guillemotright>} } \<Rightarrow>
            YulResult (r \<lparr> r_vals := [] \<rparr>, [EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} }])
          | _ \<Rightarrow> ErrorResult (STR ''No default switch case'') (Some (r, [])))
      | (Some YUL_SWITCH_CASE{ case \<guillemotleft>YulLiteral vcond _\<guillemotright> {\<guillemotleft>body\<guillemotright>} }, scs') \<Rightarrow>
        (if vh = vcond then
          YulResult (r \<lparr> r_vals := [] \<rparr>, [EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} }])
         else YulResult (r, [ExitStatement YUL_STMT{ switch \<guillemotleft>exp\<guillemotright> \<guillemotleft>scs'\<guillemotright> } 
                             (r_locals r) (r_funs r)]))
      | _ \<Rightarrow> ErrorResult (STR ''Should be dead code'') (Some (r, [])))
    | _ \<Rightarrow> ErrorResult (STR ''Invalid values stack (exiting switch statement)'') (Some (r, [])))"

(* we have already dealt with pre at this point (see evalYulEnterStatement) *)
| "evalYulExitStatement D YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } _ _ r = 
  (case r_vals r of
    [vh] \<Rightarrow>
    (if is_truthy D vh then
      YulResult 
        (r \<lparr> r_vals := [] \<rparr>, 
         [EnterStatement YUL_STMT{ {\<guillemotleft>body\<guillemotright>} },
          EnterStatement YUL_STMT{ {\<guillemotleft>post\<guillemotright>} },
          Expression cond,
          ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } (r_locals r) (r_funs r)])
     else
       (YulResult (r \<lparr> r_vals := [] \<rparr>, [])))
     | _ \<Rightarrow> ErrorResult (STR ''Invalid value stack (exiting ForLoop i.e. entering body)'')
                        (Some (r, [])))"

| "evalYulExitStatement D YUL_STMT{ \<guillemotleft>_\<guillemotright>(\<guillemotleft>_\<guillemotright>) } _ _ r =
  (case r_vals r of
    _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function call statement'') (Some (r, []))
    | [] \<Rightarrow> YulResult (r, []))"

| "evalYulExitStatement D YUL_STMT{ break } _ _ r =
   YulResult (r \<lparr> r_vals := [], r_mode := Break \<rparr>, [])"

| "evalYulExitStatement D YUL_STMT{ continue } _ _ r =
   YulResult (r \<lparr> r_vals := [], r_mode := Continue \<rparr>, [])"

| "evalYulExitStatement D YUL_STMT{ leave } _ _ r =
   YulResult (r \<lparr> r_vals := [], r_mode := Leave \<rparr>, [])"

| "evalYulExitStatement D YUL_STMT{ {\<guillemotleft>_\<guillemotright>} } L F r =
  (YulResult (r \<lparr> r_locals := restrict (r_locals r) L
                , r_vals := []
                , r_funs := F \<rparr>, []))"

| "evalYulExitStatement _ _ _ _ r = (YulResult (r \<lparr> r_vals := [] \<rparr>, []))"

fun evalYulEnterFunctionCall :: "('g, 'v, 't) YulDialect \<Rightarrow>
                                 YulIdentifier \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) result' \<Rightarrow>
                                ('g, 'v, 't) YulStepResult" where
  "evalYulEnterFunctionCall D name fsig r = 
  (case f_sig_body fsig of
    YulBuiltin impl \<Rightarrow>
     (case impl (take (length (f_sig_arguments fsig)) (r_vals r)) of
           Error err _ \<Rightarrow> 
              ErrorResult (STR ''Error in builtin '' @@ (name @@ (STR '' : '' @@ err))) 
                (Some (r, []))
           | Result impl' \<Rightarrow>
            (case impl' (r_global r) of
              (vals', G') \<Rightarrow>
                YulResult (r \<lparr> r_global := G', 
                               r_vals := vals' @ drop (length (f_sig_arguments fsig)) (r_vals r)  \<rparr>, 
                           [])))
     | YulFunction body \<Rightarrow>
       (case insert_values locals_empty (strip_id_types (f_sig_arguments fsig)) 
                                        (take (length (f_sig_arguments fsig)) (r_vals r)) of
        None \<Rightarrow> ErrorResult (STR ''Arity error when calling function '' @@ name) (Some (r, []))
        | Some L1 \<Rightarrow>
          (case insert_values L1 (strip_id_types (f_sig_returns fsig)) 
                                 (replicate (length (f_sig_returns fsig)) (default_val D)) of
           None \<Rightarrow> ErrorResult (STR ''Name collision for returns in function '' @@ name)
                               (Some (r, []))
           | Some L2 \<Rightarrow>
             YulResult (r \<lparr> r_locals := L2
                          , r_vals := []
                          , r_funs := restrict (r_funs r) (map (\<lambda> n . (n, ())) 
                                                          (f_sig_visible fsig)) \<rparr>,
                        [EnterStatement (YulBlock body)]))))"

fun evalYulExitFunctionCall :: "('g, 'v, 't) YulDialect \<Rightarrow>
                                 YulIdentifier \<Rightarrow> 
                                'v list \<Rightarrow>
                                'v locals \<Rightarrow> 
                                ('g, 'v, 't) function_sig locals \<Rightarrow>
                                ('g, 'v, 't) function_sig \<Rightarrow>
                                ('g, 'v, 't) result' \<Rightarrow>
                                ('g, 'v, 't) YulStepResult" 
  where
  "evalYulExitFunctionCall D name vals_old locals_old funs_old fsig r =
  (case f_sig_body fsig of
    YulBuiltin _ \<Rightarrow> YulResult (r, [])
    | YulFunction _ \<Rightarrow>
    (case r_vals r of
      _#_ \<Rightarrow> ErrorResult (STR ''Nonempty stack after function '' @@ name) (Some (r, []))
      | _ \<Rightarrow>
        (case get_values (r_locals r) (strip_id_types (f_sig_returns fsig)) of
         None \<Rightarrow> ErrorResult (STR ''Uninintialized returns for function '' @@ name) (Some (r, []))
         | Some vs \<Rightarrow> YulResult (r \<lparr> r_locals := locals_old
                                   , r_vals := vs @ vals_old
                                   , r_funs := funs_old \<rparr>, []))))"

(*
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
*)

definition updateResult :: "('g, 'v, 't) StackEl list \<Rightarrow>
                     ('g, 'v, 't) YulStepResult \<Rightarrow> 
                     ('g, 'v, 't) YulResult" where
"updateResult ct res =
  (case res of
    YulResult (r', c') \<Rightarrow>
      YulResult \<lparr> result = r', cont = c' @ ct \<rparr>
    | ErrorResult s (Some (r', c')) \<Rightarrow>
      ErrorResult s (Some \<lparr> result = r', cont = c' @ ct\<rparr>)
    | ErrorResult s None \<Rightarrow>
      ErrorResult s None)"


(* question: do we check for empty value stack on entry
into statement? *)
(*
              (case vals r of
               [] \<Rightarrow> evalYulEnterStatement D st (result r)
               | _ \<Rightarrow> ErrorResult (STR ''Nonempty stack on statement entry'') (Some (result r, [])))
*)

(* need to make sure early loop exit is happening correctly. *)
fun evalYulStep :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v, 't) result \<Rightarrow>
                    ('g, 'v, 't) YulResult" where
"evalYulStep D r =
  (case cont r of
    [] \<Rightarrow> 
      (case mode r of
        Regular \<Rightarrow> YulResult r
        | Break \<Rightarrow> ErrorResult (STR ''Break outside loop body'') 
                               (Some (r \<lparr> cont := []\<rparr>))
        | Continue \<Rightarrow> ErrorResult (STR ''Continue outside loop body'')
                                  (Some (r \<lparr> cont := []\<rparr>))
        | Leave \<Rightarrow> ErrorResult (STR ''Leave outside function body'')
                               (Some (r \<lparr> cont := []\<rparr>)))

    | ch#ct \<Rightarrow>
      (case mode r of
        Regular \<Rightarrow>
          updateResult ct
          (case ch of
            (EnterStatement st) \<Rightarrow> evalYulEnterStatement D st (result r)
            | (ExitStatement st L F) \<Rightarrow> evalYulExitStatement D st L F (result r)
            | (Expression e) \<Rightarrow> evalYulExpression D e (result r)
            | (EnterFunctionCall name fsig) \<Rightarrow> 
               evalYulEnterFunctionCall D name fsig (result r)
            | (ExitFunctionCall name vals_old locals_old funs_old fsig) \<Rightarrow> 
               evalYulExitFunctionCall D name vals_old locals_old funs_old fsig
                (result r))

        | Break \<Rightarrow>
          (case ch of
            (ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } c' f') \<Rightarrow>
              YulResult (r \<lparr> cont := ct, mode := Regular \<rparr>)
            | (ExitFunctionCall _ _ _ _ _) \<Rightarrow>
              ErrorResult (STR ''Break outside loop body (inside function body)'')
                          (Some (r \<lparr> cont := ct \<rparr>))
            | _ \<Rightarrow> YulResult (r \<lparr> cont := ct \<rparr>))

        | Continue \<Rightarrow>
          (case ch of
            ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } f' c' \<Rightarrow>
              YulResult (r \<lparr> cont := EnterStatement YUL_STMT{ {\<guillemotleft>post\<guillemotright>} } #
                               Expression cond #
                               ExitStatement YUL_STMT{ for {\<guillemotleft>pre\<guillemotright>} \<guillemotleft>cond\<guillemotright> {\<guillemotleft>post\<guillemotright>} {\<guillemotleft>body\<guillemotright>} } f' c' 
                               # ct
                           , mode := Regular \<rparr>)

            | (ExitFunctionCall _ _ _ _ _) \<Rightarrow>
                ErrorResult (STR ''Continue outside loop body (inside function body)'') 
                            (Some (r \<lparr> cont := ct \<rparr>))
            | _ \<Rightarrow> YulResult (r \<lparr> cont := ct \<rparr>))
                
        | Leave \<Rightarrow>
          (case ch of
            (ExitFunctionCall _ _ _ _ _) \<Rightarrow> YulResult (r \<lparr> cont := ch#ct, mode := Regular \<rparr>)
            | _ \<Rightarrow> YulResult (r \<lparr> cont := ct \<rparr>))))"



fun evalYul' :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('g, 'v, 't) result \<Rightarrow> 
                 nat \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYul' D r n =
  (if n \<le> 0 then (YulResult r)
   else 
    (if cont r = [] then YulResult r
    else (case evalYulStep D r of
           (ErrorResult msg x) \<Rightarrow> ErrorResult msg x 
         | YulResult r \<Rightarrow> evalYul' D r (n - 1))))"

fun yulInit :: "('g, 'v, 't) YulDialect \<Rightarrow> ('g, 'v,'t) result'" where
"yulInit D = \<lparr> r_global = init_state D
             , r_locals = locals_empty
             , r_vals = []
             , r_funs = builtins D
             , r_mode = Regular \<rparr>"

fun evalYul :: "('g, 'v, 't) YulDialect \<Rightarrow>
                ('v, 't) YulStatement \<Rightarrow>
                nat \<Rightarrow>
                ('g, 'v, 't) YulResult" where
"evalYul D s n =
  evalYul' D \<lparr> result = yulInit D,  cont = [EnterStatement s] \<rparr> n"

fun evalYulE :: "('g, 'v, 't) YulDialect \<Rightarrow>
                 ('v, 't) YulExpression \<Rightarrow>
                 nat \<Rightarrow>
                 ('g, 'v, 't) YulResult" where
"evalYulE D e n =
  evalYul' D \<lparr> result = yulInit D,  cont = [Expression e] \<rparr> n"

end