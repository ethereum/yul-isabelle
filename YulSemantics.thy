theory YulSemantics imports "YulSemanticsCommon"
begin

datatype YulSwitchCanonical =
  YulSwitchCanonical
    (YulSwitchCanonicalExpression: YulExpression)
    (YulSwitchCanonicalCases: "YulSwitchCase list")
    (YulSwitchCanonicalDefault : "YulStatement list")

(* idea: reorganize the switch statement so that
   - if there is no default, we add an empty one
   - pick out the default case specially either way *)
(* TODO: if we are willing to complicate the state representation, we could
   avoid having to do this as a pre-pass. *)
fun canonicalizeSwitch ::
  "YulExpression \<Rightarrow> YulSwitchCase list \<Rightarrow> YulStatement list option \<Rightarrow> YulSwitchCanonical option" 
  where
"canonicalizeSwitch e [] None =
  Some (YulSwitchCanonical e [] [])"
| "canonicalizeSwitch e [] (Some d) =
  Some (YulSwitchCanonical e [] d)"

(* fill in default case *)
| "canonicalizeSwitch e ((YulSwitchCase None dfl)#ct) None =
   canonicalizeSwitch e ct (Some dfl)"
(* 2 default cases = invalid *)
| "canonicalizeSwitch e ((YulSwitchCase None dfl)#ct) (Some _) =
   None"

| "canonicalizeSwitch e ((YulSwitchCase (Some x) body)#ct) d =
   (case canonicalizeSwitch e ct d of
    None \<Rightarrow> None
    | Some (YulSwitchCanonical e cs' d') \<Rightarrow>
           Some (YulSwitchCanonical e ((YulSwitchCase (Some x) body)#cs') d'))"


(* measures for Yul programs (used for semantics termination) *)
function yulStatementMeasure :: "YulStatement \<Rightarrow> nat"
and yulStatementsMeasure :: "YulStatement list \<Rightarrow> nat"
and yulExpressionMeasure :: "YulExpression \<Rightarrow> nat"
and yulExpressionsMeasure :: "YulExpression list \<Rightarrow> nat"
and yulCaseMeasure :: "YulSwitchCase \<Rightarrow> nat"
and yulCasesMeasure :: "YulSwitchCase list \<Rightarrow> nat"
 where
"yulStatementMeasure (YulFunctionCallStatement fc) =
  (case fc of (YulFunctionCall _ args) \<Rightarrow> 1 + yulExpressionsMeasure args)"
| "yulStatementMeasure (YulAssignmentStatement a) =
  (case a of (YulAssignment _ expr) \<Rightarrow> 1 + yulExpressionMeasure expr)"
| "yulStatementMeasure (YulVariableDeclarationStatement vd) =
  (case vd of (YulVariableDeclaration _ oexpr) \<Rightarrow>
   (case oexpr of
    None \<Rightarrow> 1
    | Some expr \<Rightarrow> 1 + yulExpressionMeasure expr))"
| "yulStatementMeasure (YulFunctionDefinitionStatement _) = 1"
| "yulStatementMeasure (YulIf cond body) =
   1 + yulExpressionMeasure cond + yulStatementsMeasure body"
| "yulStatementMeasure (YulSwitch cond cases) =
   1 + yulExpressionMeasure cond + 
      yulCasesMeasure cases"
| "yulStatementMeasure (YulForLoop pre cond post body) =
   1 + yulStatementsMeasure pre + 
       yulExpressionMeasure cond +
       yulStatementsMeasure post +
       yulStatementsMeasure body"
| "yulStatementMeasure (YulBlock sts) =
   1 + yulStatementsMeasure sts"
| "yulStatementMeasure (YulBreak) = 1"
| "yulStatementMeasure (YulLeave) = 1"
| "yulStatementMeasure (YulContinue) = 1"

| "yulExpressionMeasure (YulFunctionCallExpression  fc) =
  (case fc of (YulFunctionCall _ args) \<Rightarrow>  1 + yulExpressionsMeasure args)"
| "yulExpressionMeasure (YulIdentifier _) = 1"
| "yulExpressionMeasure (YulLiteralExpression _) = 1"

| "yulCaseMeasure (YulSwitchCase _ body) =
   1 + yulStatementsMeasure body"

| "yulStatementsMeasure [] = 1"
| "yulStatementsMeasure (h#t) = 1 + yulStatementMeasure h + yulStatementsMeasure t"

| "yulExpressionsMeasure [] = 1"
| "yulExpressionsMeasure (h#t) = 1 + yulExpressionMeasure h + yulExpressionsMeasure t"

| "yulCasesMeasure [] = 1"
| "yulCasesMeasure (h#t) = 1 + yulCaseMeasure h + yulCasesMeasure t"

  by pat_completeness auto

(* I am not sure why size_change is needed here.
   It seems like this function is rather trivially
   structurally recursive. *)
termination by size_change

lemma yul_canonical_switch_expr :
  assumes H : "canonicalizeSwitch expr cases dfl = 
               Some (YulSwitchCanonical expr2 cases2 dfl2)" 
  shows "expr = expr2" using assms
proof(induction cases arbitrary: expr expr2 cases2 dfl dfl2)
  case Nil
  then show ?case by(cases dfl; auto)
next
  case (Cons a cases)
  obtain cond body where A : "a = YulSwitchCase cond body" by(cases a; auto)
  then show ?case
  proof(cases cond)
    case None
    then show ?thesis
      using Cons.prems Cons.IH A None by(cases dfl; auto)
  next
    case (Some cond')
    then show ?thesis
    proof(cases dfl)
      case None' : None
      then show ?thesis
        using Cons.prems Cons.IH A Some by(auto split:option.splits YulSwitchCanonical.splits)
    next      
      case Some' : (Some dfl')
      then show ?thesis
        using Cons.prems Cons.IH A Some by(auto split:option.splits YulSwitchCanonical.splits)
    qed
  qed
qed

fun yulSwitchCanonicalMeasure :: "YulSwitchCanonical \<Rightarrow> nat" where
"yulSwitchCanonicalMeasure (YulSwitchCanonical expr' cases' dfl2) =
  yulExpressionMeasure expr' +
  yulCasesMeasure cases' +
  yulStatementsMeasure dfl2"

lemma yul_canonical_switch_size :
  assumes H : "canonicalizeSwitch expr cases dfl = 
               Some (YulSwitchCanonical expr' cases' dfl2)"
  shows "(case dfl of None \<Rightarrow> 0 
          | Some dfl' \<Rightarrow> yulStatementsMeasure dfl') +
         yulStatementMeasure (YulSwitch expr cases) \<ge>
         yulSwitchCanonicalMeasure (YulSwitchCanonical expr' cases' dfl2)" using H
proof(induction cases arbitrary: expr dfl expr' cases' dfl2)
  case Nil
  then show ?case
    by(cases dfl; auto)
next
  case (Cons a cases)
  then obtain lit body where
    A : "a = (YulSwitchCase lit body)" by(cases a; auto)
  show ?case
  proof(cases dfl)
    case None
    show ?thesis
    proof(cases lit)
      case None' : None
      then show ?thesis using Cons.prems Cons.IH[of expr "Some body" expr' cases' dfl2] A None
        by(auto)
    next
      case Some' : (Some a')

      then obtain cases'tl where Cases' : "cases' = YulSwitchCase (Some a') body # cases'tl"
        using Cons.prems None A Some' by(auto split:option.splits YulSwitchCanonical.splits)
      then show ?thesis using Cons.prems Cons.IH[of expr None expr' cases'tl dfl2] A None Some'
        by(auto simp add: yul_canonical_switch_expr
                split:option.splits YulSwitchCanonical.splits)
    qed
  next
    case (Some dfl')
    then show ?thesis
    proof(cases lit)
      case None' : None
      then show ?thesis using Cons.prems Cons.IH A Some
        by(auto)
    next
      case Some' : (Some a')

      then obtain cases'tl where Cases' : "cases' = YulSwitchCase (Some a') body # cases'tl"
        using Cons.prems Some A Some' by(auto split:option.splits YulSwitchCanonical.splits)
      then show ?thesis using Cons.prems Cons.IH[of expr "(Some dfl')" expr' cases'tl dfl2]
                              A Some Some'
        by(auto simp add: yul_canonical_switch_expr
                split:option.splits YulSwitchCanonical.splits)
    qed
  qed
qed

(* executable semantics for Yul programs *)
(* parameters:
   - global state
   - local state (variable map)
   - function identifiers
   - statement
   - return *)

(* TODO: do we need to maintain the typing environment at runtime?
   I don't think we should. *)


(* locale for fixing global state, value types *)
locale YulSem =
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


(* gas checks will happen on statement *)
(* TODO: consider not using the same "result" state type, this may end up giving us an
   implementation that is too similar to the small step at some points. *)
(* TODO: consider changing the nat type for fuel to int, in order to bring this in line
   with the small-step version *)
(* TODO: make sure mode is getting reset to Regular correctly when alternating between
   statement and expression evaluation *)
function
yul_eval_statement ::
  "YulStatement \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_statements ::
  "YulStatement list \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_block ::
  "YulStatement list \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_expression ::
  "YulExpression \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_expressions :: 
   "YulExpression list \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_canonical_switch ::
  "YulSwitchCanonical \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"  
  where

(*
 * helper: expression
 *)
(* identifier *)
"yul_eval_expression (YulIdentifier i) n (YulResult r) =
 (case (locals r) of
    [] \<Rightarrow> ErrorResult (STR ''No variable context'')
    | Lh#Lt \<Rightarrow> 
     (case (Lh i) of
      None \<Rightarrow> (ErrorResult (STR ''Undefined variable '' @@ i))
      | Some v \<Rightarrow> 
        (case (vals r) of
          None \<Rightarrow> YulResult (r \<lparr> locals := (Lh#Lt), vals := (Some ([v]))\<rparr>)
          | Some vs \<Rightarrow> YulResult (r \<lparr> locals := (Lh#Lt), vals := (Some (vs @ [v]))\<rparr>))))"
(* literal *)
| "yul_eval_expression (YulLiteralExpression (YulLiteral value type)) n 
                       (YulResult r) =
  (case parseLiteral value of
    None \<Rightarrow> (ErrorResult (STR ''Bad literal '' @@ value))
    | Some v \<Rightarrow> 
      (case (vals r) of
        None \<Rightarrow> YulResult (r \<lparr> vals := (Some [v])\<rparr>)
        | Some vs \<Rightarrow> YulResult (r \<lparr> vals := Some (vs @ [v])\<rparr>)))"

(* function call *)
(* function calls consume fuel *)
| "yul_eval_expression (YulFunctionCallExpression (YulFunctionCall name args)) 0 r =
    r"

(* G L F m vso *)
(* G1 (L1h#L1t) (F1h#F1t) m1 vso1 *)

(* TODO: double check details around threading of function context and mode *)
| "yul_eval_expression (YulFunctionCallExpression (YulFunctionCall name args)) (Suc n)
                       (YulResult r) =
   (case yul_eval_expressions args n (YulResult r) of
    ErrorResult s \<Rightarrow> ErrorResult s
    | YulResult r1 \<Rightarrow> 
      (case funs r of [] \<Rightarrow> ErrorResult (STR ''No function context'')
       | F1h#F1t \<Rightarrow>
        (case locals r of [] \<Rightarrow> ErrorResult (STR ''No local context'')
        | L1h#L1t \<Rightarrow>
          (case F1h name of
            None \<Rightarrow> (ErrorResult (STR ''Undefined function '' @@ name))
            | (Some (YulFunctionSig argSig retSig body)) \<Rightarrow>
              (case vals r of
                None \<Rightarrow> ErrorResult (STR ''invalid eval context (YulFunctionCallExpression)'')
                | Some vs \<Rightarrow>
                  (case put_values L1h (strip_id_types argSig) vs of
                    None \<Rightarrow> (ErrorResult (STR ''Argument arity mismatch for '' @@ name))
                    | Some Lsub \<Rightarrow>
                      (case put_values Lsub (strip_id_types retSig) 
                                            (List.replicate (length retSig) defaultValue) of
                        None \<Rightarrow> (ErrorResult (STR ''Should be dead code''))
                        | Some Lsub1 \<Rightarrow>
                          (case yul_eval_statement (YulBlock body) n
                                                   (YulResult (r1 \<lparr> locals := (Lsub1#L1h#L1t)\<rparr>)) of
                            ErrorResult r \<Rightarrow> ErrorResult r
                            | YulResult r2 \<Rightarrow>
                              (case get_values Lsub2 (strip_id_types retSig) of
                                None \<Rightarrow> ErrorResult (STR ''Return arity mismatch for '' @@ name)
                                | Some retVals \<Rightarrow> 
                                  YulResult (r2 \<lparr> locals := L1h#L1t
                                                , mode := None
                                                , vals := (Some retVals)\<rparr> ))))))))))"
| "yul_eval_expression _ _ (ErrorResult e) = ErrorResult e"

(*
 * helper: "canonicalized" switch
 *)
| "yul_eval_canonical_switch (YulSwitchCanonical e [] dfl) n (YulResult r) =
    (yul_eval_statements dfl n (YulResult r))"
(* canonicalization guarantees no defaults remain in cases list *)
| "yul_eval_canonical_switch (YulSwitchCanonical e (YulSwitchCase None _ # _) _) _ _ = 
    (ErrorResult (STR ''Non canonical switch statement''))"
| "yul_eval_canonical_switch 
    (YulSwitchCanonical e (YulSwitchCase (Some (YulLiteral hdValue _)) hdBody # rest) dfl) n 
      (YulResult r) =
    (case vals r of
      Some [condValue] \<Rightarrow>
        (case parseLiteral hdValue of
          None \<Rightarrow> ErrorResult (STR ''Bad literal '' @@ hdValue)
          | Some v \<Rightarrow>
            (if valueEq v condValue
             then yul_eval_statements hdBody n (YulResult r)
             else yul_eval_canonical_switch (YulSwitchCanonical e rest dfl) n (YulResult r)))
      | _ \<Rightarrow> ErrorResult (STR ''Bad switch condition''))"
| "yul_eval_canonical_switch _ _ (ErrorResult s) = ErrorResult s"

(* 
 * helper: statement list
 *)
| "yul_eval_statements [] n (YulResult r) = (YulResult (r \<lparr> mode := Some Regular \<rparr>))"
| "yul_eval_statements (sh#st) n (YulResult r) =
   (case yul_eval_statement sh n (YulResult r) of
    YulResult r1 \<Rightarrow> 
      (if mode r1 = Some Regular
       then yul_eval_statements st n (YulResult r1)
       else r1)
    | ErrorResult s \<Rightarrow> ErrorResult s)"
| "yul_eval_statements _ _ (ErrorResult s) = ErrorResult s"


(* helper: blocks
   (handle scoping, function gathering *)
(*
| "yul_eval_block
*)
(*
 * statement
 *)

(* have a separate yul_eval_block function? *)

(* blocks *)

| "yul_eval_statement (YulBlock sl) n (YulResult r) =
   yul_eval_block sl n (YulResult r)"

(* function definitions - TODO this needs to be a separate pass *)
(*
| "yul_eval_statement G L F 
    (YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body)) =
   (G, L, (put_value F name (YulFunctionSig args rets body)), Regular)"
*)

(* function call statement *)
| "yul_eval_statement (YulFunctionCallStatement fc) n (YulResult r) =
    (case yul_eval_expression (YulFunctionCallExpression fc) n (YulResult r) of  
      YulResult r1 \<Rightarrow> YulResult (r1 \<lparr> mode := Regular, vals := None \<rparr>)
      | ErrorResult s \<Rightarrow> ErrorResult s)"

(* variable declarations without definition *)
| "yul_eval_statement (YulVariableDeclarationStatement (YulVariableDeclaration names None)) n
    (YulResult r) =
  (case locals r of
    [] \<Rightarrow> ErrorResult (STR ''Empty list of local var contexts'')
    | (Lh#Lt) \<Rightarrow>
      (case put_values Lh (strip_id_types names)
                          (List.replicate (length names) defaultValue) of
        None \<Rightarrow> (ErrorResult (STR ''Arity mismatch in variable declaration - should be dead code''))
        | Some L1 \<Rightarrow> YulResult (r \<lparr> locals := L1#Lt \<rparr>)))"

(* variable declaration + definition *)
| "yul_eval_statement (YulVariableDeclarationStatement (YulVariableDeclaration names (Some expr))) n
                      (YulResult r) =
   yul_eval_statement (YulAssignmentStatement (YulAssignment (strip_id_types names) expr)) y
                      (YulResult r)"

(* assignments *)
| "yul_eval_statement (YulAssignmentStatement (YulAssignment ids expr)) n (YulResult r) =
    (case yul_eval_expression expr n (YulResult r) of
      ErrorResult s \<Rightarrow> ErrorResult s
      | YulResult r1 \<Rightarrow>
        (case locals r1 of
          [] \<Rightarrow> ErrorResult (STR ''Empty list of local var contexts'')
          | (Lh#Lt) \<Rightarrow>
            (case vals r1 of
              None \<Rightarrow> ErrorResult (STR ''Invalid returned expression state'')
              | Some v1 \<Rightarrow>
                (case put_values Lh ids v1 of
                  None \<Rightarrow> ErrorResult (STR ''Arity mismatch in assignment'')
                  | Some L2 \<Rightarrow> 
                    (YulResult (r1 \<lparr> locals := L2#Lt, mode := Some Regular, vals := None \<rparr>))))))"

(* if statement *)
| "yul_eval_statement (YulIf cond body) n (YulResult r) =
   (case yul_eval_expression cond n (YulResult r) of
    ErrorResult s \<Rightarrow> ErrorResult s
    | YulResult r1 \<Rightarrow>
      (case vals r1 of
        Some [v] \<Rightarrow>
          (if isTruthy v then yul_eval_statements body n 
                              (YulResult (r1 \<lparr> mode := Some Regular, vals := None \<rparr>))
           else (YulResult (r1 \<lparr> mode := Some Regular, vals := None \<rparr>)))
        | _ \<Rightarrow> (ErrorResult (STR ''Expression doesn't have 1 value (if condition)''))))"

(* for loops *)

(* for loops consume fuel *)
| "yul_eval_statement (YulForLoop _ _ _ _) 0 (YulResult r) = YulResult r"

(* process for-loop without pre-statements *)
| "yul_eval_statement (YulForLoop [] cond post body) (Suc n) (YulResult r) =
   (case yul_eval_expression cond (Suc n) (YulResult r) of
    ErrorResult s \<Rightarrow> ErrorResult s
    | YulResult r1 \<Rightarrow>
      (case vals r1 of
        Some [v] \<Rightarrow>
          (if isTruthy v then
            (case yul_eval_statements body (Suc n) (YulResult r1) of
              ErrorResult s \<Rightarrow> ErrorResult s
              | YulResult r2 \<Rightarrow>
                (case mode r2 of
                  None \<Rightarrow> ErrorResult (STR ''Invalid state after loop body'')
                  | Some Break \<Rightarrow> YulResult (r2 \<lparr> mode := Some Regular \<rparr>)
                  | Some Leave \<Rightarrow> YulResult r2
                  | Some _ \<Rightarrow> yul_eval_statement (YulForLoop [] cond post body) n (YulResult r2)))
            else YulResult (r1 \<lparr> mode := Some Regular, vals := None \<rparr>))
        | _ \<Rightarrow> ErrorResult (STR ''Expression doesn't have 1 value (loop condition)'')))"
     
(* process pre-statements for for-loop *)
| "yul_eval_statement (YulForLoop (preh#pret) cond post body) n (YulResult r) =
   (case yul_eval_statements (preh#pret) n (YulResult r) of
      ErrorResult s \<Rightarrow> ErrorResult s
      | YulResult r1 \<Rightarrow>
          \<comment> \<open>mode will be either Regular or Leave here\<close>
          (case mode r1 of
            None \<Rightarrow> ErrorResult (STR ''Invalid state after loop init'')
            | Some Leave \<Rightarrow> 
              (case (locals r1, locals r) of
                (L1h#L1t, Lh#Lt) \<Rightarrow>
                  \<comment> \<open> L1t and Lt should be equal here \<close>
                  YulResult (r1 \<lparr> locals := (restrict L1h Lh)#Lt \<rparr>) 
                | _ \<Rightarrow> ErrorResult (STR ''Invalid local contexts on loop init exit''))
            | Some _ \<Rightarrow>
              (case yul_eval_statement (YulForLoop [] cond post body) n 
                                       (YulResult r1) of
                ErrorResult s \<Rightarrow> ErrorResult s
                | YulResult r2 \<Rightarrow>
                  (case (locals r2, locals r) of
                    (L2h#L2t, Lh#Lt) \<Rightarrow>
                      \<comment> \<open> L2t and Lt should be equal here \<close>
                      YulResult (r2 \<lparr> locals := (restrict L2h Lh)#Lt \<rparr>)))))"


(* switch statement *)

| "yul_eval_statement (YulSwitch e cl) n (YulResult r) =
    (case yul_eval_expression e n (YulResult r) of
      ErrorResult s \<Rightarrow> ErrorResult s
      | YulResult r1 \<Rightarrow>
        (case vals r1 of
          Some [result] \<Rightarrow>
            (case canonicalizeSwitch e cl None of
              Some canonical \<Rightarrow> yul_eval_canonical_switch result canonical (YulResult r1)
              | None \<Rightarrow> ErrorResult (STR ''Invalid switch statement''))))"
 
(* break *)
| "yul_eval_statement YulBreak n (YulResult r) = 
    YulResult (r \<lparr> mode := Some Break \<rparr>)"

(* continue *)
| "yul_eval_statement YulContinue n (YulResult r) =
    YulResult (r \<lparr> mode := Some Continue \<rparr>)"

(* leave *)
| "yul_eval_statement YulLeave n (YulResult r) =
    YulResult (r \<lparr> mode := Some Leave \<rparr>)"

(* on errors, halt *)
| "yul_eval_statement _ _ (ErrorResult s) =
    ErrorResult s"


(* big-step inductive semantics for Yul programs *)
(* parameters:
   - global state
   - local state (variable map)
   - function identifiers
   - statement
   - return *)
(* NB official Yul interpreter appears to be
registering functions at the block level, rather than
as they appear syntactically.
*)
  by pat_completeness auto


(* measure for yul_eval function - based on gas *)
(* however we are also going to need a notion of how far in the syntax tree we are.
   then we should only need to use gas for the for loop piece *)
termination sorry (* TODO *)  
  

end

end