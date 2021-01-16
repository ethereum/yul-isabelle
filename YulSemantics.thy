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
function
yul_eval_statement ::
  "YulStatement \<Rightarrow> nat \<Rightarrow> ('g, 'v) YulResult \<Rightarrow> ('g, 'v) YulResult"
and yul_eval_statements ::
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
"yul_eval_expression (YulIdentifier i) n 
  (YulResult r) =
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
| "yul_eval_expression _ _ (ErrorResult e) = ErrorResult e"

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

(* 
 * helper: statement list
 *)
| "yul_eval_statements [] n (YulResult r) = (YulResult (r \<lparr> mode := Some Regular \<rparr>))"
| "yul_eval_statements (sh#st) n (YulResult r) =
   (case yul_eval_statement sh n (YulResult r) of
    YulResult r1 \<Rightarrow> 

    | ErrorResult s \<Rightarrow> ErrorResult s

      (if isError G1 then (G1, L1, F1, Regular)
       else yul_eval_statements G1 L1 F1 st)
    | (G1, L1, F1, mode) \<Rightarrow> (G1, L1, F1, mode))"

(*
 * helper: function arguments
 *)
| "yul_eval_args G L F [] = (G, L, F, [])"
| "yul_eval_args G L F (eh#et) =
   (case yul_eval_expression G L F eh of
      (G1, L1, F1, [vh]) \<Rightarrow>
        (case yul_eval_args G1 L1 F1 et of
          (Gn, Ln, Fn, vt) \<Rightarrow> (Gn, Ln, Fn, vh#vt))
      | _ \<Rightarrow> (error (STR ''Expression doesn't have 1 value (function argument)'') G, L, F, []))"

(*
 * statement
 *)

(* TODO should we allow redefinition of functions in inner scopes
to propagate back up to outer scopes? this seems bad *)
(* blocks *)
| "yul_eval_statement G L F (YulBlock sl) =
  (case yul_eval_statements G L F sl of
    (G1, L1, F1, mode) \<Rightarrow> (G1, restrict L1 L, F, mode))"

(* function definitions *)
| "yul_eval_statement G L F 
    (YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body)) =
   (G, L, (put_value F name (YulFunctionSig args rets body)), Regular)"

(* function call statement *)
| "yul_eval_statement G L F (YulFunctionCallStatement fc) =
    (case yul_eval_expression G L F (YulFunctionCallExpression fc) of
      (G1, L1, F1, _) \<Rightarrow> (G1, L1, F1, Regular))"

(* variable declarations *)
(* need a way to fill in values for undefined variables.
   for now let's use Isabelle undefined *)
(* idea: put_values, putting undefined if we have None on the RHS
   if we have Some, then evaluate it as an assignment *)
| "yul_eval_statement G L F
    (YulVariableDeclarationStatement (YulVariableDeclaration names None)) =
  (case put_values L (strip_id_types names) (List.replicate (length names) defaultValue) of
    None \<Rightarrow> (error (STR ''Should be dead code'') G, L, F, Regular)
    | Some L1 \<Rightarrow>  (G, L1 , F, Regular))"

(* variable declaration + definition *)
(* TODO: do we need to check gas again? i don't think we should. *)
| "yul_eval_statement G L F
    (YulVariableDeclarationStatement (YulVariableDeclaration names (Some expr))) =
   yul_eval_statement G L F (YulAssignmentStatement (YulAssignment (strip_id_types names) expr))"

(* assignments *)
| "yul_eval_statement G L F
    (YulAssignmentStatement (YulAssignment ids expr)) =
    (case yul_eval_expression G L F expr of
      (G1, L1, F1, vals) \<Rightarrow>
      (case put_values L1 ids vals of
        None \<Rightarrow> undefined
        | Some L2 \<Rightarrow> (G1, L2, F1, Regular)))"

(* if statement *)
| "yul_eval_statement G L F (YulIf cond body) =
   (case yul_eval_expression G L F cond of
    (G1, L1, F1, [v]) \<Rightarrow>
      (if truthy v then yul_eval_statements G L F body
       else (G, L, F, Regular))
    | _ \<Rightarrow> (error (STR ''Expression doesn't have 1 value (if condition)'') G, L, F, Regular))"

(* for loops *)

(* process for-loop without pre-statements *)
| "yul_eval_statement G L F (YulForLoop [] cond post body) =
   (case yul_eval_expression G L F cond of
    (G1, L1, F1, [v]) \<Rightarrow>
      (if truthy v
       then
        (case yul_eval_statements G1 L F1 body of
         (G2, L2, F2, mode) \<Rightarrow>
         (case mode of
          Break \<Rightarrow> (G2, L2, F2, Regular)
          | Leave \<Rightarrow> (G2, L2, F2, Leave)
          | _ \<Rightarrow> (case yul_eval_statements G2 L2 F2 post of
                  (G3, L3, F3, mode) \<Rightarrow>
                  (case mode of
                    Leave \<Rightarrow> (G2, L3, F2, Leave)
                    | _ \<Rightarrow> yul_eval_statement_check_gas G3 L3 F3 (YulForLoop [] cond post body)))))
       else (G1, L1, F1, Regular))
      | _ \<Rightarrow> undefined)"
     
(* process pre-statements for for-loop *)
(* TODO: I don't think we need to deduct gas when we do the final yul_eval_statement call
   because all we have done here is preprocess the loop structure *)
| "yul_eval_statement G L F (YulForLoop (preh#pret) cond post body) =
   (case yul_eval_statements G L F (preh#pret) of
        (G1, L1, F1, mode) \<Rightarrow>
          \<comment> \<open>mode will be either Regular or Leave here\<close>
          (case mode of
            Leave \<Rightarrow> (G1, restrict L1 L, F1, Leave)
            | _ \<Rightarrow>
              (case yul_eval_statement G L F (YulForLoop [] cond post body) of
                (G2, L2, F2, mode) \<Rightarrow> (G2, restrict L2 L, F2, mode))))"
                

(* switch statement *)

| "yul_eval_statement G L F (YulSwitch e cl) =
    (case yul_eval_expression G L F e of
      (G1, L1, F1, [result]) \<Rightarrow> 
        (case canonicalizeSwitch e cl None of
          Some canonical \<Rightarrow> yul_eval_canonical_switch G L F result canonical
          | _ \<Rightarrow> undefined)
      | _ \<Rightarrow> undefined)"
 
(* break *)
| "yul_eval_statement G L F YulBreak = (G, L, F, Break)"

(* continue *)
| "yul_eval_statement G L F YulContinue = (G, L, F, Continue)"

(* leave *)
| "yul_eval_statement G L F YulLeave = (G, L, F, Leave)"


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