theory YulSemantics imports "YulSyntax"
begin


datatype mode =
  Regular
  | Break
  | Continue
  | Leave

datatype yul_value =
  VInt int
  | VBool bool

datatype function_sig =
  YulFunctionSig
  (YulFunctionSigArguments: "YulTypedName list")
  (YulFunctionSigReturnValues: "YulTypedName list")
  (YulFunctionSigBody: "YulStatement list")

type_synonym 'v local = "YulIdentifier \<Rightarrow> 'v option"

definition local_empty :: "'v local" where
"local_empty = (\<lambda> _ . None)"

(* restrict e1 to the identifiers of e2 *)
definition restrict :: "'v local \<Rightarrow> 'v local \<Rightarrow> 'v local" where
"restrict e1 e2 i =
  (if e2 i = None then None
      else e1 i)"

fun strip_id_type :: "YulTypedName \<Rightarrow> YulIdentifier" where
"strip_id_type (YulTypedName name type) = name"

fun strip_id_types :: "YulTypedName list \<Rightarrow> YulIdentifier list" where
"strip_id_types l =
  List.map strip_id_type l"

fun put_value :: "'v local \<Rightarrow> YulIdentifier \<Rightarrow> 'v \<Rightarrow> 'v local" where
"put_value L i v =
  (\<lambda> i' . if i' = i then Some v else L i')"

fun put_values :: "'v local \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list \<Rightarrow> 'v local option" where
"put_values L [] [] = Some L"
| "put_values L (ih#it) (vh#vt) =
   (case put_values L it vt of
    None \<Rightarrow> None
    | Some L' \<Rightarrow> Some (put_value L' ih vh))"
| "put_values L _ _ = None"

fun get_values :: "'v local \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list option" where
"get_values L ids =
   List.those (List.map L (ids))"

fun get_min :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> 'a" where
"get_min f aset =
  (SOME a . a \<in> aset \<and>
            (\<forall> a' \<in> aset . f a' \<le> f a \<longrightarrow> a = a'))"

datatype YulSwitchCanonical =
  YulSwitchCanonical
    (YulSwitchCanonicalExpression: YulExpression)
    (YulSwitchCanonicalCases: "YulSwitchCase list")
    (YulSwitchCanonicalDefault : "YulStatement list")

(* idea: reorganize the switch statement so that
   - if there is no default, we add an empty one
   - pick out the default case specially either way *)
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

syntax plus_literal_inst.plus_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
  ("_ @@ _")

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

  fixes gasCost :: "YulStatement \<Rightarrow> nat"
  fixes gas :: "'g \<Rightarrow> nat"
  fixes updateGas :: "nat \<Rightarrow> 'g \<Rightarrow> 'g"

  fixes truthy :: "'v \<Rightarrow> bool"
  (* for declared, undefined variables *)
  fixes defaultValue :: "'v"
  (* comparison of values for use in switch *)
  fixes valueEq :: "'v \<Rightarrow> 'v \<Rightarrow> bool"

  fixes error :: "String.literal \<Rightarrow> 'g \<Rightarrow> 'g"
  fixes getError :: "'g \<Rightarrow> String.literal option"

  (* TODO: probably need more primitives for type reasoning *)
  fixes parseType :: "String.literal \<Rightarrow> 't option"
  fixes parseLiteral :: "String.literal \<Rightarrow> 'v option"

  assumes gas_decrease :
    "\<And> s . gasCost s > 0"
  assumes gas_lens1 :
    "\<And> g . updateGas (gas g) g = g"
  assumes gas_lens2 :
    "\<And> n g . gas (updateGas n g) = n"
  assumes gas_lens3 :
    "\<And> n n' g . 
      updateGas n (updateGas n' g) = updateGas n g"

  assumes error_isError :
    "\<And> msg G . getError (error msg G) = Some msg"

assumes updateGas_pres :
    "\<And> G g . getError G = getError (updateGas g G)"

begin

fun isError :: "'g \<Rightarrow> bool" where
"isError G =
  (case getError G of
    None \<Rightarrow> False
    | Some _ \<Rightarrow> True)"

fun decrement_gas ::
    "'g \<Rightarrow> YulStatement \<Rightarrow> 'g" where
"decrement_gas G st =
  (if gas G < gasCost st then error (STR ''Out of gas'') G
   else updateGas (gas G - gasCost st) G)"

lemma decrement_gas_correct :
  assumes Ok : "\<not> isError G"
  shows "isError (decrement_gas G st) \<or> gas (decrement_gas G st) < gas G"
proof(cases "gas G < gasCost st")
  case True

  hence Bad : "isError (decrement_gas G st)"
    by(simp add: error_isError)

  thus ?thesis by auto
next
  case False

  hence Good : "gas (decrement_gas G st) < gas G" using gas_decrease[of st]
    by(simp add: gas_lens2)

  thus ?thesis by auto
qed


(* gas checks will happen on statement *)
function
yul_eval_statement_check_gas ::
    "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> YulStatement \<Rightarrow>
    ('g * 'v local * function_sig local * mode)"
and yul_eval_statement ::
  "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> YulStatement \<Rightarrow>
   ('g * 'v local * function_sig local * mode)"
and yul_eval_statements ::
  "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> YulStatement list \<Rightarrow>
   ('g * 'v local * function_sig local * mode)"
and yul_eval_expression ::
   "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> YulExpression \<Rightarrow>
   ('g * 'v local * function_sig local * 'v list)"
and yul_eval_canonical_switch ::
 "'g \<Rightarrow> 'v local \<Rightarrow> function_sig local \<Rightarrow> 'v \<Rightarrow> YulSwitchCanonical \<Rightarrow>
   ('g * 'v local * function_sig local * mode)"  
and yul_eval_args ::
  "'g \<Rightarrow> 'v local \<Rightarrow>
    function_sig local \<Rightarrow>
    YulExpression list \<Rightarrow>
    ('g * 'v local * function_sig local * 'v list)" 
  where

(* gas checking (entry point) *)
"yul_eval_statement_check_gas G L F st =
  (let G' = decrement_gas G st in
    (if isError G' then (G', L, F, Regular)
     else yul_eval_statement G' L F st))"

(*
 * helper: expression
 *)
(* identifier *)
| "yul_eval_expression G L F (YulIdentifier i) =
 (case (L i) of
  None \<Rightarrow> (error (STR ''Undefined variable '' @@ i) G, L, F, []) 
  | Some v \<Rightarrow> (G, L, F, [v]))"
(* literal *)
| "yul_eval_expression G L F (YulLiteralExpression (YulLiteral value type)) =
  (case parseLiteral value of
    Some v \<Rightarrow> (G, L, F, [v])
    | None \<Rightarrow> (error (STR ''Bad literal '' @@ value) G, L, F, []))"

(* function call *)
(* TODO: evaluate function body as a block or as "raw" statements? *)
| "yul_eval_expression G L F (YulFunctionCallExpression (YulFunctionCall name args)) =
   (case yul_eval_args G L F args of
    (G1, L1, F1, vals) \<Rightarrow>
      (case F1 name of
        None \<Rightarrow> (error (STR ''Undefined function '' @@ name) G1, L1, F1, [])
        | (Some (YulFunctionSig argSig retSig body)) \<Rightarrow>
          (case put_values local_empty (strip_id_types argSig) vals of
          None \<Rightarrow> (error (STR ''Argument arity mismatch for '' @@ name) G1, L1, F1, [])
          | Some Lsub \<Rightarrow>
            (case put_values Lsub (strip_id_types retSig) 
                                  (List.replicate (length retSig) defaultValue) of
              None \<Rightarrow> (error (STR ''Should be dead code'') G1, L1, F1, [])
              | Some Lsub1 \<Rightarrow>
                (case yul_eval_statement_check_gas G1 Lsub1 F1 (YulBlock body) of
                  (G2, Lsub2, _, mode) \<Rightarrow> 
                  (if isError G2 then (G2, L1, F1, [])
                    else 
                    (case get_values Lsub2 (strip_id_types retSig) of
                      None \<Rightarrow> (error(STR ''Return arity mismatch for '' @@ name) G2, L1, F1, [])
                      | Some retVals \<Rightarrow> (G2, L1, F1, retVals))))))))"

(*
 * helper: "canonicalized" switch
 *)
(*
 * TODO: handle gas consumption of switch cases
 *)
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e [] dfl) =
    (yul_eval_statements G L F dfl)"
(* canonicalization guarantees no defaults remain in cases list *)
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e (YulSwitchCase None _ # _) _) = 
    (error (STR ''Non canonical switch statement'') G, L, F, Regular)"
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e (YulSwitchCase (Some (YulLiteral hdValue _)) hdBody # rest) dfl) =
    (case parseLiteral hdValue of
      None \<Rightarrow> (error (STR ''Bad literal '' @@ hdValue) G, L, F, Regular)
      | Some v \<Rightarrow>
        (if valueEq v condValue
         then yul_eval_statements G L F hdBody
         else yul_eval_canonical_switch G L F condValue (YulSwitchCanonical e rest dfl)))"

(* 
 * helper: statement list
 *)
| "yul_eval_statements G L F [] = (G, L, F, Regular)"
| "yul_eval_statements G L F (sh#st) =
   (case yul_eval_statement G L F sh of
    (G1, L1, F1, Regular) \<Rightarrow> 
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
termination
  apply(relation 
      "measure 
        (\<lambda> x .
          (case x of
              \<comment> \<open> yul_eval_statement_check_gas \<close>
              Inl (Inl (G, L, F, st)) \<Rightarrow> 
                if isError G then 0 else gas G + 1 + yulStatementMeasure st
              \<comment> \<open> yul_eval_statement \<close>
              | Inl (Inr (Inl (G, L, F, st))) \<Rightarrow> gas G + 1 + yulStatementMeasure st
              \<comment> \<open> yul_eval_statements \<close>
              | Inl (Inr (Inr (G, L, F, sts))) \<Rightarrow> gas G + 1 + yulStatementsMeasure sts
              \<comment> \<open> yul_eval_expression \<close>
              | Inr (Inl (G, L, F, e)) \<Rightarrow> gas G + 1 + yulExpressionMeasure e
              \<comment> \<open> yul_eval_canonical_switch \<close>
              | Inr (Inr (Inl (G, L, F, cond, sw))) \<Rightarrow> 
                gas G + 1 + yulSwitchCanonicalMeasure sw
              \<comment> \<open> yul_eval_args \<close>
              | Inr (Inr (Inr (G, L, F, args))) \<Rightarrow> 
                gas G + 1 + yulExpressionsMeasure args))")
                      apply(auto simp add: error_isError updateGas_pres gas_lens2 gas_decrease split:option.splits if_splits)
                     apply(cut_tac s = st in gas_decrease) apply(auto)
  defer
  
  

end

end