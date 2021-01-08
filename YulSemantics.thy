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

(*
fun il_length :: "identifier_list \<Rightarrow> nat" where
"il_length (Ids _ l) = List.length l + 1"

fun til_length :: "typed_identifier_list \<Rightarrow> nat" where
"til_length (TIds _ l) = List.length l + 1"
*)

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

(* bogus temporary definition for "truthy" Yul values *)
fun isTruthy :: "YulLiteralValue \<Rightarrow> bool" where
"isTruthy str = 
  (if str = STR ''0'' then False
   else True)"

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

(* executable semantics for Yul programs *)
(* parameters:
   - global state
   - local state (variable map)
   - function identifiers
   - statement
   - return *)

(* TODO: do we need to maintain the typing environment at runtime?
   I don't think we should. *)
fun yul_eval_statement :: 
  "'g \<Rightarrow> YulLiteralValue local \<Rightarrow> function_sig local \<Rightarrow> YulStatement \<Rightarrow>
   ('g * YulLiteralValue local * function_sig local * mode)"
and yul_eval_statements ::
  "'g \<Rightarrow> YulLiteralValue local \<Rightarrow> function_sig local \<Rightarrow> YulStatement list \<Rightarrow>
   ('g * YulLiteralValue local * function_sig local * mode)"
and yul_eval_expression ::
   "'g \<Rightarrow> YulLiteralValue local \<Rightarrow> function_sig local \<Rightarrow> YulExpression \<Rightarrow>
   ('g * YulLiteralValue local * function_sig local * YulLiteralValue list)"
and yul_eval_canonical_switch ::
 "'g \<Rightarrow> YulLiteralValue local \<Rightarrow> function_sig local \<Rightarrow> YulLiteralValue \<Rightarrow> YulSwitchCanonical \<Rightarrow>
   ('g * YulLiteralValue local * function_sig local * mode)"  
and yul_eval_args ::
  "'g \<Rightarrow> YulLiteralValue local \<Rightarrow>
    function_sig local \<Rightarrow>
    YulExpression list \<Rightarrow>
    ('g * YulLiteralValue local * function_sig local * YulLiteralValue list)" 
where

(*
 * helper: expression
 *)
(* identifier *)
"yul_eval_expression G L F (YulIdentifier i) =
 (case (L i) of
  None \<Rightarrow> (G, L, F, undefined) \<comment> \<open>bogus error case \<close>
  | Some v \<Rightarrow> (G, L, F, [v]))"
(* literal *)
| "yul_eval_expression G L F (YulLiteralExpression (YulLiteral value type)) =
   (G, L, F, [value])"
(* function call *)
(* TODO: evaluate function body as a block or as "raw" statements? *)
| "yul_eval_expression G L F (YulFunctionCallExpression (YulFunctionCall name args)) =
   (case yul_eval_args G L F args of
    (G1, L1, F1, vals) \<Rightarrow>
      (case F1 name of
        None \<Rightarrow> (G1, L1, F1, undefined) \<comment> \<open>bogus error case \<close>
        | (Some (YulFunctionSig argSig retSig body)) \<Rightarrow>
          (case put_values local_empty (strip_id_types argSig) vals of
          None \<Rightarrow> (G1, L1, F1, undefined) \<comment> \<open>bogus error case \<close>
          | Some Lsub \<Rightarrow>
            (case put_values Lsub (strip_id_types retSig) (List.replicate (length retSig) 0) of
            None \<Rightarrow> (G1, L1, F1, undefined) \<comment> \<open>bogus error case \<close>
            | Some Lsub1 \<Rightarrow>
              (case yul_eval_statement G1 Lsub1 F1 (YulBlock body) of
                (G2, Lsub2, _, mode) \<Rightarrow>
                (case get_values Lsub2 (strip_id_types retSig) of
                  None \<Rightarrow> (G1, L1, F1, undefined) \<comment> \<open>bogus error case \<close>
                  | Some retVals \<Rightarrow> (G2, L1, F1, retVals)))))))"

(*
 * helper: "canonicalized" switch
 *)
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e [] dfl) =
    (yul_eval_statements G L F dfl)"
(* canonicalization guarantees no defaults remain in cases list *)
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e (YulSwitchCase None _ # _) _) = undefined"
| "yul_eval_canonical_switch G L F condValue
    (YulSwitchCanonical e (YulSwitchCase (Some (YulLiteral hdValue _)) hdBody # rest) dfl) =
    (if hdValue = condValue
     then yul_eval_statements G L F hdBody
     else yul_eval_canonical_switch G L F condValue (YulSwitchCanonical e rest dfl))
    "

(* 
 * helper: statement list
 *)
| "yul_eval_statements G L F [] = (G, L, F, Regular)"
| "yul_eval_statements G L F (sh#st) =
   (case yul_eval_statement G L F sh of
    (G1, L1, F1, Regular) \<Rightarrow> yul_eval_statements G1 L1 F1 st
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
      | _ \<Rightarrow> undefined)"

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

(* variable declarations *)
(* need a way to fill in values for undefined variables.
   for now let's use Isabelle undefined *)
(* idea: put_values, putting undefined if we have None on the RHS
   if we have Some, then evaluate it as an assignment *)
| "yul_eval_statement G L F
    (YulVariableDeclarationStatement (YulVariableDeclaration names None)) =
  (case put_values L (strip_id_types names) (List.replicate (length names) undefined) of
    None \<Rightarrow> (G, L, F, Regular) \<comment> \<open>bogus error case \<close>
    | Some L1 \<Rightarrow>  (G, L1 , F, Regular))"
(* variable declaration + definition *)
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
      (if isTruthy v then yul_eval_statements G L F body
       else (G, L, F, Regular))
    | _ \<Rightarrow> undefined)"

(* for loops *)

(* process for-loop without pre-statements *)
| "yul_eval_statement G L F (YulForLoop [] cond post body) =
   (case yul_eval_expression G L F cond of
    (G1, L1, F1, [v]) \<Rightarrow>
      (if isTruthy v
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
                    | _ \<Rightarrow> yul_eval_statement G3 L3 F3 (YulForLoop [] cond post body)))))
       else (G1, L1, F1, Regular))
      | _ \<Rightarrow> undefined)"
     
(* process pre-statements for for-loop *)
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

(* locale for fixing global state, value types *)
locale YulSem =
  fixes v_int :: "int \<Rightarrow> 'v"
  fixes v_get_int :: "'v \<Rightarrow> int option"
begin

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

end

end