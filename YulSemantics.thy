theory YulSemantics imports "YulSyntax"
begin


datatype mode =
  Regular
  | Break
  | Continue

datatype yul_value =
  VInt int
  | VBool bool

type_synonym 'v local = "identifier \<Rightarrow> 'v option"

definition local_empty :: "'v local" where
"local_empty = (\<lambda> _ . None)"

(* restrict e1 to the identifiers of e2 *)
definition restrict :: "'v local \<Rightarrow> 'v local \<Rightarrow> 'v local" where
"restrict e1 e2 i =
  (if e2 i = None then None
      else e1 i)"

fun il_length :: "identifier_list \<Rightarrow> nat" where
"il_length (Ids _ l) = List.length l + 1"

fun til_length :: "typed_identifier_list \<Rightarrow> nat" where
"til_length (TIds _ l) = List.length l + 1"

fun strip_id_types :: "typed_identifier_list \<Rightarrow> identifier_list" where
"strip_id_types (TIds (i1, t1) itl) =
  Ids i1 (List.map fst itl)"

fun put_values :: "'v local \<Rightarrow> identifier_list \<Rightarrow> 'v list \<Rightarrow> 'v local option" where
"put_values L (Ids i ids) [] = None"
| "put_values L (Ids i ids) (vh#vs) =
   (if List.length ids = List.length vs 
    then 
    Some (List.fold (\<lambda> (i, v) L . 
            (\<lambda> i' . (if i' = i then Some v else L i')))
          (List.zip (i#ids) (vh#vs))
          L)
    else None)"

fun get_values :: "'v local \<Rightarrow> identifier_list \<Rightarrow> 'v list option" where
"get_values L (Ids i ids) =
   List.those (List.map L (i#ids))"

fun get_min :: "('a \<Rightarrow> nat) \<Rightarrow> 'a set \<Rightarrow> 'a" where
"get_min f aset =
  (SOME a . a \<in> aset \<and>
            (\<forall> a' \<in> aset . f a' \<le> f a \<longrightarrow> a = a'))"

fun case_lit :: "casest \<Rightarrow> literal" where
"case_lit (Case l _) = l"

fun case_block :: "casest \<Rightarrow> block" where
"case_block (Case _ b) = b"

(* locale for fixing global state, value types *)
locale YulSem =
  fixes v_int :: "int \<Rightarrow> 'v"
  fixes v_get_int :: "'v \<Rightarrow> int option"
begin

(* big-step inductive semantics for Yul programs *)
print_context

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
inductive yul_eval_st ::
  "'g \<Rightarrow> yul_value local \<Rightarrow> function_sig local \<Rightarrow> statement \<Rightarrow>
   ('g * yul_value local * function_sig  local * mode) \<Rightarrow> bool" 
and
  yul_eval_sts ::
  "'g \<Rightarrow> yul_value local \<Rightarrow> function_sig  local \<Rightarrow> statement list \<Rightarrow>
   ('g * yul_value local * function_sig  local * mode) \<Rightarrow> bool" 
and
  yul_eval_e ::
   "'g \<Rightarrow> yul_value local \<Rightarrow> function_sig  local \<Rightarrow> expression \<Rightarrow>
   ('g * yul_value local * function_sig  local * yul_value list) \<Rightarrow> bool" 
and
  yul_eval_c ::
  "'g \<Rightarrow> yul_value local \<Rightarrow>
    function_sig local \<Rightarrow>
    yul_value list \<Rightarrow>  casest list \<Rightarrow> block \<Rightarrow>
   ('g * yul_value local * function_sig  local *  mode) \<Rightarrow> bool"
and yul_eval_args ::
  "'g \<Rightarrow> yul_value local \<Rightarrow>
    function_sig local \<Rightarrow>
    expression list \<Rightarrow>
    ('g * yul_value local * function_sig local * yul_value list) \<Rightarrow> bool"
   where

(* statement lists*)
  "yul_eval_sts G L F [] (G, L, F, Regular)"
| "yul_eval_st G L F s1 (G1, L1, F1, Regular) \<Longrightarrow>
    yul_eval_sts G1 L1 F1 sl (Gn, Ln, Fn, mode) \<Longrightarrow>
    yul_eval_sts G L F (s1#sl) (Gn, Ln, Fn, mode)"
| "yul_eval_st G L F s1 (G1, L1, F1, mode) \<Longrightarrow>
    mode \<noteq> Regular \<Longrightarrow>
    yul_eval_sts G L F (s1#sl) (G1, L1, F1, mode)"

(* block *)
(* function definitions have block scoping. *)
(* TODO should we allow redefinition of functions in inner scopes
to propagate back up to outer scopes? this seems bad *)
| "yul_eval_sts G L F sl (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_st G L F (SB (Block sl)) (G1, restrict L1 L, F, mode)"

(* function definitions *)
| " put_values F (Ids idn []) [sig] = Some F1 \<Longrightarrow>
    yul_eval_st G L F (SF (Fun idn sig)) (G, L, F1, Regular)"

(* variable declarations *)
| "yul_eval_st G L F (SA (Asgn (strip_id_types til) e)) (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_st G L F (SV (Var til (Some e))) (G1, L1, F1, mode)"
| "put_values L (strip_id_types til)
                (List.replicate (til_length til) (VInt 0)) = Some L1 \<Longrightarrow>
    yul_eval_st G L F (SV (Var il (None))) (G, L1, F1, Regular)"

(* assignments *)
| "yul_eval_e G L F e (G1, L1, F1, vs) \<Longrightarrow>
   put_values L1 il vs = Some L2 \<Longrightarrow>
  yul_eval_st G L F (SA (Asgn il e)) (G, L2, F1, Regular)"

(* for loops *)
(* init block. scoping seems odd *)
| "yul_eval_sts G L F (sh#st) (G1, L1, F1, Regular) \<Longrightarrow>
   yul_eval_st G1 L1 F1 (SL ( For (Block []) cond post body)) (G2, L2, F2, Regular) \<Longrightarrow>
   yul_eval_st G L F (SL (For ( Block (sh#st)) cond post body)) (G2, restrict L2 L, F2, Regular)"
| "yul_eval_e G L F cond (G1, L1, F1, [VBool False]) \<Longrightarrow>
    yul_eval_st G L F (SL (For (Block []) cond post body)) (G1, L1, F1, Regular)"
| "yul_eval_e G L F cond (G1, L1, F1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 F1 (SB body) (G2, L2, F2, Break) \<Longrightarrow>
   yul_eval_st G L F (SL (For (Block []) cond post body)) (G2, L2, F2, Regular)"
(* TODO: double check threading of mode return here *)
| "yul_eval_e G L F cond (G1, L1, F1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 F1 (SB body) (G2, L2, F2, mode) \<Longrightarrow>
   yul_eval_st G2 L2 F2 (SB post) (G3, L3, F3, mode') \<Longrightarrow>
   yul_eval_st G3 L3 F3 (SL (For (Block []) cond post body)) (G4, L4, F4, mode'') \<Longrightarrow>
   yul_eval_st G L F (SL (For (Block []) cond post body)) (G4, L4, F4, mode'')"

(* break/continue *)
| "yul_eval_st G L F (SX XBreak) (G, L, F, Break)"
| "yul_eval_st G L F (SX XContinue) (G, L, F, Continue)"

(* if *)
| "yul_eval_e G L F cond (G1, L1, F1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 F1 (SB body) (G2, L2, F2, mode) \<Longrightarrow>
   yul_eval_st G L F (SI (Ifst cond body)) (G2, L2, F2, mode)"
| "yul_eval_e G L F cond (G1, L1, F1, [VBool False]) \<Longrightarrow>
   yul_eval_st G L F (SI (Ifst cond body)) (G1, L1, F1, mode)"

(* switch 
   there is an overlap in the first two cases here. *)
| "yul_eval_st G L F (SS (Switch e c cs (Some (Default (Block []))))) (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_st G L F (SS (Switch e c cs None)) (G1, L1, F1, mode)"
| "yul_eval_e G L F e (G1, L1, F1, vs) \<Longrightarrow>
   yul_eval_st G1 L1 F1 (SB b) (G2, L2, F2, mode) \<Longrightarrow>
   yul_eval_st G L F (SS (Switch0 e (Default b))) (G2, L2, F2, mode)"

| "yul_eval_e G L F e (G1, L1, F1, vs) \<Longrightarrow>
   yul_eval_c G1 L1 F1 vs (c#cs) d (G2, L2, F2, mode) \<Longrightarrow>
   yul_eval_st G L F (SS (Switch e c cs (Some (Default b)))) (G2, L2, F2, mode)"

(* expressions as statements *)
| "yul_eval_e G L F exp (G1, L1, F1, []) \<Longrightarrow>
   yul_eval_st G L F (SE exp) (G1, L1, F1, Regular)"

(* cases - helper *)
| "yul_eval_st G L F (SB d) (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_c G L F vs [] d (G1, L1, F1, mode)"
| "yul_eval_e G L F (EL (case_lit ch)) (_, _, _, vs) \<Longrightarrow>
   yul_eval_st G L F (SB (case_block ch)) (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_c G L F vs ((ch)#ct) d (G1, L1, F1, mode)"
| "yul_eval_e G L F (EL (case_lit ch)) (_, _, _, vs') \<Longrightarrow>
   vs' \<noteq> vs \<Longrightarrow>
   yul_eval_c G L F vs ct d (G1, L1, F1, mode) \<Longrightarrow>
   yul_eval_c G L F vs ((ch)#ct) d (G1, L1, F1, mode)"

(* function arguments - helper *)
(*
and yul_eval_args ::
  "'g \<Rightarrow> yul_value local \<Rightarrow>
    function_sig local \<Rightarrow>
    expression list \<Rightarrow>
    yul_value list \<Rightarrow> 
    ('g * yul_value local * function_sig local * yul_value list) \<Rightarrow> bool"
   where
*)
| "yul_eval_args G L F [] (G, L, F, vs)"
| "yul_eval_e G L F e (G1, L1, F1, [v]) \<Longrightarrow>
   yul_eval_args G1 L1 F1 es (G2, L2, F2, vs) \<Longrightarrow>
   yul_eval_args G L F (e#es) (G, L, F, v#vs)"

(* expressions *)

(* ids *)
| "L i = Some v \<Longrightarrow>
   yul_eval_e G L F (EI i) (G, L, F, [v])"

(* function calls *)
(* note that we do not pull any values from global scope into local scope here *)
| " yul_eval_args G L F exs (G1, L1, F1, vals) \<Longrightarrow>
    F1 idn = Some (FSig parms rets body) \<Longrightarrow>
    put_values local_empty (strip_id_types parms) vals = Some Lsub \<Longrightarrow>
    put_values Lsub (strip_id_types rets) (List.replicate (til_length rets) (VInt 0)) = Some LSub1 \<Longrightarrow>
    yul_eval_st G1 Lsub1 F1 (SB blk) (G2, Lsub2, _, mode) \<Longrightarrow>
    get_values Lsub2 (strip_id_types rets) = Some rvals \<Longrightarrow>
    yul_eval_e G L F (EF (Call idn exs)) (G2, L1, F1, rvals)"

(*     put_values L1 (strip_id_types rets) rvals = Some L2 \<Longrightarrow>
 *)

(* hex literals: TODO *)

(* string literals: TODO *)

(* hex numbers: TODO *)

(* decimal numbers *)
(* note we  aren't really dealing with overflow *)
| "yul_eval_e G L F (EL (NL (Nlit n))) (G, L, F, [VInt n])"

end

end