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


inductive yul_eval_st ::
  "'g \<Rightarrow> yul_value local \<Rightarrow> statement \<Rightarrow>
   ('g * yul_value local * mode) \<Rightarrow> bool" 
and
  yul_eval_sts ::
  "'g \<Rightarrow> yul_value local \<Rightarrow> statement list \<Rightarrow>
   ('g * yul_value local * mode) \<Rightarrow> bool" 
and
  yul_eval_e ::
   "'g \<Rightarrow> yul_value local \<Rightarrow> expression \<Rightarrow>
   ('g * yul_value local * yul_value list) \<Rightarrow> bool" 
and
  yul_eval_c ::
  "'g \<Rightarrow> yul_value local \<Rightarrow>
    yul_value list \<Rightarrow>  casest list \<Rightarrow> block \<Rightarrow>
   ('g * yul_value local * mode) \<Rightarrow> bool"
   where

(* statement lists*)
  "yul_eval_sts G L [] (G, L, Regular)"
| "yul_eval_st G L s1 (G1, L1, Regular) \<Longrightarrow>
    yul_eval_sts G1 L1 sl (Gn, Ln, mode) \<Longrightarrow>
    yul_eval_sts G L (s1#sl) (Gn, Ln, mode)"
| "yul_eval_st G L s1 (G1, L1, mode) \<Longrightarrow>
    yul_eval_sts G L (s1#sl) (G1, L1, mode)"

(* block *)
| "yul_eval_sts G L sl (G1, L1, mode) \<Longrightarrow>
   yul_eval_st G L (SB (Block sl)) (G1, restrict L1 L, mode)"

(* function definitions *)
(* TODO: have an environment for functions *)
| "yul_eval_st G L (SF _) (G, L, Regular)"

(* variable declarations *)
| "yul_eval_st G L (SA (Asgn (strip_id_types til) e)) (G1, L1, mode) \<Longrightarrow>
   yul_eval_st G L (SV (Var til (Some e))) (G1, L1, mode)"
| "put_values L (strip_id_types til)
                (List.replicate (til_length til) (VInt 0)) = Some L1 \<Longrightarrow>
    yul_eval_st G L (SV (Var il (None))) (G, L1, Regular)"

(* assignments *)
| "yul_eval_e G L e (G1, L1, vs) \<Longrightarrow>
   put_values L1 il vs = Some L2 \<Longrightarrow>
  yul_eval_st G L (SA (Asgn il e)) (G, L2, Regular)"

(* for loops *)
(* init block. scoping seems odd *)
| "yul_eval_sts G L (sh#st) (G1, L1, Regular) \<Longrightarrow>
   yul_eval_st G1 L1 (SL ( For (Block []) cond post body)) (G2, L2, Regular) \<Longrightarrow>
   yul_eval_st G L (SL (For ( Block (sh#st)) cond post body)) (G2, restrict L2 L, Regular)"
| "yul_eval_e G L cond (G1, L1, [VBool False]) \<Longrightarrow>
    yul_eval_st G L (SL (For (Block []) cond post body)) (G1, L1, Regular)"
| "yul_eval_e G L cond (G1, L1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 (SB body) (G2, L2, Break) \<Longrightarrow>
   yul_eval_st G L (SL (For (Block []) cond post body)) (G2, L2, Regular)"
| "yul_eval_e G L cond (G1, L1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 (SB body) (G2, L2, mode) \<Longrightarrow>
   yul_eval_st G2 L2 (SB post) (G3, L3, mode') \<Longrightarrow>
   yul_eval_st G3 L3 (SL (For (Block []) cond post body)) (G4, L4, mode) \<Longrightarrow>
   yul_eval_st G L (SL (For (Block []) cond post body)) (G4, L4, mode)"

(* break/continue *)
| "yul_eval_st G L (SX XBreak) (G, L, Break)"
| "yul_eval_st G L (SX XContinue) (G, L, Continue)"

(* if *)
| "yul_eval_e G L cond (G1, L1, [VBool True]) \<Longrightarrow>
   yul_eval_st G1 L1 (SB body) (G2, L2, mode) \<Longrightarrow>
   yul_eval_st G L (SI (Ifst cond body)) (G2, L2, mode)"
| "yul_eval_e G L cond (G1, L1, [VBool False]) \<Longrightarrow>
   yul_eval_st G L (SI (Ifst cond body)) (G1, L1, mode)"

(* switch *)
| "yul_eval_st G L (SS (Switch e c cs (Some (Default (Block []))))) (G1, L1, mode) \<Longrightarrow>
   yul_eval_st G L (SS (Switch e c cs None)) (G1, L1, mode)"
| "yul_eval_e G L e (G1, L1, vs) \<Longrightarrow>
   yul_eval_st G1 L1 (SB b) (G2, L2, mode) \<Longrightarrow>
   yul_eval_st G L (SS (Switch0 e (Default b))) (G2, L2, mode)"
(* we need to keep a bunch of global states around? *)

| "yul_eval_e G L e (G1, L1, vs) \<Longrightarrow>
   yul_eval_c G1 L1 vs (c#cs) d (G2, L2, mode) \<Longrightarrow>
   yul_eval_st G L (SS (Switch e c cs (Some (Default b)))) (G2, L2, mode)"

(* expressions as statements *)
| "yul_eval_e G L exp (G1, L1, []) \<Longrightarrow>
   yul_eval_st G L (SE exp) (G1, L1, Regular)"

(* cases - helper *)
| "yul_eval_st G L (SB d) (G1, L1, mode) \<Longrightarrow>
   yul_eval_c G L vs [] d (G1, L1, mode)"
| "yul_eval_e G L (EL (case_lit ch)) (_, _, vs) \<Longrightarrow>
   yul_eval_st G L (SB (case_block ch)) (G1, L1, mode) \<Longrightarrow>
   yul_eval_c G L vs ((ch)#ct) d (G1, L1, mode)"
| "yul_eval_e G L (EL (case_lit ch)) (_, _, vs') \<Longrightarrow>
   vs' \<noteq> vs \<Longrightarrow>
   yul_eval_c G L vs ct d (G1, L1, mode) \<Longrightarrow>
   yul_eval_c G L vs ((ch)#ct) d (G1, L1, mode)"

(* expressions *)

(* ids *)
| "L i = Some v \<Longrightarrow>
   yul_eval_e G L (EI i) (G, L, [v])"

(* function calls *)

(* hex literals: TODO *)

(* string literals: TODO *)

(* hex numbers: TODO *)

(* decimal numbers *)
(* note we  aren't really dealing with overflow *)
| "yul_eval_e G L (EL (NL (Nlit n))) (G, L, [VInt n])"

end

end