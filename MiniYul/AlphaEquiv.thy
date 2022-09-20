theory AlphaEquiv imports Semantics
begin

value "impl_of empty :: ((String.literal * unit) list)"

type_synonym subst' = "(name, name) oalist"

definition subst'_valid :: "subst' \<Rightarrow> bool" where
"subst'_valid subst =
  distinct (map snd (impl_of subst))"

type_synonym subst = "(name, name) oalist list"

definition subst_valid :: "subst \<Rightarrow> bool" where
"subst_valid subst = 
  list_all subst'_valid subst"

fun subst_get :: "subst \<Rightarrow> String.literal \<Rightarrow> name option" where
  "subst_get [] s = None"
| "subst_get (hl#t) s =
   (case get hl s of
    Some v \<Rightarrow> Some v
    | None \<Rightarrow> subst_get t s)"

fun subst_gets :: "subst \<Rightarrow> name list \<Rightarrow> name list option" where
  "subst_gets vm [] = Some []"
| "subst_gets vm (nh # nt) =
   (case subst_get vm nh of
    None \<Rightarrow> None
    | Some vh \<Rightarrow>
      (case subst_gets vm nt of
       None \<Rightarrow> None
       | Some vt \<Rightarrow> Some (vh#vt)))"

fun subst_insert :: "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> subst" where
  "subst_insert [] s i = []" (* bogus *)
| "subst_insert (hl#t) s i =
   update s i hl # t"

fun subst_inserts :: "subst \<Rightarrow> (name * name) list \<Rightarrow> subst" where
"subst_inserts vm [] = vm"
| "subst_inserts vm ((n, v)#t) =
   subst_inserts (subst_insert vm n v) t"

fun subst_update :: "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> subst" where
  "subst_update [] s i = []" (* bogus *)
| "subst_update (hl#t) s i =
   (case get hl s of
    Some _ \<Rightarrow> (update s i hl #t)
    | None \<Rightarrow> hl # subst_update t s i)"

fun subst_updates :: "subst \<Rightarrow> (name * name) list \<Rightarrow> subst" where
"subst_updates vm [] = vm"
| "subst_updates vm ((n, v)#t) =
   subst_updates (subst_update vm n v) t"

fun subst_push :: "subst \<Rightarrow> subst" where
"subst_push x = (empty#x)"

fun subst_pop :: "subst \<Rightarrow> subst" where
"subst_pop [] = []"
| "subst_pop (h#t) = t"

(*
definition alpha_equiv_name' :: "subst' \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool"
  where
"alpha_equiv_name' subst n1 n2 =
  (get subst n1 = Some n2)"

definition alpha_equiv_name :: "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool"
  where
"alpha_equiv_name subst n1 n2 =
  (subst_get subst n1 = Some n2)"
*)

definition alpha_equiv_name' ::
  "subst' \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool" where
"alpha_equiv_name' subst n1 n2 = 
   (case (get subst n1, get (oalist_flip subst) n2) of
    (Some n2', Some n1') \<Rightarrow> (n1 = n1' \<and> n2 = n2')
    | _ \<Rightarrow> False)"

(* makes sure a pair of variables are mapped to each other
 * at the _same_ scope depth.
 *)
fun alpha_equiv_name ::
  "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool" where
"alpha_equiv_name [] n1 n2 = False"
| "alpha_equiv_name
    (sh#st) n1 n2 =
   (case (get sh n1, get (oalist_flip sh) n2) of
    (Some n2', Some n1') \<Rightarrow> (n1 = n1' \<and> n2 = n2')
    | (None, None) \<Rightarrow> alpha_equiv_name st n1 n2
    | _ \<Rightarrow> False)"

fun alpha_equiv_expr1 ::
  "subst \<Rightarrow> expr1 \<Rightarrow> expr1 \<Rightarrow> bool" where
"alpha_equiv_expr1 subst (ELit i1) (ELit i2) =
  (i1 = i2)"
| "alpha_equiv_expr1 subst (EVar n1) (EVar n2) =
  (alpha_equiv_name subst n1 n2)"
| "alpha_equiv_expr1 _ _ _ = False"


fun alpha_equiv_expr :: "subst' \<Rightarrow> subst \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" where
"alpha_equiv_expr fsubst vsubst (E1 l1) (E1 l2) =
  list_all2 (alpha_equiv_expr1 vsubst) l1 l2"
| "alpha_equiv_expr fsubst vsubst (EPrim n1 l1) (EPrim n2 l2) =
  (alpha_equiv_name' fsubst n1 n2 \<and>
   list_all2 (alpha_equiv_expr1 vsubst) l1 l2)"
| "alpha_equiv_expr fsubst vsubst (EFun n1 l1) (EFun n2 l2) =
  (alpha_equiv_name' fsubst n1 n2 \<and>
   list_all2 (alpha_equiv_expr1 vsubst) l1 l2)"
| "alpha_equiv_expr _ _ _ _ = False"
  

fun alpha_equiv_stmt ::
  "subst' \<Rightarrow> subst \<Rightarrow> 'g fctx \<Rightarrow> 'g fctx \<Rightarrow> statement \<Rightarrow> statement \<Rightarrow> bool" where
"alpha_equiv_stmt fsubst vsubst ctx1 ctx2
  (SBlock ns1 stms1) (SBlock ns2 stms2) =
    (distinct ns1 \<and> distinct ns2 \<and>
     length ns1 = length ns2 \<and>
    (list_all2 (alpha_equiv_stmt fsubst (to_oalist (zip ns1 ns2) # vsubst) ctx1 ctx2) stms1 stms2))"
| "alpha_equiv_stmt fsubst vsubst ctx1 ctx2
  (SAssn ns1 e1) (SAssn ns2 e2) =
    (list_all2 (alpha_equiv_name vsubst) ns1 ns2 \<and> 
     alpha_equiv_expr fsubst vsubst e1 e2)"
| "alpha_equiv_stmt fsubst vsubst ctx1 ctx2
  (SIf e1 stm1a stm1b) (SIf e2 stm2a stm2b) =
    (alpha_equiv_expr1 vsubst e1 e2 \<and>
     alpha_equiv_stmt fsubst vsubst ctx1 ctx2 stm1a stm2a \<and>
     alpha_equiv_stmt fsubst vsubst ctx1 ctx2 stm1b stm2b)"
| "alpha_equiv_stmt fsubst vsubst ctx1 ctx2
  (SWhile e1 stm1) (SWhile e2 stm2) =
    (alpha_equiv_expr1 vsubst e1 e2 \<and>
     alpha_equiv_stmt fsubst vsubst ctx1 ctx2 stm1 stm2)"
| "alpha_equiv_stmt fsubst vsubst ctx1 ctx2
  SSkip SSkip = True"
| "alpha_equiv_stmt _ _ _ _ _ _ = False"

(* user needs to manually supply a mapping of functions,
 * since they will be automatically alphabetized *)

lift_definition oalist_len :: "('k :: linorder, 'v) oalist \<Rightarrow> nat"
is length.


(* NB: first argument is a copy of the fsubst for recursing over
 * second argument is the full fsubst, which we still need to handle recursion *)
fun alpha_equiv_fctx' ::
  "(name * name) list \<Rightarrow> subst' \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> bool" where
"alpha_equiv_fctx' [] fsubst0 ctx1 ctx2 = True"
| "alpha_equiv_fctx' ((nh1, nh2)#t) fsubst0 ctx1 ctx2 =
   (case get ctx1 nh1 of
    None \<Rightarrow> False
    | Some fh1 \<Rightarrow>
    (case get ctx2 nh2 of
     None \<Rightarrow> False
     | Some fh2 \<Rightarrow>
      (case (fh1, fh2) of
        (Inl (Decl args1 rets1 body1), Inl (Decl args2 rets2 body2)) \<Rightarrow>
          (length args1 = length args2 \<and>
           length rets1 = length rets2 \<and>
           distinct (args1 @ rets1) \<and>
           distinct (args2 @ rets2) \<and>
           alpha_equiv_stmt fsubst0 [to_oalist (zip (args1 @ rets1) (args2 @ rets2))] ctx1 ctx2 body1 body2 \<and>
           alpha_equiv_fctx' t fsubst0 ctx1 ctx2)
        | (Inr bh1, Inr bh2) \<Rightarrow>
          \<comment> \<open>(bh1 = bh2)\<close> alpha_equiv_fctx' t fsubst0 ctx1 ctx2
        | (_, _) \<Rightarrow> False)))"

definition alpha_equiv_fctx ::
  "(name * name) list \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> bool"
  where
"alpha_equiv_fctx ns ctx1 ctx2 = 
  alpha_equiv_fctx' ns (to_oalist ns) ctx1 ctx2"

definition fctx_prims_ok ::
  "(name, name) oalist \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> (name, (fundec + 'g builtin)) oalist \<Rightarrow> bool" where
"fctx_prims_ok subst ctx1 ctx2 =
  (\<forall> n1 n2 p1 p2.
    alpha_equiv_name' subst n1 n2 \<longrightarrow>
    get ctx1 n1 = Some (Inr p1) \<longrightarrow>
    get ctx2 n2 = Some (Inr p2) \<longrightarrow>
    p1 = p2)"

lemma fctx_prims_okI :
  assumes "\<And> n1 n2 p1 p2 .
    alpha_equiv_name' subst n1 n2 \<Longrightarrow>
    get ctx1 n1 = Some (Inr p1) \<Longrightarrow>
    get ctx2 n2 = Some (Inr p2) \<Longrightarrow>
    p1 = p2"
  shows "fctx_prims_ok subst ctx1 ctx2"
  using assms
  by(auto simp add: fctx_prims_ok_def)

lemma fctx_prims_okD :
  assumes "fctx_prims_ok subst ctx1 ctx2"
  assumes "alpha_equiv_name' subst n1 n2"
  assumes "get ctx1 n1 = Some (Inr p1)"
  assumes "get ctx2 n2 = Some (Inr p2)"
  shows "p1 = p2"
  using assms
  by(auto simp add: fctx_prims_ok_def)

fun alpha_equiv_program ::
  "(name * name) list \<Rightarrow> 'g program \<Rightarrow> 'g program \<Rightarrow> bool"
  where
"alpha_equiv_program ns (Prog ctx1 body1) (Prog ctx2 body2) =
  (alpha_equiv_fctx ns ctx1 ctx2 \<and>
   alpha_equiv_stmt (to_oalist ns) [] ctx1 ctx2 body1 body2)"

fun alpha_equiv_varmap'l ::
  "(name * name) list \<Rightarrow> (name * int) list \<Rightarrow> (name * int) list \<Rightarrow> bool" where
"alpha_equiv_varmap'l [] vm1 vm2 = True"
| "alpha_equiv_varmap'l ((nh1, nh2) # nt) vm1 vm2 =
  (case map_of vm1 nh1 of
   None \<Rightarrow> False
   | Some val1 \<Rightarrow>
    (case map_of vm2 nh2 of
     None \<Rightarrow> False
     | Some val2 \<Rightarrow>
      (val1 = val2 \<and> alpha_equiv_varmap'l nt vm1 vm2)))"

lift_definition alpha_equiv_varmap' ::
  "(name, name) oalist \<Rightarrow> (name, int) oalist \<Rightarrow> (name, int) oalist \<Rightarrow> bool"
is alpha_equiv_varmap'l
  .

fun alpha_equiv_varmap ::
  "subst \<Rightarrow> varmap \<Rightarrow> varmap \<Rightarrow> bool" where
"alpha_equiv_varmap [] [] [] = True"
| "alpha_equiv_varmap (sh#st) (v1h#v1t) (v2h#v2t) =
   (alpha_equiv_varmap' sh v1h v2h \<and>
    \<comment> \<open>oalist_len sh = oalist_len v1h \<and> \<close>
    oalist_keys sh = oalist_keys v1h \<and>
    \<comment> \<open> oalist_len sh = oalist_len v2h \<and> \<close>
    oalist_one_one sh \<and>
    oalist_keys (oalist_flip sh) = oalist_keys v2h \<and>
    alpha_equiv_varmap st v1t v2t)"
| "alpha_equiv_varmap _ _ _ = False"


end