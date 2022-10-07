theory Alpha_Equiv_Bigstep
  imports "../Yul/BigStep" "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

type_synonym name = string

type_synonym subst = "(name * name) list"

definition subst_valid :: "subst \<Rightarrow> bool" where
"subst_valid subst =
  (distinct (map fst subst) \<and>
   distinct (map snd subst))"


type_synonym varmap =
  "(name * Value) list"

fun subst_gets :: "subst \<Rightarrow> name list \<Rightarrow> name list option" where
  "subst_gets s [] = Some []"
| "subst_gets s (nh # nt) =
   (case map_of s nh of
    None \<Rightarrow> None
    | Some nh' \<Rightarrow>
      (case subst_gets s nt of
       None \<Rightarrow> None
       | Some nt' \<Rightarrow> Some (nh'#nt')))"

(*
fun subst_update :: "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> subst" where
  "subst_update [] n1 n2 = [(n1, n2)]"
| "subst_update ((n1h, n2h)#t) s i =
   (case get hl s of
    Some _ \<Rightarrow> (update s i hl #t)
    | None \<Rightarrow> hl # subst_update t s i)"

fun subst_updates :: "subst \<Rightarrow> (name * name) list \<Rightarrow> subst" where
"subst_updates vm [] = vm"
| "subst_updates vm ((n, v)#t) =
   subst_updates (subst_update vm n v) t"
*)

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

definition flip :: "('x * 'x) list \<Rightarrow> ('x * 'x) list" where
"flip l =
  map (\<lambda> (x, y) . (y, x)) l"

definition alpha_equiv_name ::
  "subst \<Rightarrow> name \<Rightarrow> name \<Rightarrow> bool" where
"alpha_equiv_name subst n1 n2 = 
   (case (map_of subst n1, map_of (flip subst) n2) of
    (Some n2', Some n1') \<Rightarrow> (n1 = n1' \<and> n2 = n2')
    | _ \<Rightarrow> False)"


(* TODO: do we want to do a single list version and then zip?
 * or a two-list version?
 *)
fun gather_var_declarations ::
  "Statement list \<Rightarrow> name list" where
"gather_var_declarations [] = []"
| "gather_var_declarations ((VariableDeclaration vars _) # sts) =
   vars @ gather_var_declarations sts"
| "gather_var_declarations (_ # sts) =
   gather_var_declarations sts"

(* TODO: do we need to keep track of the information beyond function name here?
 *)
fun gather_fun_declarations ::
  "Statement list \<Rightarrow> name list" where
"gather_fun_declarations [] = []"
| "gather_fun_declarations ((FunctionDefinition name _ _ _)# sts) =
   name # gather_fun_declarations sts"
| "gather_fun_declarations (_ # sts) =
   gather_fun_declarations sts"

definition update_vars_for_block :: "subst \<Rightarrow> Statement list \<Rightarrow> Statement list \<Rightarrow> subst option" where
"update_vars_for_block subst l1 l2 =
  (let decls1 = gather_var_declarations l1 in
  (let decls2 = gather_var_declarations l2 in
    (if length l1 = length l2
     then Some ((zip decls1 decls2) @ subst)
     else None)))"

declare update_vars_for_block_def [simp add]

definition update_funs_for_block :: "subst \<Rightarrow> Statement list \<Rightarrow> Statement list \<Rightarrow> subst option" where
"update_funs_for_block subst l1 l2 =
  (let decls1 = gather_fun_declarations l1 in
  (let decls2 = gather_fun_declarations l2 in
    (if length l1 = length l2
     then Some ((zip decls1 decls2) @ subst)
     else None)))"

definition update_funs_and_vars_for_block ::
  "subst \<Rightarrow> subst \<Rightarrow> Statement list \<Rightarrow> Statement list \<Rightarrow> (subst * subst) option" where
"update_funs_and_vars_for_block fsubst vsubst l1 l2 =
  (case update_vars_for_block vsubst l1 l2 of
   None \<Rightarrow> None
   | Some vsubst' \<Rightarrow>
    (case update_funs_for_block fsubst l1 l2 of
     None \<Rightarrow> None
     | Some fsubst' \<Rightarrow> Some (fsubst', vsubst')))"

declare update_funs_and_vars_for_block_def [simp add]

(* TODO: are we dealing with redeclarations correctly? *)
definition update_vars_for_fun_body ::
  "subst \<Rightarrow> name list \<Rightarrow> name list \<Rightarrow> name list \<Rightarrow> name list \<Rightarrow> subst option" where
"update_vars_for_fun_body subst params1 rets1 params2 rets2 =
  (if length params1 = length params2
   then (if length rets1 = length rets2
         then Some ((zip params1 params2 @ zip rets1 rets2) @ subst)
         else None)
   else None)"

declare update_vars_for_fun_body_def [simp add]

(*
  (FunctionDefinition n1 params1 rets1 body1) s2 =
  (case s2 of
    (FunctionDefinition n2 params2 rets2 body2) \<Rightarrow> 

declare update_funs_for_block_def [simp add]
*)
(* we still need to deal with visibility.
*)

fun alpha_equiv_expr :: "subst \<Rightarrow> subst \<Rightarrow> Expression \<Rightarrow> Expression \<Rightarrow> bool" where
"alpha_equiv_expr fsubst vsubst (Literal v1) (Literal v2) =
  (v1 = v2)"
| "alpha_equiv_expr fsubst vsubst (Identifier n1) (Identifier n2) =
  (alpha_equiv_name vsubst n1 n2)"
| "alpha_equiv_expr fsubst vsubst (FunctionCall f1 args1) (FunctionCall f2 args2) =
  (alpha_equiv_name fsubst f1 f2 \<and>
   list_all2 (alpha_equiv_expr fsubst vsubst) args1 args2)"
| "alpha_equiv_expr _ _ _ _ = False"

fun alpha_equiv_statement :: "subst \<Rightarrow> subst \<Rightarrow> Statement \<Rightarrow> Statement \<Rightarrow> bool" where
"alpha_equiv_statement fsubst vsubst
  (ExpressionStatement e1) s2 =
   (case s2 of
    ExpressionStatement e2 \<Rightarrow> alpha_equiv_expr fsubst vsubst e1 e2
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  (Assignment vars1 eo1) s2 =
  (case s2 of
    (Assignment vars2 eo2) \<Rightarrow>
      (list_all2 (alpha_equiv_name vsubst) vars1 vars2 \<and>
        (case (eo1, eo2) of
          (None, None) \<Rightarrow> True
        | (Some e1, Some e2) \<Rightarrow> alpha_equiv_expr fsubst vsubst e1 e2))
      | _ \<Rightarrow> False)"

(* We have already taken care of the relationship between
 * vars1 and vars2 when processing the block*)
| "alpha_equiv_statement fsubst vsubst
  (VariableDeclaration vars1 eo1) s2 =
  (case s2 of
    (VariableDeclaration vars2 eo2) \<Rightarrow>
      (length vars1 = length vars2 \<and> list_all2 (alpha_equiv_name vsubst) vars1 vars2 \<and>
      (case (eo1, eo2) of
        (None, None) \<Rightarrow> True
      | (Some e1, Some e2) \<Rightarrow> alpha_equiv_expr fsubst vsubst e1 e2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  (If cond1 body1) s2 =
  (case s2 of
    (If cond2 body2) \<Rightarrow>
      (alpha_equiv_expr fsubst vsubst cond1 cond2 \<and>
      (case update_funs_and_vars_for_block fsubst vsubst body1 body2 of
       None \<Rightarrow> False
       | Some (fsubst', vsubst') \<Rightarrow> 
          list_all2 (alpha_equiv_statement fsubst' vsubst') body1 body2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  (Switch cond1 cases1) s2 =
  (case s2 of
    (Switch cond2 cases2) \<Rightarrow>
      (alpha_equiv_expr fsubst vsubst cond1 cond2 \<and>
       list_all2
        (\<lambda> c1 c2 . 
          case (c1, c2) of
            (Case lit1 body1, Case lit2 body2) \<Rightarrow>
              (lit1 = lit2 \<and> 
              (case update_funs_and_vars_for_block fsubst vsubst body1 body2 of
               None \<Rightarrow> False
               | Some (fsubst', vsubst') \<Rightarrow> list_all2 (alpha_equiv_statement fsubst vsubst) body1 body2)))
        cases1 cases2)
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
   (ForLoop pre1 cond1 post1 body1) s2 =
   (case s2 of
     (ForLoop pre2 cond2 post2 body2) \<Rightarrow> 
       (case update_funs_and_vars_for_block fsubst vsubst pre1 pre2 of
        None \<Rightarrow> False
        | Some (fsubst', vsubst') \<Rightarrow>
          (list_all2 (alpha_equiv_statement fsubst' vsubst') pre1 pre2 \<and>
           alpha_equiv_expr fsubst' vsubst' cond1 cond2 \<and>
            (case update_funs_and_vars_for_block fsubst' vsubst' body1 body2 of
             None \<Rightarrow> False
             | Some (fsubst'b, vsubst'b) \<Rightarrow>
               (list_all2 (alpha_equiv_statement fsubst'b vsubst'b) body1 body2 \<and>
                (case update_funs_and_vars_for_block fsubst' vsubst' post1 post2 of
                  None \<Rightarrow> False
                  | Some (fsubst'p, vsubst'p) \<Rightarrow>
                    (list_all2 (alpha_equiv_statement fsubst'p vsubst'p) post1 post2))))))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  (FunctionDefinition n1 params1 rets1 body1) s2 =
  (case s2 of
    (FunctionDefinition n2 params2 rets2 body2) \<Rightarrow> 
      (alpha_equiv_name fsubst n1 n2 \<and>
      (case update_vars_for_fun_body [] params1 rets1 params2 rets2 of
        Some vsubst' \<Rightarrow> 
        (case update_funs_and_vars_for_block fsubst vsubst' body1 body2 of
         None \<Rightarrow> False
         | Some (fsubst', vsubst'') \<Rightarrow> list_all2 (alpha_equiv_statement fsubst' vsubst'') body1 body2)
        | None \<Rightarrow> False))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  (Block body1) s2 =
  (case s2 of
    (Block body2) \<Rightarrow>
      (case update_vars_for_block vsubst body1 body2 of
       None \<Rightarrow> False
       | Some vsubst' \<Rightarrow>
        (case update_funs_for_block fsubst body1 body2 of
          None \<Rightarrow> False
          | Some fsubst' \<Rightarrow> list_all2 (alpha_equiv_statement fsubst' vsubst') body1 body2))
    | _ \<Rightarrow> False)"

| "alpha_equiv_statement fsubst vsubst
  Break s2 = 
  (case s2 of
    Break \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "alpha_equiv_statement fsubst vsubst
  Continue s2 =
  (case s2 of
    Continue \<Rightarrow> True
    | _ \<Rightarrow> False)"
| "alpha_equiv_statement fsubst vsubst
  Leave s2 =
  (case s2 of
    Leave \<Rightarrow> True
    | _ \<Rightarrow> False)"

(*
fun alpha_equiv_program ::
  "(name * name) list \<Rightarrow> 'g program \<Rightarrow> 'g program \<Rightarrow> bool"
  where
"alpha_equiv_program ns (Prog ctx1 body1) (Prog ctx2 body2) =
  (alpha_equiv_fctx ns ctx1 ctx2 \<and>
   alpha_equiv_stmt (to_oalist ns) [] ctx1 ctx2 body1 body2)"
*)



value \<open>alpha_equiv_statement [] []
YUL{
  let x := 2
  let y := 3
}

YUL{
  let y := 2
  let x := 3
}\<close>

(* expect false *)
value \<open>alpha_equiv_statement [] []
YUL{
  let x := 2
  function w(in1, in2) -> r1 {
    r1 := w(in1, in2)
  }
  let y := 3
}

YUL{
  let y := 2
  function k(foo, boo) -> r2{
    r1 := k(boo, boo)
  }
  let x := 3
}\<close>

   
value \<open>alpha_equiv_statement [] []
YUL{
  let x := 2
  function w(in1, in2) -> r1 {
    r1 := w(in1, in2)
  }
  let y := 3
}

YUL{
  let y := 2
  function k(foo, boo) -> r2{
    r2 := k(foo, boo)
  }
  let x := 3
}\<close>


end