theory Semantics imports Syntax
begin

fun eval_expr1 :: "varmap \<Rightarrow> expr1 \<Rightarrow> int option" where
"eval_expr1 _ (ELit x) = Some x"
| "eval_expr1 vm (EVar n) = varmap_get vm n"

fun eval_expr1s :: "varmap \<Rightarrow> expr1 list \<Rightarrow> int list option" where
"eval_expr1s _ [] = Some []"
| "eval_expr1s vm (e1h#e1t) =
   (case eval_expr1 vm e1h of
    None \<Rightarrow> None
    | Some vh \<Rightarrow>
      (case eval_expr1s vm e1t of
       None \<Rightarrow> None
       | Some vt \<Rightarrow> Some (vh#vt)))"


fun eval_statement :: "nat \<Rightarrow> 'g fctx \<Rightarrow> statement \<Rightarrow> varmap \<Rightarrow> 'g \<Rightarrow> 'g state option" 
and eval_statements :: "nat \<Rightarrow> 'g fctx \<Rightarrow> statement list \<Rightarrow> varmap \<Rightarrow> 'g \<Rightarrow> 'g state option" 
and eval_expression :: "nat \<Rightarrow> 'g fctx \<Rightarrow> expr \<Rightarrow> varmap \<Rightarrow> 'g \<Rightarrow> (int list * 'g) orerror option" where
"eval_statement 0 _ _ _ _  = None"

| "eval_statement (Suc n) ctx (SBlock decls stms) vars g =
   (let vars' = varmap_extend (varmap_push vars) decls in
   (case eval_statements n ctx stms vars' g of
    None \<Rightarrow> None
    | Some (Error em) \<Rightarrow> Some (Error em)
    | Some (Ok (vars'', g')) \<Rightarrow> Some (Ok (varmap_pop vars'', g'))))"

| "eval_statement (Suc n) ctx (SAssn ns expr) vars g =
   (case eval_expression n ctx expr vars g of
    None \<Rightarrow> None
    | Some (Error em) \<Rightarrow> Some (Error em)
    | Some (Ok (vals, g')) \<Rightarrow>
      (if length vals = length ns
       then Some (Ok (varmap_updates vars (zip ns vals), g'))
       else Some (Error (STR ''Arity error in assignment''))))"

| "eval_statement (Suc n) ctx (SIf expr1 stm_t stm_f) vars g =
    (case eval_expr1 vars expr1 of
     None \<Rightarrow> Some (Error (STR ''Failed lookup in If condition''))
     | Some r \<Rightarrow>
       (if r = 0
        then eval_statement n ctx stm_f vars g
        else eval_statement n ctx stm_t vars g))"

| "eval_statement (Suc n) ctx (SWhile expr1 stm_body) vars g =
    (case eval_expr1 vars expr1 of
     None \<Rightarrow> Some (Error (STR ''Failed lookup in While condition''))
     | Some r \<Rightarrow>
       (if r = 0
        then Some (Ok (vars, g))
        else (case eval_statement n ctx stm_body vars g of
          None \<Rightarrow> None
          | Some (Error em) \<Rightarrow> Some (Error em)
          | Some (Ok (vars', g')) \<Rightarrow>
            eval_statement n ctx (SWhile expr1 stm_body) vars' g')))"

| "eval_statement (Suc n) ctx Sskip vars g = Some (Ok (vars, g))"


| "eval_statements 0 ctx _ vars g = None"

| "eval_statements (Suc n) ctx [] vars g = Some (Ok (vars, g))"

| "eval_statements (Suc n) ctx (stm_h # stm_t) vars g =
   (case eval_statement n ctx stm_h vars g of
    None \<Rightarrow> None
    | Some (Error em) \<Rightarrow> Some (Error em)
    | Some (Ok (vars', g')) \<Rightarrow> eval_statements n ctx stm_t vars' g')"


| "eval_expression 0 ctx _ vars g = None"

| "eval_expression (Suc n) ctx (E1 e1s) vars g =
   (case eval_expr1s vars e1s of
    None \<Rightarrow> Some (Error (STR ''Failed lookup in expression evaluation''))
    | Some vals \<Rightarrow> Some (Ok (vals, g)))"

| "eval_expression (Suc n) ctx (EPrim p args) vars g =
   (case eval_expr1s vars args of
    None \<Rightarrow> Some (Error (STR ''Failed lookup in expression evaluation''))
    | Some vals \<Rightarrow>
      (case get ctx p of
       None \<Rightarrow> Some (Error (STR ''Undefined primitive''))
       | Some (Inl _) \<Rightarrow> Some (Error (STR ''Called function as primitive''))
       | Some (Inr pb) \<Rightarrow> 
         (case pb g vals vars of
          None \<Rightarrow> Some (Error (STR ''Builtin crashed''))
          | Some (g', vals') \<Rightarrow> Some (Ok (vals', g')))))"

| "eval_expression (Suc n) ctx (EFun f args) vars g =
   (case eval_expr1s vars args of
    None \<Rightarrow> Some (Error (STR ''Failed lookup in expression evaluation''))
    | Some vals \<Rightarrow>
      (case get ctx f of
       None \<Rightarrow> Some (Error (STR ''Undefined function''))
       | Some (Inr _) \<Rightarrow> Some (Error (STR ''Called primitive as function''))
       | Some (Inl (Decl n_args n_rets body)) \<Rightarrow> 
         (if length vals = length n_args
          then
            (let vars_f = varmap_inserts (varmap_extend [empty] n_rets) (zip n_args vals) in
            (case eval_statement n ctx body vars_f g of
             None \<Rightarrow> None
             | Some (Error em) \<Rightarrow> Some (Error em)
             | Some (Ok (vars_f', g')) \<Rightarrow>
               (case varmap_gets vars_f' n_rets of
                None \<Rightarrow> Some (Error (STR ''Should be dead code - function return (1)''))
                | Some rets \<Rightarrow>
                  (if length rets = length n_rets
                   then Some (Ok (rets, g'))
                   else Some (Error (STR ''Should be dead code - function return (2)''))))))
          else Some (Error (STR ''Arity error in function arguments'')))))"
    
fun eval_program :: "nat \<Rightarrow> 'g program \<Rightarrow> 'g \<Rightarrow> 'g state option" where
"eval_program n (Prog ctx body) g = eval_statement n ctx body [empty] g"

fun ctx_make :: "(name * fundec) list \<Rightarrow> (name * 'g builtin) list \<Rightarrow> 'g fctx" where
"ctx_make [] [] = empty"
| "ctx_make ((nh, fh)#ft) b =
   (update nh (Inl fh) (ctx_make ft b))"
| "ctx_make [] ((nh, bh)#bt) =
   (update nh (Inr bh) (ctx_make [] bt))"
   
end