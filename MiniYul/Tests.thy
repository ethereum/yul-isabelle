theory Tests imports Semantics begin

definition test_ctx1 :: "int fctx" where
"test_ctx1 = ctx_make
  []
  [(STR ''write'', (\<lambda> g il _.
    (case il of [] \<Rightarrow> None
     |ih # _ \<Rightarrow> Some (ih, []))))]"

definition test_prog1 :: "int program" where
"test_prog1 =
  Prog test_ctx1
  (SSkip)"

value "eval_program 999 test_prog1 0"

definition test_prog2 :: "int program" where
"test_prog2 =
  Prog test_ctx1
  (SBlock [STR ''a'', STR ''b'', STR ''c''] 
    [ SAssn [STR ''a''] (E1 [ELit 2])
    , SAssn [] (EPrim (STR ''write'') [EVar (STR ''a'')])])"

value "eval_program 999 test_prog2 0"

definition test_prog3 :: "int program" where
"test_prog3 =
  Prog test_ctx1
  (SBlock [STR ''a'', STR ''b'', STR ''c''] 
    [ SAssn [STR ''a''] (E1 [ELit 2])
    , SBlock [STR ''a'']
      [ SAssn [STR ''a''] (E1 [ELit 3])]
    , SAssn [] (EPrim (STR ''write'') [EVar (STR ''a'')])])"

value "eval_program 999 test_prog3 0"


(*
  ,(STR ''zrec'', Decl
    [STR ''x''] [STR ''y'']]
*)
definition test_ctx2 :: "varmap fctx" where
"test_ctx2 = ctx_make
  [(STR ''inc'', Decl
   [STR ''x''] [STR ''y'']
   (SBlock []
    [SAssn [STR ''y''] (EPrim (STR ''add'') [EVar (STR ''x''), ELit 1])]))

  ,(STR ''reczero'', Decl
    [STR ''x''] [STR ''y'']
    (SBlock [STR ''cond'']
      [SAssn [STR ''cond''] (EPrim (STR ''lt'') [ELit 0, EVar (STR ''x'')])
      ,SIf (EVar (STR ''cond''))
       (SBlock []
        [SAssn [STR ''x''] (EPrim (STR ''sub'') [EVar (STR ''x''), ELit 1])
        ,SAssn [STR ''y''] (EFun (STR ''reczero'') [EVar (STR ''x'')])])
       SSkip]))]

  [(STR ''write'', (\<lambda> g il vm.
    (case il of [] \<Rightarrow> Some (vm, [])
     | _ \<Rightarrow> None)))
  ,(STR ''add'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [a1 + a2])
      | _ \<Rightarrow> None)))
  ,(STR ''sub'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [a1 - a2])
      | _ \<Rightarrow> None)))
  ,(STR ''mul'', (\<lambda> g il _.
      (case il of [a1, a2] \<Rightarrow>
        Some (g, [a1 - a2])
        | _ \<Rightarrow> None)))
  ,(STR ''eq'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [(if a1 = a2 then 1 else 0)])
      | _ \<Rightarrow> None)))
  ,(STR ''lt'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [(if a1 < a2 then 1 else 0)])
      | _ \<Rightarrow> None)))]"

definition test_prog4 :: "varmap program" where
"test_prog4 =
  Prog test_ctx2
  (SBlock [STR ''a'']
   [ SAssn [STR ''a''] (E1 [ELit 1])
   , SAssn [STR ''a''] (EFun (STR ''inc'') [EVar (STR ''a'')])
   , SAssn [] (EPrim (STR ''write'') [])])"

value "varmap_gets (varmap_inserts [empty] [(STR ''a'', 1), (STR ''b'', 2)]) [STR ''a'', STR ''b''] "

value "eval_program 999 test_prog4 []"

definition test_prog5 :: "varmap program" where
"test_prog5 =
  Prog test_ctx2
  (SBlock [STR ''a'', STR ''cond'']
   [ SAssn [STR ''a''] (E1 [ELit 2])
   , SAssn [STR ''cond''] (EPrim (STR ''lt'') [EVar (STR ''a''), ELit 3])
   , SIf (EVar (STR ''cond''))
     (SAssn [STR ''a''] (E1 [ELit 10]))
     (SAssn [STR ''a''] (E1 [ELit 15]))
   , SAssn [] (EPrim (STR ''write'') [])])"

value "eval_program 999 test_prog5 []"


definition test_prog6 :: "varmap program" where
"test_prog6 =
  Prog test_ctx2
  (SBlock [STR ''a'', STR ''cond'']
   [ SAssn [STR ''a''] (E1 [ELit 10])
   , SAssn [STR ''cond''] (EPrim (STR ''lt'') [ELit 0, EVar (STR ''a'')])
   , SWhile (EVar (STR ''cond''))
     (SBlock []
      [ SAssn [STR ''a''] (EPrim (STR ''sub'') [EVar (STR ''a''), ELit 1])
      , SAssn [STR ''cond''] (EPrim (STR ''lt'') [ELit 0, EVar (STR ''a'')])])
   , SAssn [] (EPrim (STR ''write'') [])])"

value "eval_program 999 test_prog6 []"

definition test_prog7 :: "varmap program" where
"test_prog7 =
  Prog test_ctx2
  (SBlock [STR ''a'']
   [ SAssn [STR ''a''] (E1 [ELit 10])
   , SAssn [STR ''a''] (EFun (STR ''reczero'') [EVar (STR ''a'')])
   , SAssn [] (EPrim (STR ''write'') [])])"

value "eval_program 999 test_prog7 []"

end