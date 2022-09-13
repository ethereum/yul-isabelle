theory AlphaEquiv_Tests
imports AlphaEquiv
begin

definition test_ctx1 :: "int fctx" where
"test_ctx1 = ctx_make
  []
  [(STR ''write'', (\<lambda> g il _.
    (case il of [] \<Rightarrow> None
     |ih # _ \<Rightarrow> Some (ih, []))))]"

definition test_funmap1 :: "(name * name) list" where
  "test_funmap1 = [(STR ''write'', STR ''write'')]"

definition test_prog1a :: "int program" where
"test_prog1a = 
  Prog test_ctx1
  (SBlock [STR ''a'', STR ''b''] [])"

definition test_prog1b :: "int program" where
"test_prog1b = 
  Prog test_ctx1
  (SBlock [STR ''b'', STR ''''] [])"

value "alpha_equiv_program test_funmap1 test_prog1a test_prog1b"

definition test_prog2a :: "int program" where
"test_prog2a = 
  Prog test_ctx1
  (SBlock [STR ''a'', STR ''b''] [
    SAssn [(STR ''a'')] (E1 [EVar (STR ''b'')])])"

definition test_prog2b :: "int program" where
"test_prog2b = 
  Prog test_ctx1
  (SBlock [STR ''b'', STR ''a''] [
    SAssn [(STR ''b'')] (E1 [EVar (STR ''a'')])])"

value  "alpha_equiv_program test_funmap1 test_prog2a test_prog2b"

definition test_ctx2 :: "int fctx" where
"test_ctx2 = ctx_make
  []
  [(STR ''writee'', (\<lambda> g il _.
    (case il of [] \<Rightarrow> None
     |ih # _ \<Rightarrow> Some (ih, []))))]"

definition test_prog3a :: "int program" where
"test_prog3a = 
  Prog test_ctx1
  (SBlock [STR ''a'', STR ''b''] [
    SAssn [(STR ''a'')] (E1 [EVar (STR ''b'')])
    , SAssn [] (EPrim (STR ''write'') [])])"

definition test_prog3b :: "int program" where
"test_prog3b = 
  Prog test_ctx2
  (SBlock [STR ''a'', STR ''b''] [
    SAssn [(STR ''a'')] (E1 [EVar (STR ''b'')])
    , SAssn [] (EPrim (STR ''write'') [])])"

definition test_funmap2 :: "(name * name) list" where
  "test_funmap2 = [(STR ''write'', STR ''writee'')]"

(* false expected *)
value "alpha_equiv_program test_funmap2 test_prog3a test_prog3b"

definition test_prog3c :: "int program" where
"test_prog3c = 
  Prog test_ctx2
  (SBlock [STR ''a'', STR ''b''] [
    SAssn [(STR ''a'')] (E1 [EVar (STR ''b'')])
    , SAssn [] (EPrim (STR ''writee'') [])])"

value "alpha_equiv_program test_funmap2 test_prog3a test_prog3c"

(* next, actual functions. *)

definition test_ctx3a :: "int fctx" where
"test_ctx3a = ctx_make
  [(STR ''f'', Decl
    [STR ''x'', STR ''y''] [STR ''z'']
    (SBlock []
      [SAssn [STR ''y''] (EPrim (STR ''add'') [EVar (STR ''x''), EVar (STR ''y'')])]))]
  [(STR ''add'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [a1 + a2])
      | _ \<Rightarrow> None)))]"

definition test_ctx3b :: "int fctx" where
"test_ctx3b = ctx_make
  [(STR ''f1'', Decl
    [STR ''a'', STR ''b''] [STR ''c'']
    (SBlock []
      [SAssn [STR ''c''] (EPrim (STR ''add'') [EVar (STR ''a''), EVar (STR ''b'')])]))]
  [(STR ''add'', (\<lambda> g il _.
    (case il of [a1, a2] \<Rightarrow>
      Some (g, [a1 + a2])
      | _ \<Rightarrow> None)))]"

definition test_funmap3 :: "(name * name) list" where
"test_funmap3 = [(STR ''add'', STR ''add''), (STR ''f'', STR ''f1'')]"

definition test_prog4a :: "int program" where
"test_prog4a =
  Prog test_ctx3a
  (SBlock [STR ''a'', STR ''b'']
    [SAssn [(STR ''a'')] (EFun (STR ''f'') [EVar (STR ''a''), (EVar (STR ''a''))])])"

definition test_prog4b :: "int program" where
"test_prog4b =
  Prog test_ctx3b
  (SBlock [STR ''t'', STR ''u'']
    [SAssn [(STR ''t'')] (EFun (STR ''f1'') [EVar (STR ''t''), (EVar (STR ''t''))])])"

value "alpha_equiv_program test_funmap3 test_prog4a test_prog4b"

definition test_prog4c :: "int program" where
"test_prog4c =
  Prog test_ctx3b
  (SBlock [STR ''t'', STR ''u'']
    [SAssn [(STR ''u'')] (EFun (STR ''f1'') [EVar (STR ''t''), (EVar (STR ''t''))])])"

(* false expected *)
value "alpha_equiv_program test_funmap3 test_prog4a test_prog4c"

(*
definition test_prog4a :: "int program" where
"test_prog4a =
*)



end