theory YulTests
  imports YulSemanticsSingleStep YulSyntax
"HOL-Library.Adhoc_Overloading"
begin

definition simpleBuiltins :: 
  "(int, int, unit) function_sig locals" where
"simpleBuiltins = make_locals
  [ ( (STR ''plus'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns =   [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                            (\<lambda> g vs .
                              (case vs of v1#v2#vt \<Rightarrow>
                                Inl (g, [v1+v2])
                                | _ \<Rightarrow> Inr (STR ''bad args for plus''))))
      , f_sig_visible = [] \<rparr>)
  , ( (STR ''minus'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [v1-v2])
                            | _ \<Rightarrow> Inr (STR ''bad args for minus''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''times'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [v1*v2])
                            | _ \<Rightarrow> Inr (STR ''bad args for times''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''div'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [divide_int_inst.divide_int v1 v2])
                            | _ \<Rightarrow> Inr (STR ''bad args for div''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''print'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()]
      , f_sig_returns = []
      , f_sig_body = (YulBuiltin 
                        (\<lambda> g vs .
                          (case vs of
                            v1#vt \<Rightarrow> Inl (v1, [])
                            | _ \<Rightarrow> Inr (STR ''bad args for print''))))
      , f_sig_visible = []\<rparr>)]"
    

definition simpleDialect ::
  "(int, int, unit) YulDialect" where
  "simpleDialect =
    \<lparr> is_truthy = (\<lambda> i . i = 0)
    , init_state = 0
    , default_val = 0
    , builtins = simpleBuiltins \<rparr>"


term "YUL{

}"

definition tt :: unit where "tt = ()"

adhoc_overloading YulTypeUint256 "()"
adhoc_overloading YulDefaultType "tt"
adhoc_overloading "YulLiteralNumber" "uint :: 256 word \<Rightarrow> int YulLiteralValue"

(* TODO: we are reversing fun args order twice. *)
definition prog1 :: "(int, unit) YulStatement" where
  "prog1 \<equiv>
  (YUL{
    let x  := 5 : uint256
    print(minus(x, 3:uint256))
  })"

value prog1

value "evalYul simpleDialect prog1 90"

definition prog2 :: "(int, unit) YulStatement" where
"prog2 \<equiv>
  (YUL{
    function f(x) -> z {
      if x { leave }
      z := f(minus(x, 1 : uint256))
    }
    print(29 : uint256)
    print(f(5 : uint256))
})"

value "evalYul simpleDialect prog2 99"


definition bad1 :: "(int, unit) YulStatement" where
"bad1 \<equiv>
  (YUL{
    { function f() {} }
    f()
})"

value "evalYul simpleDialect bad1 30"

definition prog3 :: "(int, unit) YulStatement" where
"prog3 \<equiv>
  (YUL{ x := minus(1 : uint256, 2 : uint256)
print(x)
})"


value "evalYul simpleDialect prog3 30"




end