theory YulTests
  imports YulSemanticsSingleStep YulSyntax
"HOL-Library.Adhoc_Overloading"
begin

definition simpleBuiltins :: 
  "(int list, int, unit) function_sig locals" where
"simpleBuiltins = make_locals
  [ ( (STR ''add'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns =   [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                            (\<lambda> g vs .
                              (case vs of v1#v2#vt \<Rightarrow>
                                Inl (g, [v1+v2])
                                | _ \<Rightarrow> Inr (STR ''bad args for add''))))
      , f_sig_visible = [] \<rparr>)
  , ( (STR ''sub'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [v1-v2])
                            | _ \<Rightarrow> Inr (STR ''bad args for sub''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''mul'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [v1*v2])
                            | _ \<Rightarrow> Inr (STR ''bad args for mul''))))
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
  ,( (STR ''lt'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [(if v1 < v2 then 1 else 0)])
                            | _ \<Rightarrow> Inr (STR ''bad args for lt''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''gt'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [(if v1 > v2 then 1 else 0)])
                            | _ \<Rightarrow> Inr (STR ''bad args for gt''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''eq'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()
                          , YulTypedName (STR ''y'') ()]
      , f_sig_returns = [ YulTypedName (STR ''z'') ()]
      , f_sig_body = (YulBuiltin
                        (\<lambda> g vs .
                          (case vs of v1#v2#vt \<Rightarrow>
                            Inl (g, [(if v1 = v2 then 1 else 0)])
                            | _ \<Rightarrow> Inr (STR ''bad args for eq''))))
      , f_sig_visible = []\<rparr>)
  , ( (STR ''print'')
    , \<lparr> f_sig_arguments = [ YulTypedName (STR ''x'') ()]
      , f_sig_returns = []
      , f_sig_body = (YulBuiltin 
                        (\<lambda> g vs .
                          (case vs of
                            v1#vt \<Rightarrow> Inl (v1#g, [])
                            | _ \<Rightarrow> Inr (STR ''bad args for print''))))
      , f_sig_visible = []\<rparr>)]"
    

definition simpleDialect ::
  "(int list, int, unit) YulDialect" where
  "simpleDialect =
    \<lparr> is_truthy = (\<lambda> i . i \<noteq> 0)
    , init_state = []
    , default_val = 0
    , builtins = simpleBuiltins \<rparr>"


term "YUL{

}"

definition tt :: unit where "tt = ()"

adhoc_overloading YulTypeUint256 "()"
adhoc_overloading YulDefaultType "tt"
adhoc_overloading "YulLiteralNumber" "uint :: 256 word \<Rightarrow> int YulLiteralValue"

definition eval where "eval \<equiv> \<lambda> x . case (evalYul simpleDialect x 10000) of ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g)"
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
      z := f(sub(x, 1 : uint256))
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
  (YUL{ x := sub(1 : uint256, 2 : uint256)
print(x)
})"


value "evalYul simpleDialect prog3 30"

definition prog4 :: "(int, unit) YulStatement" where
"prog4 \<equiv>
  (YUL{
        base := 2
        exponent := 4
        result := 1
        for { let i := 0 } lt(i, exponent) { i := add(i, 1) }
        {
            result := mul(result, base)
        }
        print(result)
})"

value "eval prog4"

definition prog5 :: 
"(int, unit) YulStatement" where
"prog5 \<equiv>
  (YUL{
      function f() -> a, b {
        a := 1
        b := 2
      }
      x, y := f()
      print(x)
      print(y)
print(sub(x, y))
})"

value "eval prog5"

value "eval prog5"

(* test switch statements *)

(* test function shadowing (should fail) *)


end