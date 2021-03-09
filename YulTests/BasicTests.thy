theory BasicTests
  imports "../Yul/YulSemanticsSingleStep" "../Yul/YulSyntax" "../Dialects/BasicDialect"
begin

definition eval where "eval \<equiv> \<lambda> x . case (evalYul basicDialect x 10000) of
  ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g)"

(* TODO: we are reversing fun args order twice. *)
definition prog1 :: "(256 word, unit) YulStatement" where
  "prog1 \<equiv>
  (YUL{
    let x  := 5 : uint256
    print(sub(x, 3:uint256))
  })"

value prog1

value "evalYul basicDialect prog1 90"

definition prog2 :: "(256 word, unit) YulStatement" where
"prog2 \<equiv>
  (YUL{
    function f(x) -> z {
      if x { leave }
      z := f(sub(x, 1 : uint256))
    }
    print(29 : uint256)
    print(f(5 : uint256))
})"

value "evalYul basicDialect prog2 99"


definition bad1 :: "(256 word, unit) YulStatement" where
"bad1 \<equiv>
  (YUL{
    { function f() {} }
    f()
})"

value "evalYul basicDialect bad1 30"

definition prog3 :: "(256 word, unit) YulStatement" where
"prog3 \<equiv>
  (YUL{ x := sub(1 : uint256, 2 : uint256)
print(x)
})"


value "evalYul basicDialect prog3 30"

definition prog4 :: "(256 word, unit) YulStatement" where
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
"(256 word, unit) YulStatement" where
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


(* test switch statements *)

(* test function shadowing (should fail) *)


end