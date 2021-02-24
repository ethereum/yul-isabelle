theory YulInterpreterTests
  imports "../EvmDialect"

begin

definition eval where "eval \<equiv> \<lambda> x . case (evalYul EvmDialect x 10000) of
  ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g)"


(* exp.yul *)
(*
definition exp_yul :: "(eint, unit) YulStatement" where
"exp_yul \<equiv>
YUL{
  mstore(0, exp(3,not(1)))
}"


value [nbe] "eval exp_yul"
*)

(*
definition not_yul :: "(eint, unit) YulStatement" where
"not_yul \<equiv>
YUL{
  mstore(0,not(1)))
}"
*)

(*
definition loop_yul :: "(eint, unit) YulStatement" where
"loop_yul \<equiv>
YUL{
    for { let x := 2 } lt(x, 10) { x := add(x, 1) } {
        mstore(mul(x, 2), mul(x, 0x2))
    }
}"
*)

definition loop_yul :: "(eint, unit) YulStatement" where
"loop_yul \<equiv>
YUL{
    for { let x := 2 } lt(x, 10) { x := add(x, 1) } {
        mstore(mul(x, 5), mul(x, 0x1000))
    }
}
"


(*
*)

end