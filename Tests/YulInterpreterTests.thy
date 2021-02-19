theory YulInterpreterTests
  imports "../EvmDialect"

begin



(* exp.yul *)

definition exp_yul :: "(eint, unit) YulStatement" where
"exp_yul \<equiv>
YUL{
  mstore(0, exp(3,not(1)))
}"

(*
value "eval exp_yul"
*)

(*
value "(evalYul EvmDialect exp_yul 10)"
*)
end