theory YulInterpreterTests
  imports "../Dialects/EvmDialectRestricted"

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
        mstore(mul(x, 5), mul(x, 0x1))
    }
}"

(*
value "
(case (eval loop_yul) of
  Inl x \<Rightarrow> edata_gets 0 72 (e_memory x))"
*)

definition memtest_yul :: "(eint, unit) YulStatement" where
"memtest_yul \<equiv>
YUL{mstore(40, 22)}"

value "
(case (eval memtest_yul) of
  Inl x \<Rightarrow> edata_gets 0 72 (e_memory x))"

term "0 :: nat"

(*
export_code "loop_yul" eval in Haskell module_name ABICoder file_prefix abicoder
*)
(*
*)

end
