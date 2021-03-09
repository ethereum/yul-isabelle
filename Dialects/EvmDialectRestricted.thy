theory EvmDialectRestricted imports
  "../Evm/MiniEvm"
  "../Yul/YulSemanticsSingleStep"

begin

(*
 * Construct builtins list
 *)
definition yulBuiltins :: "(estate, eint, unit) function_sig locals" where
"yulBuiltins = make_locals
  [ (STR ''stop'', mkBuiltin ei_stop)
  , (STR ''add'', mkBuiltin ei_add)
  , (STR ''mul'', mkBuiltin ei_sub)

  , (STR ''lt'', mkBuiltin ei_lt)
  , (STR ''mstore'', mkBuiltin ei_mstore)
  ]"

(*
definition tt :: unit where "tt = ()"
definition tt' :: unit where "tt' = ()"


adhoc_overloading YulTypeUint256 "tt"
adhoc_overloading YulDefaultType "()"
adhoc_overloading "YulLiteralNumber" "id :: 256 word \<Rightarrow> eint YulLiteralValue"
*)
definition EvmDialect :: "(estate, eint, unit) YulDialect" where
"EvmDialect =
  \<lparr> is_truthy = (\<lambda> x . (x \<noteq> word_of_int 0))
  , init_state = dummy_estate
  , default_val = word_of_int 0
  , builtins = yulBuiltins
  , set_flag = 
      (\<lambda> f st . (st \<lparr> e_flag := f \<rparr>))
  , get_flag = e_flag \<rparr>"

definition eval where "eval \<equiv> \<lambda> x . case (evalYul EvmDialect x 100) of 
ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g)"

end