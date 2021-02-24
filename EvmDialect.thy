theory EvmDialect imports
  MiniEvm
  YulSemanticsSingleStep
  "HOL-Library.Adhoc_Overloading"

begin

(*
 * Construct builtins list
 *)
definition yulBuiltins :: "(estate, eint, unit) function_sig locals" where
"yulBuiltins = make_locals
  [ (STR ''stop'', mkBuiltin ei_stop)
  , (STR ''add'', mkBuiltin ei_add)
  , (STR ''mul'', mkBuiltin ei_sub)
  , (STR ''div'', mkBuiltin ei_div)
  , (STR ''sdiv'', mkBuiltin ei_sdiv)
  , (STR ''mod'', mkBuiltin ei_mod)
  , (STR ''smod'', mkBuiltin ei_smod)
  , (STR ''addmod'', mkBuiltin ei_addmod)
  , (STR ''mulmod'', mkBuiltin ei_mulmod)
  , (STR ''exp'', mkBuiltin ei_exp)
  , (STR ''signextend'', mkBuiltin ei_signextend)

  , (STR ''lt'', mkBuiltin ei_lt)
  , (STR ''gt'', mkBuiltin ei_gt)
  , (STR ''slt'', mkBuiltin ei_slt)
  , (STR ''sgt'', mkBuiltin ei_sgt)
  , (STR ''eq'', mkBuiltin ei_eq)
  , (STR ''iszero'', mkBuiltin ei_iszero)
  , (STR ''and'', mkBuiltin ei_and)
  , (STR ''or'', mkBuiltin ei_or)
  , (STR ''xor'', mkBuiltin ei_xor)
  , (STR ''not'', mkBuiltin ei_not)
  , (STR ''byte'', mkBuiltin ei_byte)
  , (STR ''shl'', mkBuiltin ei_shl)
  , (STR ''shr'', mkBuiltin ei_shr)
  , (STR ''sar'', mkBuiltin ei_sar)

  , (STR ''keccak256'', mkBuiltin ei_keccak256)

  , (STR ''address'', mkBuiltin ei_address)
  , (STR ''balance'', mkBuiltin ei_balance)
  , (STR ''origin'', mkBuiltin ei_origin)
  , (STR ''caller'', mkBuiltin ei_caller)
  , (STR ''callvalue'', mkBuiltin ei_callvalue)
  , (STR ''calldataload'', mkBuiltin ei_calldataload)
  , (STR ''calldatasize'', mkBuiltin ei_calldatasize)
  , (STR ''calldatacopy'', mkBuiltin ei_calldatacopy)
  , (STR ''codesize'', mkBuiltin ei_codesize)
  , (STR ''codecopy'', mkBuiltin ei_codecopy)
  , (STR ''gasprice'', mkBuiltin ei_gasprice)
  , (STR ''extcodesize'', mkBuiltin ei_extcodesize)
  , (STR ''extcodecopy'', mkBuiltin ei_extcodecopy)
  , (STR ''returndatasize'', mkBuiltin ei_returndatacopy)
  , (STR ''extcodehash'', mkBuiltin ei_extcodehash)

  , (STR ''blockhash'', mkBuiltin ei_blockhash)
  , (STR ''coinbase'', mkBuiltin ei_coinbase)
  , (STR ''timestamp'', mkBuiltin ei_timestamp)
  , (STR ''number'', mkBuiltin ei_number)
  , (STR ''difficulty'', mkBuiltin ei_difficulty)
  , (STR ''gaslimit'', mkBuiltin ei_gaslimit)
  , (STR ''chainid'', mkBuiltin ei_chainid)
  , (STR ''selfbalance'', mkBuiltin ei_selfbalance)

  \<comment> \<open> pop ... jumpdest \<close>
  , (STR ''pop'', mkBuiltin ei_pop)
  , (STR ''mload'', mkBuiltin ei_mload)
  , (STR ''mstore'', mkBuiltin ei_mstore)
  , (STR ''mstore8'', mkBuiltin ei_mstore8)
  , (STR ''sload'', mkBuiltin ei_sload)
  , (STR ''sstore'', mkBuiltin ei_sstore)
  , (STR ''msize'', mkBuiltin ei_msize)
  , (STR ''gas'', mkBuiltin ei_gas)

  \<comment> \<open>, (STR ''jumpdest'', mkBuiltin ei_jumpdest) \<close>

  , (STR ''log0'', mkBuiltin ei_log0)
  , (STR ''log1'', mkBuiltin ei_log1)
  , (STR ''log2'', mkBuiltin ei_log2)
  , (STR ''log3'', mkBuiltin ei_log3)
  , (STR ''log4'', mkBuiltin ei_log4)

  \<comment> \<open> eip615_jumpto... eip615_getlocal \<close>

  \<comment> \<open> create... staticcall (just return for now) \<close>
  , (STR ''create'', mkBuiltin ei_create)
  , (STR ''call'', mkBuiltin ei_call)
  , (STR ''callcode'', mkBuiltin ei_callcode)
  , (STR ''return'', mkBuiltin ei_return)
  , (STR ''delegatecall'', mkBuiltin ei_delegatecall)
  , (STR ''create2'', mkBuiltin ei_create2)
\<comment> \<open>  , (STR ''staticcall'', mkBuiltin ei_staticcall) \<close>

  , (STR ''revert'', mkBuiltin ei_revert)
  , (STR ''invalid'', mkBuiltin ei_invalid)
  , (STR ''selfdestruct'', mkBuiltin ei_selfdestruct)
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