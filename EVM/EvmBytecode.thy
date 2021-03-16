theory EvmBytecode imports Main "HOL-Library.Numeral_Type" MiniEvm 
"../Utils/Ranges"
begin

(* define EVM instruction syntax in terms of their representation as instruction-words *)
definition inst_codes :: ranges where
"inst_codes = mk_ranges [(0, 256)]"
declare inst_codes_def [simp]

typedef inst = "set_of_ranges inst_codes"
proof-
  have "(0 :: nat) \<in> {n . n < 256}" by auto
  thus "\<exists> (x :: nat) . x \<in> set_of_ranges inst_codes" 
    unfolding inst_codes_def
    apply(transfer; auto)
    apply(rule_tac x = 0 in exI)
    apply(auto)
    done
qed
setup_lifting type_definition_inst


(* 
 * begin opcodes
*)
(* 
 * STOP
 *)
definition stop_codes  :: "ranges"  where 
"stop_codes = mk_ranges[(0, 1)]" 
declare stop_codes_def [simp add]
typedef stop_inst = "set_of_ranges stop_codes" 
  unfolding stop_codes_def by (transfer; auto)
setup_lifting type_definition_stop_inst

lift_definition STOP_INST :: "stop_inst \<Rightarrow> inst" is id 
  unfolding stop_codes_def inst_codes_def
  by(transfer; auto)

lift_definition STOP_STOP :: stop_inst is "0x00 :: nat" 
    unfolding stop_codes_def inst_codes_def 
    by(transfer; auto)

free_constructors cases_stop_inst for STOP_STOP
  by (transfer; auto)+

definition is_STOP_STOP :: "stop_inst \<Rightarrow> bool" where
"is_STOP_STOP x \<equiv> case x of STOP_STOP \<Rightarrow> True"

(*
 * Arithmetic
 *)
definition arith_codes :: "ranges" where 
"arith_codes = mk_ranges [(0x01, 0x0c)]"

declare arith_codes_def [simp add]
typedef arith_inst = "set_of_ranges arith_codes" 
  unfolding arith_codes_def
  by(transfer; auto)

setup_lifting type_definition_arith_inst

lift_definition ARITH_INST :: "arith_inst \<Rightarrow> inst" is id 
  unfolding arith_codes_def inst_codes_def
  by(transfer; auto)

lift_definition ARITH_ADD        :: "arith_inst" is "0x01 :: nat" 
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_MUL        :: "arith_inst" is "0x02 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_SUB        :: "arith_inst" is "0x03 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_DIV        :: "arith_inst" is "0x04 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_SDIV       :: "arith_inst" is "0x05 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_MOD        :: "arith_inst" is "0x06 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_SMOD       :: "arith_inst" is "0x07 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_ADDMOD     :: "arith_inst" is "0x08 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_MULMOD     :: "arith_inst" is "0x09 :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_EXP        :: "arith_inst" is "0x0a :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)
lift_definition ARITH_SIGNEXTEND :: "arith_inst" is "0x0b :: nat"
  unfolding inst_codes_def arith_codes_def
  by(transfer; auto)

free_constructors cases_arith_inst for
  ARITH_ADD
| ARITH_MUL
| ARITH_SUB
| ARITH_DIV
| ARITH_SDIV
| ARITH_MOD
| ARITH_SMOD
| ARITH_ADDMOD
| ARITH_MULMOD
| ARITH_EXP
| ARITH_SIGNEXTEND
  apply(transfer; simp only:set_of_ranges_alt_spec arith_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)
  by(transfer;
     auto simp add:List.upt_def)+

fun is_arith_ADD :: "arith_inst => bool" where
"is_arith_ADD ARITH_ADD = True"
| "is_arith_ADD _ = False"
fun is_arith_MUL :: "arith_inst => bool" where
"is_arith_MUL ARITH_MUL = True"
| "is_arith_MUL _ = False"
fun is_arith_SUB :: "arith_inst => bool" where
"is_arith_SUB ARITH_SUB = True"
| "is_arith_SUB _ = False"
fun is_arith_DIV :: "arith_inst => bool" where
"is_arith_DIV ARITH_DIV = True"
| "is_arith_DIV _ = False"
fun is_arith_SDIV :: "arith_inst => bool" where
"is_arith_SDIV ARITH_SDIV = True"
| "is_arith_SDIV _ = False"
fun is_arith_MOD :: "arith_inst => bool" where
"is_arith_MOD ARITH_MOD = True"
| "is_arith_MOD _ = False"
fun is_arith_SMOD :: "arith_inst => bool" where
"is_arith_SMOD ARITH_SMOD = True"
| "is_arith_SMOD _ = False"
fun is_arith_ADDMOD :: "arith_inst => bool" where
"is_arith_ADDMOD ARITH_ADDMOD = True"
| "is_arith_ADDMOD _ = False"
fun is_arith_MULMOD :: "arith_inst => bool" where
"is_arith_MULMOD ARITH_MULMOD = True"
| "is_arith_MULMOD _ = False"
fun is_arith_EXP :: "arith_inst => bool" where
"is_arith_EXP ARITH_EXP = True"
| "is_arith_EXP _ = False"
fun is_arith_SIGNEXTEND :: "arith_inst => bool" where
"is_arith_SIGNEXTEND ARITH_SIGNEXTEND = True"
| "is_arith_SIGNEXTEND _ = False"


(* 
 * Bits + Comparisons
 *)
definition bits_compare_codes :: "ranges" where 
  "bits_compare_codes = mk_ranges[(0x10, 0x1e)]"
declare bits_compare_codes_def [simp add]
typedef bits_compare_inst = "set_of_ranges bits_compare_codes" 
  unfolding bits_compare_codes_def
  by(transfer; auto)
setup_lifting type_definition_bits_compare_inst

lift_definition BITS_COMPARE_LT     :: "bits_compare_inst" is "0x10"
  unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_GT     :: "bits_compare_inst" is "0x11"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_SLT    :: "bits_compare_inst" is "0x12"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_SGT    :: "bits_compare_inst" is "0x13"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_EQ     :: "bits_compare_inst" is "0x14"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_ISZERO :: "bits_compare_inst" is "0x15"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_AND    :: "bits_compare_inst" is "0x16" 
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_OR     :: "bits_compare_inst" is "0x17"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_XOR    :: "bits_compare_inst" is "0x18"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_NOT    :: "bits_compare_inst" is "0x19"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_BYTE   :: "bits_compare_inst" is "0x1a"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_SHL    :: "bits_compare_inst" is "0x1b"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_SHR    :: "bits_compare_inst" is "0x1c"
 unfolding bits_compare_codes_def by (transfer; auto)
lift_definition BITS_COMPARE_SAR    :: "bits_compare_inst" is "0x1d"
 unfolding bits_compare_codes_def by (transfer; auto)


lift_definition BITS_COMPARE_INST :: "bits_compare_inst \<Rightarrow> inst" is id
  unfolding bits_compare_codes_def inst_codes_def by(transfer; auto)

free_constructors cases_compare_inst for
  BITS_COMPARE_LT
| BITS_COMPARE_GT
| BITS_COMPARE_SLT
| BITS_COMPARE_SGT
| BITS_COMPARE_EQ
| BITS_COMPARE_ISZERO
| BITS_COMPARE_AND
| BITS_COMPARE_OR
| BITS_COMPARE_XOR
| BITS_COMPARE_NOT
| BITS_COMPARE_BYTE
| BITS_COMPARE_SHL
| BITS_COMPARE_SHR
| BITS_COMPARE_SAR
  apply(transfer; simp only:set_of_ranges_alt_spec bits_compare_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)

  by(transfer;
     auto simp add:List.upt_def)+

fun "is_bits_compare_LT" :: "bits_compare_inst => bool" where
"is_bits_compare_LT BITS_COMPARE_LT = True"
| "is_bits_compare_LT _ = False"
fun "is_bits_compare_GT" :: "bits_compare_inst => bool" where
"is_bits_compare_GT BITS_COMPARE_GT = True"
| "is_bits_compare_GT _ = False"
fun "is_bits_compare_SLT" :: "bits_compare_inst => bool" where
"is_bits_compare_SLT BITS_COMPARE_SLT = True"
| "is_bits_compare_SLT _ = False"
fun "is_bits_compare_SGT" :: "bits_compare_inst => bool" where
"is_bits_compare_SGT BITS_COMPARE_SGT = True"
| "is_bits_compare_SGT _ = False"
fun "is_bits_compare_EQ" :: "bits_compare_inst => bool" where
"is_bits_compare_EQ BITS_COMPARE_EQ = True"
| "is_bits_compare_EQ _ = False"
fun "is_bits_compare_ISZERO" :: "bits_compare_inst => bool" where
"is_bits_compare_ISZERO BITS_COMPARE_ISZERO = True"
| "is_bits_compare_ISZERO _ = False"
fun "is_bits_compare_AND" :: "bits_compare_inst => bool" where
"is_bits_compare_AND BITS_COMPARE_AND = True"
| "is_bits_compare_AND _ = False"
fun "is_bits_compare_OR" :: "bits_compare_inst => bool" where
"is_bits_compare_OR BITS_COMPARE_OR = True"
| "is_bits_compare_OR _ = False"
fun "is_bits_compare_XOR" :: "bits_compare_inst => bool" where
"is_bits_compare_XOR BITS_COMPARE_XOR = True"
| "is_bits_compare_XOR _ = False"
fun "is_bits_compare_NOT" :: "bits_compare_inst => bool" where
"is_bits_compare_NOT BITS_COMPARE_NOT = True"
| "is_bits_compare_NOT _ = False"
fun "is_bits_compare_BYTE" :: "bits_compare_inst => bool" where
"is_bits_compare_BYTE BITS_COMPARE_BYTE = True"
| "is_bits_compare_BYTE _ = False"
fun "is_bits_compare_SHL" :: "bits_compare_inst => bool" where
"is_bits_compare_SHL BITS_COMPARE_SHL = True"
| "is_bits_compare_SHL _ = False"
fun "is_bits_compare_SHR" :: "bits_compare_inst => bool" where
"is_bits_compare_SHR BITS_COMPARE_SHR = True"
| "is_bits_compare_SHR _ = False"
fun "is_bits_compare_SAR" :: "bits_compare_inst => bool" where
"is_bits_compare_SAR BITS_COMPARE_SAR = True"
| "is_bits_compare_SAR _ = False"


(* keccak256 *)
definition keccak256_codes  :: "ranges"  where 
"keccak256_codes = mk_ranges[(0x20, 0x21)]" 
declare keccak256_codes_def [simp add]
typedef keccak256_inst = "set_of_ranges keccak256_codes" 
  unfolding keccak256_codes_def
  by (transfer; auto)
setup_lifting type_definition_keccak256_inst

lift_definition KECCAK256_KECCAK256 :: keccak256_inst is "0x20 :: nat" 
  unfolding keccak256_codes_def
  by(transfer; auto)

lift_definition KECCAK256_INST :: "keccak256_inst \<Rightarrow> inst" is id 
  unfolding keccak256_codes_def inst_codes_def
  by (transfer; auto)

free_constructors cases_keccak256_inst for KECCAK256_KECCAK256
  by (transfer; auto)+

fun "is_keccak256_KECCAK256" :: "keccak256_inst => bool" where
"is_keccak256_KECCAK256 KECCAK256_KECCAK256 = True"


(* 
 * transaction-specific data instructions
 *)
definition tx_data_codes :: "ranges"
  where 
  "tx_data_codes = mk_ranges[(0x30, 0x40)]"
declare tx_data_codes_def[simp add]
typedef tx_data_inst = "set_of_ranges tx_data_codes" 
  unfolding tx_data_codes_def
  by(transfer; auto)
setup_lifting type_definition_tx_data_inst

lift_definition TX_DATA_ADDRESS        :: "tx_data_inst" is "0x30"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_BALANCE        :: "tx_data_inst" is "0x31"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_ORIGIN         :: "tx_data_inst" is "0x32"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CALLER         :: "tx_data_inst" is "0x33"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CALLVALUE      :: "tx_data_inst" is "0x34"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CALLDATALOAD   :: "tx_data_inst" is "0x35"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CALLDATASIZE   :: "tx_data_inst" is "0x36"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CALLDATACOPY   :: "tx_data_inst" is "0x37"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CODESIZE       :: "tx_data_inst" is "0x38"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_CODECOPY       :: "tx_data_inst" is "0x39"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_GASPRICE       :: "tx_data_inst" is "0x3a"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_EXTCODESIZE    :: "tx_data_inst" is "0x3b"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_EXTCODECOPY    :: "tx_data_inst" is "0x3c"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_RETURNDATASIZE :: "tx_data_inst" is "0x3d"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_RETURNDATACOPY :: "tx_data_inst" is "0x3e"
  unfolding tx_data_codes_def
  by(transfer; auto)
lift_definition TX_DATA_EXTCODEHASH    :: "tx_data_inst" is "0x3f"
  unfolding tx_data_codes_def
  by(transfer; auto)

lift_definition TX_DATA_INST :: "tx_data_inst \<Rightarrow> inst" is id
  unfolding tx_data_codes_def inst_codes_def by(transfer; auto)

free_constructors cases_tx_data_inst for
TX_DATA_ADDRESS
| TX_DATA_BALANCE
| TX_DATA_ORIGIN
| TX_DATA_CALLER
| TX_DATA_CALLVALUE
| TX_DATA_CALLDATALOAD
| TX_DATA_CALLDATASIZE
| TX_DATA_CALLDATACOPY
| TX_DATA_CODESIZE
| TX_DATA_CODECOPY
| TX_DATA_GASPRICE
| TX_DATA_EXTCODESIZE
| TX_DATA_EXTCODECOPY
| TX_DATA_RETURNDATASIZE
| TX_DATA_RETURNDATACOPY
| TX_DATA_EXTCODEHASH
  apply(transfer; simp only:set_of_ranges_alt_spec tx_data_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)
  by(transfer;
     auto simp add:List.upt_def)+

fun "is_tx_data_ADDRESS" :: "tx_data_inst => bool" where
"is_tx_data_ADDRESS TX_DATA_ADDRESS = True"
| "is_tx_data_ADDRESS _ = False"
fun "is_tx_data_BALANCE" :: "tx_data_inst => bool" where
"is_tx_data_BALANCE TX_DATA_BALANCE = True"
| "is_tx_data_BALANCE _ = False"
fun "is_tx_data_ORIGIN" :: "tx_data_inst => bool" where
"is_tx_data_ORIGIN TX_DATA_ORIGIN = True"
| "is_tx_data_ORIGIN _ = False"
fun "is_tx_data_CALLER" :: "tx_data_inst => bool" where
"is_tx_data_CALLER TX_DATA_CALLER = True"
| "is_tx_data_CALLER _ = False"
fun "is_tx_data_CALLVALUE" :: "tx_data_inst => bool" where
"is_tx_data_CALLVALUE TX_DATA_CALLVALUE = True"
| "is_tx_data_CALLVALUE _ = False"
fun "is_tx_data_CALLDATALOAD" :: "tx_data_inst => bool" where
"is_tx_data_CALLDATALOAD TX_DATA_CALLDATALOAD = True"
| "is_tx_data_CALLDATALOAD _ = False"
fun "is_tx_data_CALLDATASIZE" :: "tx_data_inst => bool" where
"is_tx_data_CALLDATASIZE TX_DATA_CALLDATASIZE = True"
| "is_tx_data_CALLDATASIZE _ = False"
fun "is_tx_data_CALLDATACOPY" :: "tx_data_inst => bool" where
"is_tx_data_CALLDATACOPY TX_DATA_CALLDATACOPY = True"
| "is_tx_data_CALLDATACOPY _ = False"
fun "is_tx_data_CODESIZE" :: "tx_data_inst => bool" where
"is_tx_data_CODESIZE TX_DATA_CODESIZE = True"
| "is_tx_data_CODESIZE _ = False"
fun "is_tx_data_CODECOPY" :: "tx_data_inst => bool" where
"is_tx_data_CODECOPY TX_DATA_CODECOPY = True"
| "is_tx_data_CODECOPY _ = False"
fun "is_tx_data_GASPRICE" :: "tx_data_inst => bool" where
"is_tx_data_GASPRICE TX_DATA_GASPRICE = True"
| "is_tx_data_GASPRICE _ = False"
fun "is_tx_data_EXTCODESIZE" :: "tx_data_inst => bool" where
"is_tx_data_EXTCODESIZE TX_DATA_EXTCODESIZE = True"
| "is_tx_data_EXTCODESIZE _ = False"
fun "is_tx_data_EXTCODECOPY" :: "tx_data_inst => bool" where
"is_tx_data_EXTCODECOPY TX_DATA_EXTCODECOPY = True"
| "is_tx_data_EXTCODECOPY _ = False"
fun "is_tx_data_RETURNDATASIZE" :: "tx_data_inst => bool" where
"is_tx_data_RETURNDATASIZE TX_DATA_RETURNDATASIZE = True"
| "is_tx_data_RETURNDATASIZE _ = False"
fun "is_tx_data_RETURNDATACOPY" :: "tx_data_inst => bool" where
"is_tx_data_RETURNDATACOPY TX_DATA_RETURNDATACOPY = True"
| "is_tx_data_RETURNDATACOPY _ = False"
fun "is_tx_data_EXTCODEHASH" :: "tx_data_inst => bool" where
"is_tx_data_EXTCODEHASH TX_DATA_EXTCODEHASH = True"
| "is_tx_data_EXTCODEHASH _ = False"


(* 
 * chain-specific data instructions
 *)
definition chain_data_codes :: "ranges"
  where
  "chain_data_codes = mk_ranges[(0x40, 0x48)]"
declare chain_data_codes_def[simp add]
typedef chain_data_inst = "set_of_ranges chain_data_codes"
  unfolding chain_data_codes_def
  by (transfer; auto)
setup_lifting type_definition_chain_data_inst

lift_definition CHAIN_DATA_BLOCKHASH   :: "chain_data_inst" is "0x40"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_COINBASE    :: "chain_data_inst" is "0x41"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_TIMESTAMP   :: "chain_data_inst" is "0x42"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_NUMBER      :: "chain_data_inst" is "0x43"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_DIFFICULTY  :: "chain_data_inst" is "0x44"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_GASLIMIT    :: "chain_data_inst" is "0x45"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_CHAINID     :: "chain_data_inst" is "0x46"
  unfolding chain_data_codes_def
  by (transfer; auto)
lift_definition CHAIN_DATA_SELFBALANCE :: "chain_data_inst" is "0x47"
  unfolding chain_data_codes_def
  by (transfer; auto)

lift_definition CHAIN_DATA_INST :: "chain_data_inst \<Rightarrow> inst" is id 
  unfolding chain_data_codes_def inst_codes_def
  by (transfer; auto)

free_constructors cases_chain_data_inst for
CHAIN_DATA_BLOCKHASH
| CHAIN_DATA_COINBASE
| CHAIN_DATA_TIMESTAMP
| CHAIN_DATA_NUMBER
| CHAIN_DATA_DIFFICULTY
| CHAIN_DATA_GASLIMIT
| CHAIN_DATA_CHAINID
| CHAIN_DATA_SELFBALANCE
  apply(transfer; simp only:set_of_ranges_alt_spec chain_data_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)
  by(transfer;
     auto simp add:List.upt_def)+


fun "is_chain_data_BLOCKHASH" :: "chain_data_inst => bool" where
"is_chain_data_BLOCKHASH CHAIN_DATA_BLOCKHASH = True"
| "is_chain_data_BLOCKHASH _ = False"
fun "is_chain_data_COINBASE" :: "chain_data_inst => bool" where
"is_chain_data_COINBASE CHAIN_DATA_COINBASE = True"
| "is_chain_data_COINBASE _ = False"
fun "is_chain_data_TIMESTAMP" :: "chain_data_inst => bool" where
"is_chain_data_TIMESTAMP CHAIN_DATA_TIMESTAMP = True"
| "is_chain_data_TIMESTAMP _ = False"
fun "is_chain_data_NUMBER" :: "chain_data_inst => bool" where
"is_chain_data_NUMBER CHAIN_DATA_NUMBER = True"
| "is_chain_data_NUMBER _ = False"
fun "is_chain_data_DIFFICULTY" :: "chain_data_inst => bool" where
"is_chain_data_DIFFICULTY CHAIN_DATA_DIFFICULTY = True"
| "is_chain_data_DIFFICULTY _ = False"
fun "is_chain_data_CHAINID" :: "chain_data_inst => bool" where
"is_chain_data_CHAINID CHAIN_DATA_CHAINID = True"
| "is_chain_data_CHAINID _ = False"
fun "is_chain_data_GASLIMIT" :: "chain_data_inst => bool" where
"is_chain_data_GASLIMIT CHAIN_DATA_GASLIMIT = True"
| "is_chain_data_GASLIMIT _ = False"
fun "is_chain_data_SELFBALANCE" :: "chain_data_inst => bool" where
"is_chain_data_SELFBALANCE CHAIN_DATA_SELFBALANCE = True"
| "is_chain_data_SELFBALANCE _ = False"


(* 
 * state and control instructions
 *)
(* we could break this down; e.g. into
- put
- memory ops
- storage ops
- resource queries
- control flow *)
definition state_control_codes :: "ranges" where
"state_control_codes = mk_ranges[(0x50, 0x5c)]"
declare state_control_codes_def[simp add]
typedef state_control_inst = "set_of_ranges state_control_codes" 
  unfolding state_control_codes_def
  by(transfer; auto)
setup_lifting type_definition_state_control_inst

lift_definition STATE_CONTROL_POP      :: "state_control_inst" is "0x50"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_MLOAD    :: "state_control_inst" is "0x51"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_MSTORE   :: "state_control_inst" is "0x52"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_MSTORE8  :: "state_control_inst" is "0x53"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_SLOAD    :: "state_control_inst" is "0x54"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_SSTORE   :: "state_control_inst" is "0x55"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_JUMP     :: "state_control_inst" is "0x56"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_JUMPI    :: "state_control_inst" is "0x57"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_PC       :: "state_control_inst" is "0x58"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_MSIZE    :: "state_control_inst" is "0x59"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_GAS      :: "state_control_inst" is "0x5a"
unfolding state_control_codes_def
  by(transfer; auto)
lift_definition STATE_CONTROL_JUMPDEST :: "state_control_inst" is "0x5b"
unfolding state_control_codes_def
  by(transfer; auto)

lift_definition STATE_CONTROL_INST :: "state_control_inst => inst" is id
  unfolding state_control_codes_def inst_codes_def
  by(transfer; auto)

free_constructors cases_state_control_inst for
STATE_CONTROL_POP
| STATE_CONTROL_MLOAD
| STATE_CONTROL_MSTORE
| STATE_CONTROL_MSTORE8
| STATE_CONTROL_SLOAD
| STATE_CONTROL_SSTORE
| STATE_CONTROL_JUMP
| STATE_CONTROL_JUMPI
| STATE_CONTROL_PC
| STATE_CONTROL_MSIZE
| STATE_CONTROL_GAS
| STATE_CONTROL_JUMPDEST
  apply(transfer; simp only:set_of_ranges_alt_spec state_control_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)

  by(transfer;
     auto simp add:List.upt_def)+


fun "is_state_control_POP" :: "state_control_inst => bool" where
"is_state_control_POP STATE_CONTROL_POP = True"
| "is_state_control_POP _ = False"
fun "is_state_control_MLOAD" :: "state_control_inst => bool" where
"is_state_control_MLOAD STATE_CONTROL_MLOAD = True"
| "is_state_control_MLOAD _ = False"
fun "is_state_control_MSTORE" :: "state_control_inst => bool" where
"is_state_control_MSTORE STATE_CONTROL_MSTORE = True"
| "is_state_control_MSTORE _ = False"
fun "is_state_control_MSTORE8" :: "state_control_inst => bool" where
"is_state_control_MSTORE8 STATE_CONTROL_MSTORE8 = True"
| "is_state_control_MSTORE8 _ = False"
fun "is_state_control_SLOAD" :: "state_control_inst => bool" where
"is_state_control_SLOAD STATE_CONTROL_SLOAD = True"
| "is_state_control_SLOAD _ = False"
fun "is_state_control_SSTORE" :: "state_control_inst => bool" where
"is_state_control_SSTORE STATE_CONTROL_SSTORE = True"
| "is_state_control_SSTORE _ = False"
fun "is_state_control_JUMP" :: "state_control_inst => bool" where
"is_state_control_JUMP STATE_CONTROL_JUMP = True"
| "is_state_control_JUMP _ = False"
fun "is_state_control_JUMPI" :: "state_control_inst => bool" where
"is_state_control_JUMPI STATE_CONTROL_JUMPI = True"
| "is_state_control_JUMPI _ = False"
fun "is_state_control_PC" :: "state_control_inst => bool" where
"is_state_control_PC STATE_CONTROL_PC = True"
| "is_state_control_PC _ = False"
fun "is_state_control_MSIZE" :: "state_control_inst => bool" where
"is_state_control_MSIZE STATE_CONTROL_MSIZE = True"
| "is_state_control_MSIZE _ = False"
fun "is_state_control_GAS" :: "state_control_inst => bool" where
"is_state_control_GAS STATE_CONTROL_GAS = True"
| "is_state_control_GAS _ = False"
fun "is_state_control_JUMPDEST" :: "state_control_inst => bool" where
"is_state_control_JUMPDEST STATE_CONTROL_JUMPDEST = True"
| "is_state_control_JUMPDEST _ = False"


(* 
 * push instructions
 *)
definition push_codes :: "ranges" where
"push_codes = mk_ranges[(0x60, 0x80)]"
declare push_codes_def[simp add]
typedef push_inst = "set_of_ranges push_codes" 
  unfolding push_codes_def
  by (transfer; auto)
setup_lifting type_definition_push_inst

lift_definition PUSH_INST :: "push_inst \<Rightarrow> inst" is id
  unfolding push_codes_def inst_codes_def
  by(transfer; auto)

typedef nat32 = "{x :: nat . x < 32}"
proof
  have "0 < (32 :: nat)" by auto
  thus "0 \<in> {x :: nat . x < 32}" by(auto)
qed
setup_lifting type_definition_nat32

lift_definition nat_of_nat32 :: "nat32 \<Rightarrow> nat" is id done

lift_definition nat32_of_nat :: "nat \<Rightarrow> nat32" is "(\<lambda> n . n mod 32)"
  using pos_mod_bound[of 32 n] by auto

(* helper for building push instructions *)
fun make_push :: "nat \<Rightarrow> nat" where
"make_push n =
  0x60 + (n mod 32)"

lift_definition MAKE_PUSH :: "nat \<Rightarrow> push_inst" is make_push
proof-
  fix n :: nat

  have "n mod 32 < 32" using pos_mod_bound[of 32 n] by auto

  hence Upt32: "n mod 32 \<in> set (List.upt 0 32)" by auto

  hence "(0x60 + (n mod 32)) \<in> ((\<lambda> x . x + 0x60) ` set (List.upt 0 32))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x60)"] by auto

  hence Mapped : "(0x60 + (n mod 32)) \<in> set (map (\<lambda> x . x + 0x60) (List.upt 0 32))"
    by auto

  then show "make_push n \<in> set_of_ranges push_codes"
    by(transfer; auto)+
qed

lift_definition PUSH_PUSH :: "nat32 \<Rightarrow> push_inst" is make_push
proof-
  fix n :: nat
  assume "n < 32"

  have "n mod 32 < 32" using pos_mod_bound[of 32 n] by auto

  hence Upt32: "n mod 32 \<in> set (List.upt 0 32)" by auto

  hence "(0x60 + (n mod 32)) \<in> ((\<lambda> x . x + 0x60) ` set (List.upt 0 32))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x60)"] by auto

  hence Mapped : "(0x60 + (n mod 32)) \<in> set (map (\<lambda> x . x + 0x60) (List.upt 0 32))"
    by auto

  then show "make_push n \<in> set_of_ranges push_codes"
    by(transfer; auto)+
qed


free_constructors cases_push_inst for PUSH_PUSH
  apply(transfer; simp only:set_of_ranges_alt_spec push_codes_def; transfer)
  by(transfer;
     auto simp add:List.upt_def)+


fun is_PUSH_PUSH :: "push_inst \<Rightarrow> bool" where
"is_PUSH_PUSH (PUSH_PUSH _) = True"

fun get_PUSH_PUSH :: "push_inst \<Rightarrow> nat" where
"get_PUSH_PUSH (PUSH_PUSH x) = nat_of_nat32 x"

fun is_PUSH_PUSH_n :: "push_inst \<Rightarrow> nat \<Rightarrow> bool" where
"is_PUSH_PUSH_n i x = (get_PUSH_PUSH i = x)"

(* 
 * dup instructions 
 *)
definition dup_codes :: "ranges" where
"dup_codes = mk_ranges[(0x80, 0x90)]"
declare dup_codes_def[simp add]
typedef dup_inst = "set_of_ranges dup_codes" 
  unfolding dup_codes_def
  by(transfer; auto)
setup_lifting type_definition_dup_inst

typedef nat16 = "{x :: nat . x < 16}"
proof
  have "0 < (16 :: nat)" by auto
  thus "0 \<in> {x :: nat . x < 16}" by(auto)
qed
setup_lifting type_definition_nat16

lift_definition DUP_INST :: "dup_inst => inst" is id
  unfolding dup_codes_def inst_codes_def
  by(transfer; auto)

lift_definition nat_of_nat16 :: "nat16 \<Rightarrow> nat" is id done

lift_definition nat16_of_nat :: "nat \<Rightarrow> nat16" is "(\<lambda> n . n mod 16)"
  using pos_mod_bound[of 16 ] by auto

(* helper for building dup instructions *)
fun make_dup :: "nat \<Rightarrow> nat" where
"make_dup n =
  0x80 + (n mod 16)"

lift_definition MAKE_DUP :: "nat \<Rightarrow> dup_inst" is make_dup
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x80 + (n mod 16)) \<in> ((\<lambda> x . x + 0x80) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x80)"] by auto

  hence Mapped : "(0x80 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x80) (List.upt 0 16))"
    by auto

  then show "make_dup n \<in> set_of_ranges dup_codes"
    by (transfer; auto)+
qed

lift_definition DUP_DUP :: "nat16 \<Rightarrow> dup_inst" is make_dup
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x80 + (n mod 16)) \<in> ((\<lambda> x . x + 0x80) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x80)"] by auto

  hence Mapped : "(0x80 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x80) (List.upt 0 16))"
    by auto

  then show "make_dup n \<in> set_of_ranges dup_codes"
    by(transfer; auto)+
qed

free_constructors cases_dup_inst for DUP_DUP
  apply(transfer; simp only:set_of_ranges_alt_spec dup_codes_def; transfer)
  by(transfer;
     auto simp add:List.upt_def)+

fun is_DUP_DUP :: "dup_inst \<Rightarrow> bool" where
"is_DUP_DUP (DUP_DUP _) = True"

fun get_DUP_DUP :: "dup_inst \<Rightarrow> nat" where
"get_DUP_DUP (DUP_DUP x) = nat_of_nat16 x"

fun is_DUP_DUP_n :: "dup_inst \<Rightarrow> nat \<Rightarrow> bool" where
"is_DUP_DUP_n i x = (get_DUP_DUP i = x)"

(* 
 * swap instructions 
 *)
definition swap_codes :: "ranges" where
"swap_codes = mk_ranges[(0x90, 0xa0)]"
declare swap_codes_def[simp add]
typedef swap_inst = "set_of_ranges swap_codes"
  unfolding swap_codes_def
  by(transfer; auto)
setup_lifting type_definition_swap_inst

lift_definition SWAP_INST :: "swap_inst => inst" is id
  unfolding swap_codes_def inst_codes_def
  by (transfer; auto)

(* helper for building swap instructions *)
fun make_swap :: "nat \<Rightarrow> nat" where
"make_swap n =
  0x90 + (n mod 16)"

lift_definition MAKE_SWAP :: "nat \<Rightarrow> swap_inst" is make_swap
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x90 + (n mod 16)) \<in> ((\<lambda> x . x + 0x90) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x90)"] by auto

  hence Mapped : "(0x90 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x90) (List.upt 0 16))"
    by auto

  then show "make_swap n \<in> set_of_ranges swap_codes"
    by(transfer; auto)+
qed

lift_definition SWAP_SWAP :: "nat16 \<Rightarrow> swap_inst" is make_swap
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x90 + (n mod 16)) \<in> ((\<lambda> x . x + 0x90) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x90)"] by auto

  hence Mapped : "(0x90 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x90) (List.upt 0 16))"
    by auto

  then show "make_swap n \<in> set_of_ranges swap_codes"
    by(transfer; auto)+
qed

free_constructors cases_swap_inst for SWAP_SWAP
  apply(transfer; simp only:set_of_ranges_alt_spec swap_codes_def; transfer)
  by(transfer;
     auto simp add:List.upt_def)+

fun is_SWAP_SWAP :: "swap_inst \<Rightarrow> bool" where
"is_SWAP_SWAP (SWAP_SWAP _) = True"

fun get_SWAP_SWAP :: "swap_inst \<Rightarrow> nat" where
"get_SWAP_SWAP (SWAP_SWAP x) = nat_of_nat16 x"

fun is_SWAP_SWAP_n :: "swap_inst \<Rightarrow> nat \<Rightarrow> bool" where
"is_SWAP_SWAP_n i x = (get_SWAP_SWAP i = x)"

(* 
 * log instructions 
 *)
definition log_codes where
"log_codes = mk_ranges[(0xa0, 0xa5)]"
declare log_codes_def[simp]
typedef log_inst = "set_of_ranges log_codes"
  unfolding log_codes_def
  by(transfer; auto)

setup_lifting type_definition_log_inst

lift_definition LOG_INST :: "log_inst => inst" is id 
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)

lift_definition LOG_LOG0 :: "log_inst" is "0xa0" 
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)
lift_definition LOG_LOG1 :: "log_inst" is "0xa1"
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)
lift_definition LOG_LOG2 :: "log_inst" is "0xa2"
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)
lift_definition LOG_LOG3 :: "log_inst" is "0xa3"
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)
lift_definition LOG_LOG4 :: "log_inst" is "0xa4"
  unfolding inst_codes_def log_codes_def
  by(transfer; auto)

free_constructors cases_log_inst for
LOG_LOG0
| LOG_LOG1
| LOG_LOG2
| LOG_LOG3
| LOG_LOG4
  apply(transfer; simp only:set_of_ranges_alt_spec log_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)
  by(transfer;
     auto simp add:List.upt_def)+

fun "is_log_LOG0" :: "log_inst => bool" where
"is_log_LOG0 LOG_LOG0 = True"
| "is_log_LOG0 _ = False"
fun "is_log_LOG1" :: "log_inst => bool" where
"is_log_LOG1 LOG_LOG1 = True"
| "is_log_LOG1 _ = False"
fun "is_log_LOG2" :: "log_inst => bool" where
"is_log_LOG2 LOG_LOG2 = True"
| "is_log_LOG2 _ = False"
fun "is_log_LOG3" :: "log_inst => bool" where
"is_log_LOG3 LOG_LOG3 = True"
| "is_log_LOG3 _ = False"
fun "is_log_LOG4" :: "log_inst => bool" where
"is_log_LOG4 LOG_LOG4 = True"
| "is_log_LOG4 _ = False"

(* 
 * EIP615 instructions 
 *)
definition eip615_codes where
"eip615_codes = mk_ranges[(0xb0, 0xba)]"
declare eip615_codes_def[simp]
typedef eip615_inst = "set_of_ranges eip615_codes" 
  unfolding eip615_codes_def
  by(transfer; auto)
setup_lifting type_definition_eip615_inst

lift_definition EIP615_JUMPTO    :: "eip615_inst" is "0xb0"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_JUMPIF    :: "eip615_inst" is "0xb1"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_JUMPV     :: "eip615_inst" is "0xb2"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_JUMPSUB   :: "eip615_inst" is "0xb3"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_JUMPSUBV  :: "eip615_inst" is "0xb4"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_BEGINSUB  :: "eip615_inst" is "0xb5"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_BEGINDATA :: "eip615_inst" is "0xb6"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_RETURNSUB :: "eip615_inst" is "0xb7"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_PUTLOCAL  :: "eip615_inst" is "0xb8"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)
lift_definition EIP615_GETLOCAL  :: "eip615_inst" is "0xb9"
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)

lift_definition EIP615_INST :: "eip615_inst => inst" is id
  unfolding eip615_codes_def inst_codes_def
  by(transfer; auto)

free_constructors cases_eip615_inst for
EIP615_JUMPTO
| EIP615_JUMPIF
| EIP615_JUMPV
| EIP615_JUMPSUB
| EIP615_JUMPSUBV
| EIP615_BEGINSUB
| EIP615_BEGINDATA
| EIP615_RETURNSUB
| EIP615_PUTLOCAL
| EIP615_GETLOCAL
  apply(transfer; simp only:set_of_ranges_alt_spec eip615_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)

  by(transfer;
     auto simp add:List.upt_def)+

fun "is_eip615_JUMPTO" :: "eip615_inst => bool" where
"is_eip615_JUMPTO EIP615_JUMPTO = True"
| "is_eip615_JUMPTO _ = False"
fun "is_eip615_JUMPIF" :: "eip615_inst => bool" where
"is_eip615_JUMPIF EIP615_JUMPIF = True"
| "is_eip615_JUMPIF _ = False"
fun "is_eip615_JUMPV" :: "eip615_inst => bool" where
"is_eip615_JUMPV EIP615_JUMPV = True"
| "is_eip615_JUMPV _ = False"
fun "is_eip615_JUMPSUB" :: "eip615_inst => bool" where
"is_eip615_JUMPSUB EIP615_JUMPSUB = True"
| "is_eip615_JUMPSUB _ = False"
fun "is_eip615_JUMPSUBV" :: "eip615_inst => bool" where
"is_eip615_JUMPSUBV EIP615_JUMPSUBV = True"
| "is_eip615_JUMPSUBV _ = False"
fun "is_eip615_BEGINSUB" :: "eip615_inst => bool" where
"is_eip615_BEGINSUB EIP615_BEGINSUB = True"
| "is_eip615_BEGINSUB _ = False"
fun "is_eip615_BEGINDATA" :: "eip615_inst => bool" where
"is_eip615_BEGINDATA EIP615_BEGINDATA = True"
| "is_eip615_BEGINDATA _ = False"
fun "is_eip615_RETURNSUB" :: "eip615_inst => bool" where
"is_eip615_RETURNSUB EIP615_RETURNSUB = True"
| "is_eip615_RETURNSUB _ = False"
fun "is_eip615_PUTLOCAL" :: "eip615_inst => bool" where
"is_eip615_PUTLOCAL EIP615_PUTLOCAL = True"
| "is_eip615_PUTLOCAL _ = False"
fun "is_eip615_GETLOCAL" :: "eip615_inst => bool" where
"is_eip615_GETLOCAL EIP615_GETLOCAL = True"
| "is_eip615_GETLOCAL _ = False"

(* 
 * cross-contract communication instructions
 *)
definition comms_codes where
"comms_codes = mk_ranges[(0xf0, 0xf6), (0xfa, 0xfb)]"
declare comms_codes_def[simp]
typedef comms_inst = "set_of_ranges comms_codes" 
  unfolding comms_codes_def
  by(transfer; auto)
setup_lifting type_definition_comms_inst

lift_definition COMMS_CREATE       :: "comms_inst" is "0xf0"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_CALL         :: "comms_inst" is "0xf1"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_CALLCODE     :: "comms_inst" is "0xf2"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_RETURN       :: "comms_inst" is "0xf3"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_DELEGATECALL :: "comms_inst" is "0xf4"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_CREATE2      :: "comms_inst" is "0xf5"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)
lift_definition COMMS_STATICCALL   :: "comms_inst" is "0xfa"
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)

lift_definition COMMS_INST :: "comms_inst => inst" is id
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)

free_constructors cases_comms_inst for
COMMS_CREATE
| COMMS_CALL
| COMMS_CALLCODE
| COMMS_RETURN
| COMMS_DELEGATECALL
| COMMS_CREATE2
| COMMS_STATICCALL
  apply(transfer; simp only:set_of_ranges_alt_spec comms_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)

  by(transfer;
     auto simp add:List.upt_def)+


fun "is_comms_CREATE" :: "comms_inst => bool" where
"is_comms_CREATE COMMS_CREATE = True"
| "is_comms_CREATE _ = False"
fun "is_comms_CALL" :: "comms_inst => bool" where
"is_comms_CALL COMMS_CALL = True"
| "is_comms_CALL _ = False"
fun "is_comms_CALLCODE" :: "comms_inst => bool" where
"is_comms_CALLCODE COMMS_CALLCODE = True"
| "is_comms_CALLCODE _ = False"
fun "is_comms_RETURN" :: "comms_inst => bool" where
"is_comms_RETURN COMMS_RETURN = True"
| "is_comms_RETURN _ = False"
fun "is_comms_DELEGATECALL" :: "comms_inst => bool" where
"is_comms_DELEGATECALL COMMS_DELEGATECALL = True"
| "is_comms_DELEGATECALL _ = False"
fun "is_comms_CREATE2" :: "comms_inst => bool" where
"is_comms_CREATE2 COMMS_CREATE2 = True"
| "is_comms_CREATE2 _ = False"
fun "is_comms_STATICCALL" :: "comms_inst => bool" where
"is_comms_STATICCALL COMMS_STATICCALL = True"
| "is_comms_STATICCALL _ = False"


(* 
 * special halting instructions
 *)
definition special_halt_codes where
"special_halt_codes = mk_ranges [(0xfd, 0x100)]"
declare special_halt_codes_def[simp]
typedef special_halt_inst = "set_of_ranges special_halt_codes" 
  unfolding special_halt_codes_def inst_codes_def
  by(transfer; auto)
setup_lifting type_definition_special_halt_inst

lift_definition SPECIAL_HALT_REVERT       :: "special_halt_inst" is "0xfd" 
  unfolding special_halt_codes_def
  by(transfer; auto)
lift_definition SPECIAL_HALT_INVALID      :: "special_halt_inst" is "0xfe"
  unfolding special_halt_codes_def
  by(transfer; auto)
lift_definition SPECIAL_HALT_SELFDESTRUCT :: "special_halt_inst" is "0xff"
  unfolding special_halt_codes_def
  by(transfer; auto)

lift_definition SPECIAL_HALT_INST :: "special_halt_inst => inst" is id
  unfolding inst_codes_def special_halt_codes_def
  by(transfer; auto)

free_constructors cases_special_halt_inst for
SPECIAL_HALT_REVERT
| SPECIAL_HALT_INVALID
| SPECIAL_HALT_SELFDESTRUCT
  apply(transfer; simp only:set_of_ranges_alt_spec special_halt_codes_def; transfer)
  apply(force simp del:set_upt simp  add:List.upt_def)

  by(transfer;
     auto simp add:List.upt_def)+

fun "is_special_halt_REVERT" :: "special_halt_inst => bool" where
"is_special_halt_REVERT SPECIAL_HALT_REVERT = True"
| "is_special_halt_REVERT _ = False"
fun "is_special_halt_INVALID" :: "special_halt_inst => bool" where
"is_special_halt_INVALID SPECIAL_HALT_INVALID = True"
| "is_special_halt_INVALID _ = False"
fun "is_special_halt_SELFDESTRUCT" :: "special_halt_inst => bool" where
"is_special_halt_SELFDESTRUCT SPECIAL_HALT_SELFDESTRUCT = True"
| "is_special_halt_SELFDESTRUCT _ = False"


(* 
 * Putting the pieces together to get case analysis for all instructions
 *)

(* we are leaving out EIP615 *)
definition good_codes :: "ranges" where
"good_codes = 
  Union_ranges
  [stop_codes,
   arith_codes,
   bits_compare_codes,
   keccak256_codes,
   tx_data_codes,
   chain_data_codes,
   state_control_codes,
   push_codes,
   dup_codes,
   swap_codes,
   log_codes,
   comms_codes,
   special_halt_codes]"

typedef good_inst = "set_of_ranges (good_codes)"
  apply(simp add: good_codes_def)
  apply(transfer) apply(auto)
  done
setup_lifting type_definition_good_inst

lift_definition GOOD_INST :: "good_inst \<Rightarrow> inst" is id
  by(simp add: good_codes_def; transfer; auto)

definition bad_codes :: "ranges" where
"bad_codes = diff_ranges inst_codes good_codes"
typedef bad_inst = "set_of_ranges bad_codes"
  apply(simp add: bad_codes_def good_codes_def)
  apply(transfer) apply(simp)
  apply(auto)
  done
setup_lifting type_definition_bad_inst

lift_definition BAD_INST :: "bad_inst \<Rightarrow> inst" is id
  unfolding bad_codes_def good_codes_def inst_codes_def
  apply(simp)
  apply(transfer) apply(simp)
  apply(auto)
  done

lemma good_bad_all :
  "union_ranges good_codes bad_codes = inst_codes"
  unfolding bad_codes_def good_codes_def
  by(transfer; simp; transfer; auto)

lemma good_bad_all' :
  "Union_ranges [
  stop_codes, 
  arith_codes,
  bits_compare_codes,
  keccak256_codes,
  tx_data_codes,
  chain_data_codes,
  state_control_codes,
  push_codes,
  dup_codes,
  swap_codes,
  log_codes,
  comms_codes,
  special_halt_codes,
  bad_codes] = inst_codes"
  unfolding bad_codes_def good_codes_def
  by(simp; transfer; auto)

lemma cases_inst_helper :
assumes H : "y \<in> set_of_ranges inst_codes"
assumes H1 :  "(\<And>x1. x1 \<in> set_of_ranges stop_codes \<Longrightarrow>
                  y = id x1 \<Longrightarrow> P)"
assumes H2 : "(\<And>x2. x2 \<in> set_of_ranges arith_codes \<Longrightarrow>
                  y = id x2 \<Longrightarrow> P)"
assumes H3 : "(\<And>x3. x3 \<in> set_of_ranges bits_compare_codes \<Longrightarrow>
                  y = id x3 \<Longrightarrow> P)"
assumes H4: "(\<And>x4. x4 \<in> set_of_ranges keccak256_codes \<Longrightarrow>
                  y = id x4 \<Longrightarrow> P)"
assumes H5 : "(\<And>x5. x5 \<in> set_of_ranges tx_data_codes \<Longrightarrow>
                  y = id x5 \<Longrightarrow> P)"
assumes H6 : "(\<And>x6. x6 \<in> set_of_ranges chain_data_codes \<Longrightarrow>
                  y = id x6 \<Longrightarrow> P)"
assumes H7 : "(\<And>x7. x7 \<in> set_of_ranges state_control_codes \<Longrightarrow>
                  y = id x7 \<Longrightarrow> P)"
assumes H8 : "(\<And> x8. x8 \<in> set_of_ranges push_codes \<Longrightarrow>
                  y = id x8 \<Longrightarrow> P)"
assumes H9 : "(\<And>x9. x9 \<in> set_of_ranges dup_codes \<Longrightarrow>
                  y = id x9 \<Longrightarrow> P)"
assumes H10 : "(\<And>x10. x10 \<in> set_of_ranges swap_codes \<Longrightarrow>
                   y = id x10 \<Longrightarrow> P)"
assumes H11 : "(\<And>x11. x11 \<in> set_of_ranges log_codes \<Longrightarrow>
                   y = id x11 \<Longrightarrow> P)"
assumes H12 : "(\<And>x12. x12 \<in> set_of_ranges comms_codes \<Longrightarrow>
                   y = id x12 \<Longrightarrow> P)"
assumes H13 : "(\<And>x13. x13 \<in> set_of_ranges special_halt_codes \<Longrightarrow>
                   y = id x13 \<Longrightarrow> P)"
assumes H14 : "(\<And>x14. x14 \<in> set_of_ranges bad_codes \<Longrightarrow>
                   y = id x14 \<Longrightarrow> P)"
shows P
proof-

  have H' : "member_ranges y (Union_ranges [
          stop_codes, 
          arith_codes,
          bits_compare_codes,
          keccak256_codes,
          tx_data_codes,
          chain_data_codes,
          state_control_codes,
          push_codes,
          dup_codes,
          swap_codes,
          log_codes,
          comms_codes,
          special_halt_codes,
          bad_codes])"
    using H unfolding sym[OF good_bad_all'] member_ranges_spec by(auto)

  have Conc' : "(y = y \<longrightarrow> P)"
  proof(rule Union_ranges_cases[OF _ H', of "\<lambda> x . (y = x \<longrightarrow> P)"] )
    fix r x
    assume R_cases :
    "r \<in> set [stop_codes, arith_codes, bits_compare_codes,
                    keccak256_codes, tx_data_codes,
                    chain_data_codes, state_control_codes,
                    push_codes, dup_codes, swap_codes, log_codes,
                    comms_codes, special_halt_codes,
                    bad_codes]"
    assume R_mem : "member_ranges x r"
    consider (1) "r = stop_codes" | 
             (2) "r = arith_codes" |
             (3) "r = bits_compare_codes" |
             (4) "r = keccak256_codes" |
             (5) "r = tx_data_codes" |
             (6) "r = chain_data_codes" |
             (7) "r = state_control_codes" |
             (8) "r = push_codes" |
             (9) "r = dup_codes" |
             (10) "r = swap_codes" |
             (11) "r = log_codes" |
             (12) "r = comms_codes" |
             (13) "r = special_halt_codes" |
             (14) "r = bad_codes"
      using R_cases by(auto)
    thus "y = x \<longrightarrow> P"
    proof cases
    case 1
      then show ?thesis using H1 R_mem unfolding member_ranges_spec by(auto)
    next
      case 2
      then show ?thesis using H2 R_mem unfolding member_ranges_spec by(auto)
    next
      case 3
      then show ?thesis using H3 R_mem unfolding member_ranges_spec by(auto)
    next
      case 4
      then show ?thesis using H4 R_mem unfolding member_ranges_spec by(auto)
    next
      case 5
      then show ?thesis using H5 R_mem unfolding member_ranges_spec by(auto)
    next
      case 6
      then show ?thesis using H6 R_mem unfolding member_ranges_spec by(auto)
    next
      case 7
      then show ?thesis using H7 R_mem unfolding member_ranges_spec by(auto)
    next
      case 8
      then show ?thesis using H8 R_mem unfolding member_ranges_spec by(auto)
    next
      case 9
      then show ?thesis using H9 R_mem unfolding member_ranges_spec by(auto)
    next
      case 10
      then show ?thesis using H10 R_mem unfolding member_ranges_spec by(auto)
    next
      case 11
      then show ?thesis using H11 R_mem unfolding member_ranges_spec by(auto)
    next
      case 12
      then show ?thesis using H12 R_mem unfolding member_ranges_spec by(auto)
    next
      case 13
      then show ?thesis using H13 R_mem unfolding member_ranges_spec by(auto)
    next
      case 14
      then show ?thesis using H14 R_mem unfolding member_ranges_spec by(auto)
    qed
  qed
  thus ?thesis by auto
qed

lift_definition parse_byte_inst :: "8 word \<Rightarrow> inst"
is unat
proof-
  fix wd :: "8 word"
  show "unat wd \<in> set_of_ranges inst_codes"
    unfolding inst_codes_def
  proof(transfer)
    fix wd :: int
    show "(nat \<circ> take_bit LENGTH(8)) wd
          \<in> set_of_ranges' (mk_ranges' [(0, 256)])"
      using Bits_Int.bintr_lt2p[of "8" "wd"]
      by simp
  qed
qed

free_constructors cases_inst for
STOP_INST
| ARITH_INST
| BITS_COMPARE_INST
| KECCAK256_INST
| TX_DATA_INST
| CHAIN_DATA_INST
| STATE_CONTROL_INST
| PUSH_INST
| DUP_INST
| SWAP_INST
| LOG_INST
| COMMS_INST
| SPECIAL_HALT_INST
| BAD_INST
  apply(transfer)
  apply(rule cases_inst_helper; blast)
  apply(transfer; simp add: bad_codes_def good_codes_def; transfer; force; fail)+
  done

(*
 * Having defined inst, now we can define some further abbreviations
 *)


definition is_STOP :: "inst => bool" where
"is_STOP i ==
  (case i of STOP_INST _ => True
  | _ => False)"
  
abbreviation eSTOP :: "inst" where
"eSTOP == STOP_INST STOP_STOP"

definition is_eSTOP :: "inst => bool" where
"is_eSTOP i ==
  (case i of eSTOP => True
  | _ => False)"


definition is_ARITH :: "inst => bool" where
"is_ARITH i ==
  (case i of ARITH_INST _ => True
  | _ => False)"
  
abbreviation eADD :: "inst" where
"eADD == ARITH_INST ARITH_ADD"

definition is_eADD :: "inst => bool" where
"is_eADD i ==
  (case i of eADD => True
  | _ => False)"


abbreviation eMUL :: "inst" where
"eMUL == ARITH_INST ARITH_MUL"

definition is_eMUL :: "inst => bool" where
"is_eMUL i ==
  (case i of eMUL => True
  | _ => False)"


abbreviation eSUB :: "inst" where
"eSUB == ARITH_INST ARITH_SUB"

definition is_eSUB :: "inst => bool" where
"is_eSUB i ==
  (case i of eSUB => True
  | _ => False)"


abbreviation eDIV :: "inst" where
"eDIV == ARITH_INST ARITH_DIV"

definition is_eDIV :: "inst => bool" where
"is_eDIV i ==
  (case i of eDIV => True
  | _ => False)"


abbreviation eSDIV :: "inst" where
"eSDIV == ARITH_INST ARITH_SDIV"

definition is_eSDIV :: "inst => bool" where
"is_eSDIV i ==
  (case i of eSDIV => True
  | _ => False)"


abbreviation eMOD :: "inst" where
"eMOD == ARITH_INST ARITH_MOD"

definition is_eMOD :: "inst => bool" where
"is_eMOD i ==
  (case i of eMOD => True
  | _ => False)"


abbreviation eSMOD :: "inst" where
"eSMOD == ARITH_INST ARITH_SMOD"

definition is_eSMOD :: "inst => bool" where
"is_eSMOD i ==
  (case i of eSMOD => True
  | _ => False)"


abbreviation eADDMOD :: "inst" where
"eADDMOD == ARITH_INST ARITH_ADDMOD"

definition is_eADDMOD :: "inst => bool" where
"is_eADDMOD i ==
  (case i of eADDMOD => True
  | _ => False)"


abbreviation eMULMOD :: "inst" where
"eMULMOD == ARITH_INST ARITH_MULMOD"

definition is_eMULMOD :: "inst => bool" where
"is_eMULMOD i ==
  (case i of eMULMOD => True
  | _ => False)"


abbreviation eEXP :: "inst" where
"eEXP == ARITH_INST ARITH_EXP"

definition is_eEXP :: "inst => bool" where
"is_eEXP i ==
  (case i of eEXP => True
  | _ => False)"


abbreviation eSIGNEXTEND :: "inst" where
"eSIGNEXTEND == ARITH_INST ARITH_SIGNEXTEND"

definition is_eSIGNEXTEND :: "inst => bool" where
"is_eSIGNEXTEND i ==
  (case i of eSIGNEXTEND => True
  | _ => False)"


definition is_BITS_COMPARE :: "inst => bool" where
"is_BITS_COMPARE i ==
  (case i of BITS_COMPARE_INST _ => True
  | _ => False)"
  
abbreviation eLT :: "inst" where
"eLT == BITS_COMPARE_INST BITS_COMPARE_LT"

definition is_eLT :: "inst => bool" where
"is_eLT i ==
  (case i of eLT => True
  | _ => False)"


abbreviation eGT :: "inst" where
"eGT == BITS_COMPARE_INST BITS_COMPARE_GT"

definition is_eGT :: "inst => bool" where
"is_eGT i ==
  (case i of eGT => True
  | _ => False)"


abbreviation eSLT :: "inst" where
"eSLT == BITS_COMPARE_INST BITS_COMPARE_SLT"

definition is_eSLT :: "inst => bool" where
"is_eSLT i ==
  (case i of eSLT => True
  | _ => False)"


abbreviation eSGT :: "inst" where
"eSGT == BITS_COMPARE_INST BITS_COMPARE_SGT"

definition is_eSGT :: "inst => bool" where
"is_eSGT i ==
  (case i of eSGT => True
  | _ => False)"


abbreviation eEQ :: "inst" where
"eEQ == BITS_COMPARE_INST BITS_COMPARE_EQ"

definition is_eEQ :: "inst => bool" where
"is_eEQ i ==
  (case i of eEQ => True
  | _ => False)"


abbreviation eISZERO :: "inst" where
"eISZERO == BITS_COMPARE_INST BITS_COMPARE_ISZERO"

definition is_eISZERO :: "inst => bool" where
"is_eISZERO i ==
  (case i of eISZERO => True
  | _ => False)"


abbreviation eAND :: "inst" where
"eAND == BITS_COMPARE_INST BITS_COMPARE_AND"

definition is_eAND :: "inst => bool" where
"is_eAND i ==
  (case i of eAND => True
  | _ => False)"


abbreviation eOR :: "inst" where
"eOR == BITS_COMPARE_INST BITS_COMPARE_OR"

definition is_eOR :: "inst => bool" where
"is_eOR i ==
  (case i of eOR => True
  | _ => False)"


abbreviation eXOR :: "inst" where
"eXOR == BITS_COMPARE_INST BITS_COMPARE_XOR"

definition is_eXOR :: "inst => bool" where
"is_eXOR i ==
  (case i of eXOR => True
  | _ => False)"


abbreviation eNOT :: "inst" where
"eNOT == BITS_COMPARE_INST BITS_COMPARE_NOT"

definition is_eNOT :: "inst => bool" where
"is_eNOT i ==
  (case i of eNOT => True
  | _ => False)"


abbreviation eBYTE :: "inst" where
"eBYTE == BITS_COMPARE_INST BITS_COMPARE_BYTE"

definition is_eBYTE :: "inst => bool" where
"is_eBYTE i ==
  (case i of eBYTE => True
  | _ => False)"


abbreviation eSHL :: "inst" where
"eSHL == BITS_COMPARE_INST BITS_COMPARE_SHL"

definition is_eSHL :: "inst => bool" where
"is_eSHL i ==
  (case i of eSHL => True
  | _ => False)"


abbreviation eSHR :: "inst" where
"eSHR == BITS_COMPARE_INST BITS_COMPARE_SHR"

definition is_eSHR :: "inst => bool" where
"is_eSHR i ==
  (case i of eSHR => True
  | _ => False)"


abbreviation eSAR :: "inst" where
"eSAR == BITS_COMPARE_INST BITS_COMPARE_SAR"

definition is_eSAR :: "inst => bool" where
"is_eSAR i ==
  (case i of eSAR => True
  | _ => False)"


definition is_KECCAK256 :: "inst => bool" where
"is_KECCAK256 i ==
  (case i of KECCAK256_INST _ => True
  | _ => False)"
  
abbreviation eKECCAK256 :: "inst" where
"eKECCAK256 == KECCAK256_INST KECCAK256_KECCAK256"

definition is_eKECCAK256 :: "inst => bool" where
"is_eKECCAK256 i ==
  (case i of eKECCAK256 => True
  | _ => False)"


definition is_TX_DATA :: "inst => bool" where
"is_TX_DATA i ==
  (case i of TX_DATA_INST _ => True
  | _ => False)"
  
abbreviation eADDRESS :: "inst" where
"eADDRESS == TX_DATA_INST TX_DATA_ADDRESS"

definition is_eADDRESS :: "inst => bool" where
"is_eADDRESS i ==
  (case i of eADDRESS => True
  | _ => False)"


abbreviation eBALANCE :: "inst" where
"eBALANCE == TX_DATA_INST TX_DATA_BALANCE"

definition is_eBALANCE :: "inst => bool" where
"is_eBALANCE i ==
  (case i of eBALANCE => True
  | _ => False)"


abbreviation eORIGIN :: "inst" where
"eORIGIN == TX_DATA_INST TX_DATA_ORIGIN"

definition is_eORIGIN :: "inst => bool" where
"is_eORIGIN i ==
  (case i of eORIGIN => True
  | _ => False)"


abbreviation eCALLER :: "inst" where
"eCALLER == TX_DATA_INST TX_DATA_CALLER"

definition is_eCALLER :: "inst => bool" where
"is_eCALLER i ==
  (case i of eCALLER => True
  | _ => False)"


abbreviation eCALLVALUE :: "inst" where
"eCALLVALUE == TX_DATA_INST TX_DATA_CALLVALUE"

definition is_eCALLVALUE :: "inst => bool" where
"is_eCALLVALUE i ==
  (case i of eCALLVALUE => True
  | _ => False)"


abbreviation eCALLDATALOAD :: "inst" where
"eCALLDATALOAD == TX_DATA_INST TX_DATA_CALLDATALOAD"

definition is_eCALLDATALOAD :: "inst => bool" where
"is_eCALLDATALOAD i ==
  (case i of eCALLDATALOAD => True
  | _ => False)"


abbreviation eCALLDATASIZE :: "inst" where
"eCALLDATASIZE == TX_DATA_INST TX_DATA_CALLDATASIZE"

definition is_eCALLDATASIZE :: "inst => bool" where
"is_eCALLDATASIZE i ==
  (case i of eCALLDATASIZE => True
  | _ => False)"


abbreviation eCALLDATACOPY :: "inst" where
"eCALLDATACOPY == TX_DATA_INST TX_DATA_CALLDATACOPY"

definition is_eCALLDATACOPY :: "inst => bool" where
"is_eCALLDATACOPY i ==
  (case i of eCALLDATACOPY => True
  | _ => False)"


abbreviation eCODESIZE :: "inst" where
"eCODESIZE == TX_DATA_INST TX_DATA_CODESIZE"

definition is_eCODESIZE :: "inst => bool" where
"is_eCODESIZE i ==
  (case i of eCODESIZE => True
  | _ => False)"


abbreviation eCODECOPY :: "inst" where
"eCODECOPY == TX_DATA_INST TX_DATA_CODECOPY"

definition is_eCODECOPY :: "inst => bool" where
"is_eCODECOPY i ==
  (case i of eCODECOPY => True
  | _ => False)"


abbreviation eGASPRICE :: "inst" where
"eGASPRICE == TX_DATA_INST TX_DATA_GASPRICE"

definition is_eGASPRICE :: "inst => bool" where
"is_eGASPRICE i ==
  (case i of eGASPRICE => True
  | _ => False)"


abbreviation eEXTCODESIZE :: "inst" where
"eEXTCODESIZE == TX_DATA_INST TX_DATA_EXTCODESIZE"

definition is_eEXTCODESIZE :: "inst => bool" where
"is_eEXTCODESIZE i ==
  (case i of eEXTCODESIZE => True
  | _ => False)"


abbreviation eEXTCODECOPY :: "inst" where
"eEXTCODECOPY == TX_DATA_INST TX_DATA_EXTCODECOPY"

definition is_eEXTCODECOPY :: "inst => bool" where
"is_eEXTCODECOPY i ==
  (case i of eEXTCODECOPY => True
  | _ => False)"


abbreviation eRETURNDATASIZE :: "inst" where
"eRETURNDATASIZE == TX_DATA_INST TX_DATA_RETURNDATASIZE"

definition is_eRETURNDATASIZE :: "inst => bool" where
"is_eRETURNDATASIZE i ==
  (case i of eRETURNDATASIZE => True
  | _ => False)"


abbreviation eRETURNDATACOPY :: "inst" where
"eRETURNDATACOPY == TX_DATA_INST TX_DATA_RETURNDATACOPY"

definition is_eRETURNDATACOPY :: "inst => bool" where
"is_eRETURNDATACOPY i ==
  (case i of eRETURNDATACOPY => True
  | _ => False)"


abbreviation eEXTCODEHASH :: "inst" where
"eEXTCODEHASH == TX_DATA_INST TX_DATA_EXTCODEHASH"

definition is_eEXTCODEHASH :: "inst => bool" where
"is_eEXTCODEHASH i ==
  (case i of eEXTCODEHASH => True
  | _ => False)"


definition is_CHAIN_DATA :: "inst => bool" where
"is_CHAIN_DATA i ==
  (case i of CHAIN_DATA_INST _ => True
  | _ => False)"
  
abbreviation eBLOCKHASH :: "inst" where
"eBLOCKHASH == CHAIN_DATA_INST CHAIN_DATA_BLOCKHASH"

definition is_eBLOCKHASH :: "inst => bool" where
"is_eBLOCKHASH i ==
  (case i of eBLOCKHASH => True
  | _ => False)"


abbreviation eCOINBASE :: "inst" where
"eCOINBASE == CHAIN_DATA_INST CHAIN_DATA_COINBASE"

definition is_eCOINBASE :: "inst => bool" where
"is_eCOINBASE i ==
  (case i of eCOINBASE => True
  | _ => False)"


abbreviation eTIMESTAMP :: "inst" where
"eTIMESTAMP == CHAIN_DATA_INST CHAIN_DATA_TIMESTAMP"

definition is_eTIMESTAMP :: "inst => bool" where
"is_eTIMESTAMP i ==
  (case i of eTIMESTAMP => True
  | _ => False)"


abbreviation eNUMBER :: "inst" where
"eNUMBER == CHAIN_DATA_INST CHAIN_DATA_NUMBER"

definition is_eNUMBER :: "inst => bool" where
"is_eNUMBER i ==
  (case i of eNUMBER => True
  | _ => False)"


abbreviation eDIFFICULTY :: "inst" where
"eDIFFICULTY == CHAIN_DATA_INST CHAIN_DATA_DIFFICULTY"

definition is_eDIFFICULTY :: "inst => bool" where
"is_eDIFFICULTY i ==
  (case i of eDIFFICULTY => True
  | _ => False)"


abbreviation eCHAINID :: "inst" where
"eCHAINID == CHAIN_DATA_INST CHAIN_DATA_CHAINID"

definition is_eCHAINID :: "inst => bool" where
"is_eCHAINID i ==
  (case i of eCHAINID => True
  | _ => False)"


abbreviation eSELFBALANCE :: "inst" where
"eSELFBALANCE == CHAIN_DATA_INST CHAIN_DATA_SELFBALANCE"

definition is_eSELFBALANCE :: "inst => bool" where
"is_eSELFBALANCE i ==
  (case i of eSELFBALANCE => True
  | _ => False)"


definition is_STATE_CONTROL :: "inst => bool" where
"is_STATE_CONTROL i ==
  (case i of STATE_CONTROL_INST _ => True
  | _ => False)"
  
abbreviation ePOP :: "inst" where
"ePOP == STATE_CONTROL_INST STATE_CONTROL_POP"

definition is_ePOP :: "inst => bool" where
"is_ePOP i ==
  (case i of ePOP => True
  | _ => False)"


abbreviation eMLOAD :: "inst" where
"eMLOAD == STATE_CONTROL_INST STATE_CONTROL_MLOAD"

definition is_eMLOAD :: "inst => bool" where
"is_eMLOAD i ==
  (case i of eMLOAD => True
  | _ => False)"


abbreviation eMSTORE :: "inst" where
"eMSTORE == STATE_CONTROL_INST STATE_CONTROL_MSTORE"

definition is_eMSTORE :: "inst => bool" where
"is_eMSTORE i ==
  (case i of eMSTORE => True
  | _ => False)"


abbreviation eMSTORE8 :: "inst" where
"eMSTORE8 == STATE_CONTROL_INST STATE_CONTROL_MSTORE8"

definition is_eMSTORE8 :: "inst => bool" where
"is_eMSTORE8 i ==
  (case i of eMSTORE8 => True
  | _ => False)"


abbreviation eSLOAD :: "inst" where
"eSLOAD == STATE_CONTROL_INST STATE_CONTROL_SLOAD"

definition is_eSLOAD :: "inst => bool" where
"is_eSLOAD i ==
  (case i of eSLOAD => True
  | _ => False)"


abbreviation eSSTORE :: "inst" where
"eSSTORE == STATE_CONTROL_INST STATE_CONTROL_SSTORE"

definition is_eSSTORE :: "inst => bool" where
"is_eSSTORE i ==
  (case i of eSSTORE => True
  | _ => False)"


abbreviation eJUMP :: "inst" where
"eJUMP == STATE_CONTROL_INST STATE_CONTROL_JUMP"

definition is_eJUMP :: "inst => bool" where
"is_eJUMP i ==
  (case i of eJUMP => True
  | _ => False)"


abbreviation eJUMPI :: "inst" where
"eJUMPI == STATE_CONTROL_INST STATE_CONTROL_JUMPI"

definition is_eJUMPI :: "inst => bool" where
"is_eJUMPI i ==
  (case i of eJUMPI => True
  | _ => False)"


abbreviation ePC :: "inst" where
"ePC == STATE_CONTROL_INST STATE_CONTROL_PC"

definition is_ePC :: "inst => bool" where
"is_ePC i ==
  (case i of ePC => True
  | _ => False)"


abbreviation eMSIZE :: "inst" where
"eMSIZE == STATE_CONTROL_INST STATE_CONTROL_MSIZE"

definition is_eMSIZE :: "inst => bool" where
"is_eMSIZE i ==
  (case i of eMSIZE => True
  | _ => False)"


abbreviation eGAS :: "inst" where
"eGAS == STATE_CONTROL_INST STATE_CONTROL_GAS"

definition is_eGAS :: "inst => bool" where
"is_eGAS i ==
  (case i of eGAS => True
  | _ => False)"


abbreviation eJUMPDEST :: "inst" where
"eJUMPDEST == STATE_CONTROL_INST STATE_CONTROL_JUMPDEST"

definition is_eJUMPDEST :: "inst => bool" where
"is_eJUMPDEST i ==
  (case i of eJUMPDEST => True
  | _ => False)"

definition is_PUSH :: "inst => bool" where
"is_PUSH i ==
  (case i of PUSH_INST _ => True
  | _ => False)"

(* NB: we cannot pattern match on this. *)
abbreviation mkPUSH :: "nat \<Rightarrow> inst" where
"mkPUSH n \<equiv> PUSH_INST (MAKE_PUSH n)"

abbreviation ePUSH :: "nat32 \<Rightarrow> inst" where
"ePUSH n \<equiv> PUSH_INST (PUSH_PUSH n)"

  
definition is_DUP :: "inst => bool" where
"is_DUP i ==
  (case i of DUP_INST _ => True
  | _ => False)"

(* NB: we cannot pattern match on this. *)
abbreviation mkDUP :: "nat \<Rightarrow> inst" where
"mkDUP n \<equiv> DUP_INST (MAKE_DUP n)"

abbreviation eDUP :: "nat16 \<Rightarrow> inst" where
"eDUP n \<equiv> DUP_INST (DUP_DUP n)"

  
definition is_SWAP :: "inst => bool" where
"is_SWAP i ==
  (case i of SWAP_INST _ => True
  | _ => False)"

(* NB: we cannot pattern match on this. *)
abbreviation mkSWAP :: "nat \<Rightarrow> inst" where
"mkSWAP n \<equiv> SWAP_INST (MAKE_SWAP n)"

abbreviation eSWAP :: "nat16 \<Rightarrow> inst" where
"eSWAP n \<equiv> SWAP_INST (SWAP_SWAP n)"

  
definition is_LOG :: "inst => bool" where
"is_LOG i ==
  (case i of LOG_INST _ => True
  | _ => False)"
  
abbreviation eLOG0 :: "inst" where
"eLOG0 == LOG_INST LOG_LOG0"

definition is_eLOG0 :: "inst => bool" where
"is_eLOG0 i ==
  (case i of eLOG0 => True
  | _ => False)"


abbreviation eLOG1 :: "inst" where
"eLOG1 == LOG_INST LOG_LOG1"

definition is_eLOG1 :: "inst => bool" where
"is_eLOG1 i ==
  (case i of eLOG1 => True
  | _ => False)"


abbreviation eLOG2 :: "inst" where
"eLOG2 == LOG_INST LOG_LOG2"

definition is_eLOG2 :: "inst => bool" where
"is_eLOG2 i ==
  (case i of eLOG2 => True
  | _ => False)"


abbreviation eLOG3 :: "inst" where
"eLOG3 == LOG_INST LOG_LOG3"

definition is_eLOG3 :: "inst => bool" where
"is_eLOG3 i ==
  (case i of eLOG3 => True
  | _ => False)"


abbreviation eLOG4 :: "inst" where
"eLOG4 == LOG_INST LOG_LOG4"

definition is_eLOG4 :: "inst => bool" where
"is_eLOG4 i ==
  (case i of eLOG4 => True
  | _ => False)"

(* EIP615 instructions would go here *)

definition is_COMMS :: "inst => bool" where
"is_COMMS i ==
  (case i of COMMS_INST _ => True
  | _ => False)"
  
abbreviation eCREATE :: "inst" where
"eCREATE == COMMS_INST COMMS_CREATE"

definition is_eCREATE :: "inst => bool" where
"is_eCREATE i ==
  (case i of eCREATE => True
  | _ => False)"


abbreviation eCALL :: "inst" where
"eCALL == COMMS_INST COMMS_CALL"

definition is_eCALL :: "inst => bool" where
"is_eCALL i ==
  (case i of eCALL => True
  | _ => False)"


abbreviation eCALLCODE :: "inst" where
"eCALLCODE == COMMS_INST COMMS_CALLCODE"

definition is_eCALLCODE :: "inst => bool" where
"is_eCALLCODE i ==
  (case i of eCALLCODE => True
  | _ => False)"


abbreviation eRETURN :: "inst" where
"eRETURN == COMMS_INST COMMS_RETURN"

definition is_eRETURN :: "inst => bool" where
"is_eRETURN i ==
  (case i of eRETURN => True
  | _ => False)"


abbreviation eDELEGATECALL :: "inst" where
"eDELEGATECALL == COMMS_INST COMMS_DELEGATECALL"

definition is_eDELEGATECALL :: "inst => bool" where
"is_eDELEGATECALL i ==
  (case i of eDELEGATECALL => True
  | _ => False)"


abbreviation eCREATE2 :: "inst" where
"eCREATE2 == COMMS_INST COMMS_CREATE2"

definition is_eCREATE2 :: "inst => bool" where
"is_eCREATE2 i ==
  (case i of eCREATE2 => True
  | _ => False)"


abbreviation eSTATICCALL :: "inst" where
"eSTATICCALL == COMMS_INST COMMS_STATICCALL"

definition is_eSTATICCALL :: "inst => bool" where
"is_eSTATICCALL i ==
  (case i of eSTATICCALL => True
  | _ => False)"


definition is_SPECIAL_HALT :: "inst => bool" where
"is_SPECIAL_HALT i ==
  (case i of SPECIAL_HALT_INST _ => True
  | _ => False)"
  
abbreviation eREVERT :: "inst" where
"eREVERT == SPECIAL_HALT_INST SPECIAL_HALT_REVERT"

definition is_eREVERT :: "inst => bool" where
"is_eREVERT i ==
  (case i of eREVERT => True
  | _ => False)"


abbreviation eINVALID :: "inst" where
"eINVALID == SPECIAL_HALT_INST SPECIAL_HALT_INVALID"

definition is_eINVALID :: "inst => bool" where
"is_eINVALID i ==
  (case i of eINVALID => True
  | _ => False)"


abbreviation eSELFDESTRUCT :: "inst" where
"eSELFDESTRUCT == SPECIAL_HALT_INST SPECIAL_HALT_SELFDESTRUCT"

definition is_eSELFDESTRUCT :: "inst => bool" where
"is_eSELFDESTRUCT i ==
  (case i of eSELFDESTRUCT => True
  | _ => False)"


(*
 * Parsing bytes as instructions
 * member_ranges
 * in order to avoid issues with the code generator, I think we would need to do
 * something like this for all instructions...
 *)
fun parse_stop_inst :: "nat \<Rightarrow> inst" where
"parse_stop_inst _ = eSTOP"

fun parse_arith_inst :: "nat \<Rightarrow> inst" where
"parse_arith_inst n =
  (if n = 0x01 then eADD else
  (if n = 0x02 then eMUL else
  (if n = 0x03 then eSUB else
  (if n = 0x04 then eDIV else
  (if n = 0x05 then eSDIV else
  (if n = 0x06 then eMOD else   
  (if n = 0x07 then eSMOD else
  (if n = 0x08 then eADDMOD else
  (if n = 0x09 then eMULMOD else
  (if n = 0x0a then eEXP else
  (if n = 0x0b then eSIGNEXTEND else
   eADD)))))))))))"



(*

fun parse_stop_inst w where
"parse_stop_inst 4 = 

*)

(*
fun parse_byte_inst :: "nat \<Rightarrow> inst" where
"parse_byte_inst w =
  (if member_ranges w stop_codes then parse_stop_inst w else
  (if member_ranges w arith_codes then parse_arith_inst w ele
  (if member_ranges w bits_compare_codes then parse_bits_compare_inst w else
  (if member_ranges w keccak256_codes then parse_keccak256_inst w else
  (if member_ranges w tx_data_codes then parse_tx_data_inst w else
  (if member_ranges w chain_data_codes then parse_chain_data_inst w else
  (if member_ranges w state_control_codes then parse_state_control_inst w else
  (if member_ranges w push_codes then parse_push_inst w else
  (if member_ranges w dup_codes then parse_dup_inst w else
  (if member_ranges w swap_codes then parse_swap_inst w else
  (if member_ranges w log_codes then parse_log_inst w else
  (if member_ranges w comms_codes then parse_comms_inst w else
  (if member_ranges w special_halt_codes then parse_special_halt_inst w else
   parse_bad_codes w)))))))))))))
*)
end
  