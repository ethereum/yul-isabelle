theory LowLevelEvm imports Main "HOL-Library.Numeral_Type" MiniEvm "HOL-Library.Adhoc_Overloading"
"HOL-Eisbach.Eisbach_Tools"
begin

(* define EVM instruction syntax in terms of their representation as instruction-words *)
typedef inst = "{n :: nat . n < 256 }"
proof-
  have "(0 :: nat) \<in> {n . n < 256}" by auto
  thus "\<exists> (x :: nat) . x \<in> {n . n < 256}" by blast
qed
setup_lifting type_definition_inst

(* begin opcodes *)
(* 
 * STOP
 *)
definition stop_codes  :: "nat set"  where "stop_codes = {0 :: nat}" 
declare stop_codes_def [simp add]
typedef stop_inst = "stop_codes" by auto
setup_lifting type_definition_stop_inst

lift_definition STOP_INST :: "stop_inst \<Rightarrow> inst" is id by auto

lift_definition STOP_STOP :: stop_inst is "0x00 :: nat" by auto
free_constructors cases_stop_inst for STOP_STOP
  by (transfer; auto)+

definition is_STOP :: "stop_inst \<Rightarrow> bool" where
"is_STOP x \<equiv> case x of STOP_STOP \<Rightarrow> True"

(*
 * Arithmetic
 *)
definition arith_codes :: "nat set" where 
"arith_codes = set (List.upt 0x01 0x0c)"

declare arith_codes_def [simp add]
typedef arith_inst = "arith_codes" by auto
setup_lifting type_definition_arith_inst

lift_definition ARITH_INST :: "arith_inst \<Rightarrow> inst" is id by auto

lift_definition ARITH_ADD        :: "arith_inst" is "0x01 :: nat" by auto
lift_definition ARITH_MUL        :: "arith_inst" is "0x02 :: nat" by auto
lift_definition ARITH_SUB        :: "arith_inst" is "0x03 :: nat" by auto
lift_definition ARITH_DIV        :: "arith_inst" is "0x04 :: nat" by auto
lift_definition ARITH_SDIV       :: "arith_inst" is "0x05 :: nat" by auto
lift_definition ARITH_MOD        :: "arith_inst" is "0x06 :: nat" by auto
lift_definition ARITH_SMOD       :: "arith_inst" is "0x07 :: nat" by auto
lift_definition ARITH_ADDMOD     :: "arith_inst" is "0x08 :: nat" by auto
lift_definition ARITH_MULMOD     :: "arith_inst" is "0x09 :: nat" by auto
lift_definition ARITH_EXP        :: "arith_inst" is "0x0a :: nat" by auto
lift_definition ARITH_SIGNEXTEND :: "arith_inst" is "0x0b :: nat" by auto

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
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
 * Comparisons
 *)
definition compare_codes :: "nat set" where 
  "compare_codes = set (List.upt 0x10 0x16)"
declare compare_codes_def [simp add]
typedef compare_inst = "compare_codes" by auto
setup_lifting type_definition_compare_inst

lift_definition COMPARE_LT     :: "compare_inst" is "0x10" by auto
lift_definition COMPARE_GT     :: "compare_inst" is "0x11" by auto
lift_definition COMPARE_SLT    :: "compare_inst" is "0x12" by auto
lift_definition COMPARE_SGT    :: "compare_inst" is "0x13" by auto
lift_definition COMPARE_EQ     :: "compare_inst" is "0x14" by auto
lift_definition COMPARE_ISZERO :: "compare_inst" is "0x15" by auto

lift_definition COMPARE_INST :: "compare_inst \<Rightarrow> inst" is id by auto

free_constructors cases_compare_inst for
  COMPARE_LT
| COMPARE_GT
| COMPARE_SLT
| COMPARE_SGT
| COMPARE_EQ
| COMPARE_ISZERO
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_compare_LT" :: "compare_inst => bool" where
"is_compare_LT COMPARE_LT = True"
| "is_compare_LT _ = False"
fun "is_compare_GT" :: "compare_inst => bool" where
"is_compare_GT COMPARE_GT = True"
| "is_compare_GT _ = False"
fun "is_compare_SLT" :: "compare_inst => bool" where
"is_compare_SLT COMPARE_SLT = True"
| "is_compare_SLT _ = False"
fun "is_compare_SGT" :: "compare_inst => bool" where
"is_compare_SGT COMPARE_SGT = True"
| "is_compare_SGT _ = False"
fun "is_compare_EQ" :: "compare_inst => bool" where
"is_compare_EQ COMPARE_EQ = True"
| "is_compare_EQ _ = False"
fun "is_compare_ISZERO" :: "compare_inst => bool" where
"is_compare_ISZERO COMPARE_ISZERO = True"
| "is_compare_ISZERO _ = False"


(* 
 * bits
 *)
definition bits_codes :: "nat set" where "bits_codes = set (List.upt 0x16 0x1e)"
declare bits_codes_def [simp add]
typedef bits_inst = "bits_codes" by auto
setup_lifting type_definition_bits_inst

lift_definition BITS_AND  :: "bits_inst" is "0x16" by auto
lift_definition BITS_OR   :: "bits_inst" is "0x17" by auto
lift_definition BITS_XOR  :: "bits_inst" is "0x18" by auto
lift_definition BITS_NOT  :: "bits_inst" is "0x19" by auto
lift_definition BITS_BYTE :: "bits_inst" is "0x1a" by auto
lift_definition BITS_SHL  :: "bits_inst" is "0x1b" by auto
lift_definition BITS_SHR  :: "bits_inst" is "0x1c" by auto
lift_definition BITS_SAR  :: "bits_inst" is "0x1d" by auto

lift_definition BITS_INST :: "bits_inst \<Rightarrow> inst" is id by auto

free_constructors cases_bits_inst for
  BITS_AND
| BITS_OR
| BITS_XOR
| BITS_NOT
| BITS_BYTE
| BITS_SHL
| BITS_SHR
| BITS_SAR
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_bits_AND" :: "bits_inst => bool" where
"is_bits_AND BITS_AND = True"
| "is_bits_AND _ = False"
fun "is_bits_OR" :: "bits_inst => bool" where
"is_bits_OR BITS_OR = True"
| "is_bits_OR _ = False"
fun "is_bits_XOR" :: "bits_inst => bool" where
"is_bits_XOR BITS_XOR = True"
| "is_bits_XOR _ = False"
fun "is_bits_NOT" :: "bits_inst => bool" where
"is_bits_NOT BITS_NOT = True"
| "is_bits_NOT _ = False"
fun "is_bits_BYTE" :: "bits_inst => bool" where
"is_bits_BYTE BITS_BYTE = True"
| "is_bits_BYTE _ = False"
fun "is_bits_SHL" :: "bits_inst => bool" where
"is_bits_SHL BITS_SHL = True"
| "is_bits_SHL _ = False"
fun "is_bits_SHR" :: "bits_inst => bool" where
"is_bits_SHR BITS_SHR = True"
| "is_bits_SHR _ = False"
fun "is_bits_SAR" :: "bits_inst => bool" where
"is_bits_SAR BITS_SAR = True"
| "is_bits_SAR _ = False"


(* keccak256 *)
definition keccak256_codes  :: "nat set"  where "keccak256_codes = {0x20 :: nat}" 
declare keccak256_codes_def [simp add]
typedef keccak256_inst = "keccak256_codes" by auto
setup_lifting type_definition_keccak256_inst

lift_definition KECCAK256_KECCAK256 :: keccak256_inst is "0x20 :: nat" by auto

lift_definition KECCAK256_INST :: "keccak256_inst \<Rightarrow> inst" is id by auto

free_constructors cases_keccak256_inst for KECCAK256_KECCAK256
  by (transfer; auto)+

fun "is_keccak256_KECCAK256" :: "keccak256_inst => bool" where
"is_keccak256_KECCAK256 KECCAK256_KECCAK256 = True"


(* 
 * transaction-specific data instructions
 *)
definition tx_data_codes :: "nat set"
  where 
  "tx_data_codes = set (List.upt 0x30 0x40)"
declare tx_data_codes_def[simp add]
typedef tx_data_inst = tx_data_codes by auto
setup_lifting type_definition_tx_data_inst

lift_definition TX_DATA_ADDRESS        :: "tx_data_inst" is "0x30" by auto
lift_definition TX_DATA_BALANCE        :: "tx_data_inst" is "0x31" by auto
lift_definition TX_DATA_ORIGIN         :: "tx_data_inst" is "0x32" by auto
lift_definition TX_DATA_CALLER         :: "tx_data_inst" is "0x33" by auto
lift_definition TX_DATA_CALLVALUE      :: "tx_data_inst" is "0x34" by auto
lift_definition TX_DATA_CALLDATALOAD   :: "tx_data_inst" is "0x35" by auto
lift_definition TX_DATA_CALLDATASIZE   :: "tx_data_inst" is "0x36" by auto
lift_definition TX_DATA_CALLDATACOPY   :: "tx_data_inst" is "0x37" by auto
lift_definition TX_DATA_CODESIZE       :: "tx_data_inst" is "0x38" by auto
lift_definition TX_DATA_CODECOPY       :: "tx_data_inst" is "0x39" by auto
lift_definition TX_DATA_GASPRICE       :: "tx_data_inst" is "0x3a" by auto
lift_definition TX_DATA_EXTCODESIZE    :: "tx_data_inst" is "0x3b" by auto
lift_definition TX_DATA_EXTCODECOPY    :: "tx_data_inst" is "0x3c" by auto
lift_definition TX_DATA_RETURNDATASIZE :: "tx_data_inst" is "0x3d" by auto
lift_definition TX_DATA_RETURNDATACOPY :: "tx_data_inst" is "0x3e" by auto
lift_definition TX_DATA_EXTCODEHASH    :: "tx_data_inst" is "0x3f" by auto

lift_definition TX_DATA_INST :: "tx_data_inst \<Rightarrow> inst" is id by auto

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
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
definition chain_data_codes :: "nat set"
  where
  "chain_data_codes = set (List.upt 0x40 0x47)"
declare chain_data_codes_def[simp add]
typedef chain_data_inst = chain_data_codes by auto
setup_lifting type_definition_chain_data_inst

lift_definition CHAIN_DATA_BLOCKHASH   :: "chain_data_inst" is "0x40" by auto
lift_definition CHAIN_DATA_COINBASE    :: "chain_data_inst" is "0x41" by auto
lift_definition CHAIN_DATA_TIMESTAMP   :: "chain_data_inst" is "0x42" by auto
lift_definition CHAIN_DATA_NUMBER      :: "chain_data_inst" is "0x43" by auto
lift_definition CHAIN_DATA_DIFFICULTY  :: "chain_data_inst" is "0x44" by auto
lift_definition CHAIN_DATA_CHAINID     :: "chain_data_inst" is "0x45" by auto
lift_definition CHAIN_DATA_SELFBALANCE :: "chain_data_inst" is "0x46" by auto

lift_definition CHAIN_DATA_INST :: "chain_data_inst \<Rightarrow> inst" is id by auto

free_constructors cases_chain_data_inst for
CHAIN_DATA_BLOCKHASH
| CHAIN_DATA_COINBASE
| CHAIN_DATA_TIMESTAMP
| CHAIN_DATA_NUMBER
| CHAIN_DATA_DIFFICULTY
| CHAIN_DATA_CHAINID
| CHAIN_DATA_SELFBALANCE
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
definition state_control_codes :: "nat set" where
"state_control_codes = set (List.upt 0x50 0x5c)"
declare state_control_codes_def[simp add]
typedef state_control_inst = state_control_codes by auto
setup_lifting type_definition_state_control_inst

lift_definition STATE_CONTROL_POP      :: "state_control_inst" is "0x50" by auto
lift_definition STATE_CONTROL_MLOAD    :: "state_control_inst" is "0x51" by auto
lift_definition STATE_CONTROL_MSTORE   :: "state_control_inst" is "0x52" by auto
lift_definition STATE_CONTROL_MSTORE8  :: "state_control_inst" is "0x53" by auto
lift_definition STATE_CONTROL_SLOAD    :: "state_control_inst" is "0x54" by auto
lift_definition STATE_CONTROL_SSTORE   :: "state_control_inst" is "0x55" by auto
lift_definition STATE_CONTROL_JUMP     :: "state_control_inst" is "0x56" by auto
lift_definition STATE_CONTROL_JUMPI    :: "state_control_inst" is "0x57" by auto
lift_definition STATE_CONTROL_PC       :: "state_control_inst" is "0x58" by auto
lift_definition STATE_CONTROL_MSIZE    :: "state_control_inst" is "0x59" by auto
lift_definition STATE_CONTROL_GAS      :: "state_control_inst" is "0x5a" by auto
lift_definition STATE_CONTROL_JUMPDEST :: "state_control_inst" is "0x5b" by auto

lift_definition STATE_CONTROL_INST :: "state_control_inst => inst" is id by auto

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
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
definition push_codes :: "nat set" where
"push_codes = set (List.upt 0x60 0x80)"
declare push_codes_def[simp add]
typedef push_inst = push_codes by auto
setup_lifting type_definition_push_inst

(* we split push into two sub-groups to avoid having a 32-way free_constructors theorem *)
(* push few = (1-16) *)
definition push_few_codes :: "nat set" where
"push_few_codes = set (List.upt 0x60 0x70)"
declare push_few_codes_def[simp add]
typedef push_few_inst = push_few_codes by auto
setup_lifting type_definition_push_few_inst

lift_definition PUSH_FEW_PUSH1  :: "push_few_inst" is "0x60" by auto
lift_definition PUSH_FEW_PUSH2  :: "push_few_inst" is "0x61" by auto
lift_definition PUSH_FEW_PUSH3  :: "push_few_inst" is "0x62" by auto
lift_definition PUSH_FEW_PUSH4  :: "push_few_inst" is "0x63" by auto
lift_definition PUSH_FEW_PUSH5  :: "push_few_inst" is "0x64" by auto
lift_definition PUSH_FEW_PUSH6  :: "push_few_inst" is "0x65" by auto
lift_definition PUSH_FEW_PUSH7  :: "push_few_inst" is "0x66" by auto
lift_definition PUSH_FEW_PUSH8  :: "push_few_inst" is "0x67" by auto
lift_definition PUSH_FEW_PUSH9  :: "push_few_inst" is "0x68" by auto
lift_definition PUSH_FEW_PUSH10 :: "push_few_inst" is "0x69" by auto
lift_definition PUSH_FEW_PUSH11 :: "push_few_inst" is "0x6a" by auto
lift_definition PUSH_FEW_PUSH12 :: "push_few_inst" is "0x6b" by auto
lift_definition PUSH_FEW_PUSH13 :: "push_few_inst" is "0x6c" by auto
lift_definition PUSH_FEW_PUSH14 :: "push_few_inst" is "0x6d" by auto
lift_definition PUSH_FEW_PUSH15 :: "push_few_inst" is "0x6e" by auto
lift_definition PUSH_FEW_PUSH16 :: "push_few_inst" is "0x6f" by auto

lift_definition PUSH_FEW_INST :: "push_few_inst => inst" is id by auto

free_constructors cases_push_few_inst for
PUSH_FEW_PUSH1
| PUSH_FEW_PUSH2
| PUSH_FEW_PUSH3
| PUSH_FEW_PUSH4
| PUSH_FEW_PUSH5
| PUSH_FEW_PUSH6
| PUSH_FEW_PUSH7
| PUSH_FEW_PUSH8
| PUSH_FEW_PUSH9
| PUSH_FEW_PUSH10
| PUSH_FEW_PUSH11
| PUSH_FEW_PUSH12
| PUSH_FEW_PUSH13
| PUSH_FEW_PUSH14
| PUSH_FEW_PUSH15
| PUSH_FEW_PUSH16
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_push_few_PUSH1" :: "push_few_inst => bool" where
"is_push_few_PUSH1 PUSH_FEW_PUSH1 = True"
| "is_push_few_PUSH1 _ = False"
fun "is_push_few_PUSH2" :: "push_few_inst => bool" where
"is_push_few_PUSH2 PUSH_FEW_PUSH2 = True"
| "is_push_few_PUSH2 _ = False"
fun "is_push_few_PUSH3" :: "push_few_inst => bool" where
"is_push_few_PUSH3 PUSH_FEW_PUSH3 = True"
| "is_push_few_PUSH3 _ = False"
fun "is_push_few_PUSH4" :: "push_few_inst => bool" where
"is_push_few_PUSH4 PUSH_FEW_PUSH4 = True"
| "is_push_few_PUSH4 _ = False"
fun "is_push_few_PUSH5" :: "push_few_inst => bool" where
"is_push_few_PUSH5 PUSH_FEW_PUSH5 = True"
| "is_push_few_PUSH5 _ = False"
fun "is_push_few_PUSH6" :: "push_few_inst => bool" where
"is_push_few_PUSH6 PUSH_FEW_PUSH6 = True"
| "is_push_few_PUSH6 _ = False"
fun "is_push_few_PUSH7" :: "push_few_inst => bool" where
"is_push_few_PUSH7 PUSH_FEW_PUSH7 = True"
| "is_push_few_PUSH7 _ = False"
fun "is_push_few_PUSH8" :: "push_few_inst => bool" where
"is_push_few_PUSH8 PUSH_FEW_PUSH8 = True"
| "is_push_few_PUSH8 _ = False"
fun "is_push_few_PUSH9" :: "push_few_inst => bool" where
"is_push_few_PUSH9 PUSH_FEW_PUSH9 = True"
| "is_push_few_PUSH9 _ = False"
fun "is_push_few_PUSH10" :: "push_few_inst => bool" where
"is_push_few_PUSH10 PUSH_FEW_PUSH10 = True"
| "is_push_few_PUSH10 _ = False"
fun "is_push_few_PUSH11" :: "push_few_inst => bool" where
"is_push_few_PUSH11 PUSH_FEW_PUSH11 = True"
| "is_push_few_PUSH11 _ = False"
fun "is_push_few_PUSH12" :: "push_few_inst => bool" where
"is_push_few_PUSH12 PUSH_FEW_PUSH12 = True"
| "is_push_few_PUSH12 _ = False"
fun "is_push_few_PUSH13" :: "push_few_inst => bool" where
"is_push_few_PUSH13 PUSH_FEW_PUSH13 = True"
| "is_push_few_PUSH13 _ = False"
fun "is_push_few_PUSH14" :: "push_few_inst => bool" where
"is_push_few_PUSH14 PUSH_FEW_PUSH14 = True"
| "is_push_few_PUSH14 _ = False"
fun "is_push_few_PUSH15" :: "push_few_inst => bool" where
"is_push_few_PUSH15 PUSH_FEW_PUSH15 = True"
| "is_push_few_PUSH15 _ = False"
fun "is_push_few_PUSH16" :: "push_few_inst => bool" where
"is_push_few_PUSH16 PUSH_FEW_PUSH16 = True"
| "is_push_few_PUSH16 _ = False"


(* "push many" = 17-32 *)
definition push_many_codes :: "nat set" where
"push_many_codes = set (List.upt 0x70 0x80)"
declare push_many_codes_def[simp add]
typedef push_many_inst = push_many_codes by auto
setup_lifting type_definition_push_many_inst

lift_definition PUSH_MANY_PUSH17 :: "push_many_inst" is "0x70" by auto
lift_definition PUSH_MANY_PUSH18 :: "push_many_inst" is "0x71" by auto
lift_definition PUSH_MANY_PUSH19 :: "push_many_inst" is "0x72" by auto
lift_definition PUSH_MANY_PUSH20 :: "push_many_inst" is "0x73" by auto
lift_definition PUSH_MANY_PUSH21 :: "push_many_inst" is "0x74" by auto
lift_definition PUSH_MANY_PUSH22 :: "push_many_inst" is "0x75" by auto
lift_definition PUSH_MANY_PUSH23 :: "push_many_inst" is "0x76" by auto
lift_definition PUSH_MANY_PUSH24 :: "push_many_inst" is "0x77" by auto
lift_definition PUSH_MANY_PUSH25 :: "push_many_inst" is "0x78" by auto
lift_definition PUSH_MANY_PUSH26 :: "push_many_inst" is "0x79" by auto
lift_definition PUSH_MANY_PUSH27 :: "push_many_inst" is "0x7a" by auto
lift_definition PUSH_MANY_PUSH28 :: "push_many_inst" is "0x7b" by auto
lift_definition PUSH_MANY_PUSH29 :: "push_many_inst" is "0x7c" by auto
lift_definition PUSH_MANY_PUSH30 :: "push_many_inst" is "0x7d" by auto
lift_definition PUSH_MANY_PUSH31 :: "push_many_inst" is "0x7e" by auto
lift_definition PUSH_MANY_PUSH32 :: "push_many_inst" is "0x7f" by auto

lift_definition PUSH_MANY_INST :: "push_many_inst => inst" is id by auto

free_constructors cases_push_many_inst for
PUSH_MANY_PUSH17
| PUSH_MANY_PUSH18
| PUSH_MANY_PUSH19
| PUSH_MANY_PUSH20
| PUSH_MANY_PUSH21
| PUSH_MANY_PUSH22
| PUSH_MANY_PUSH23
| PUSH_MANY_PUSH24
| PUSH_MANY_PUSH25
| PUSH_MANY_PUSH26
| PUSH_MANY_PUSH27
| PUSH_MANY_PUSH28
| PUSH_MANY_PUSH29
| PUSH_MANY_PUSH30
| PUSH_MANY_PUSH31
| PUSH_MANY_PUSH32
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_push_many_PUSH17" :: "push_many_inst => bool" where
"is_push_many_PUSH17 PUSH_MANY_PUSH17 = True"
| "is_push_many_PUSH17 _ = False"
fun "is_push_many_PUSH18" :: "push_many_inst => bool" where
"is_push_many_PUSH18 PUSH_MANY_PUSH18 = True"
| "is_push_many_PUSH18 _ = False"
fun "is_push_many_PUSH19" :: "push_many_inst => bool" where
"is_push_many_PUSH19 PUSH_MANY_PUSH19 = True"
| "is_push_many_PUSH19 _ = False"
fun "is_push_many_PUSH20" :: "push_many_inst => bool" where
"is_push_many_PUSH20 PUSH_MANY_PUSH20 = True"
| "is_push_many_PUSH20 _ = False"
fun "is_push_many_PUSH21" :: "push_many_inst => bool" where
"is_push_many_PUSH21 PUSH_MANY_PUSH21 = True"
| "is_push_many_PUSH21 _ = False"
fun "is_push_many_PUSH22" :: "push_many_inst => bool" where
"is_push_many_PUSH22 PUSH_MANY_PUSH22 = True"
| "is_push_many_PUSH22 _ = False"
fun "is_push_many_PUSH23" :: "push_many_inst => bool" where
"is_push_many_PUSH23 PUSH_MANY_PUSH23 = True"
| "is_push_many_PUSH23 _ = False"
fun "is_push_many_PUSH24" :: "push_many_inst => bool" where
"is_push_many_PUSH24 PUSH_MANY_PUSH24 = True"
| "is_push_many_PUSH24 _ = False"
fun "is_push_many_PUSH25" :: "push_many_inst => bool" where
"is_push_many_PUSH25 PUSH_MANY_PUSH25 = True"
| "is_push_many_PUSH25 _ = False"
fun "is_push_many_PUSH26" :: "push_many_inst => bool" where
"is_push_many_PUSH26 PUSH_MANY_PUSH26 = True"
| "is_push_many_PUSH26 _ = False"
fun "is_push_many_PUSH27" :: "push_many_inst => bool" where
"is_push_many_PUSH27 PUSH_MANY_PUSH27 = True"
| "is_push_many_PUSH27 _ = False"
fun "is_push_many_PUSH28" :: "push_many_inst => bool" where
"is_push_many_PUSH28 PUSH_MANY_PUSH28 = True"
| "is_push_many_PUSH28 _ = False"
fun "is_push_many_PUSH29" :: "push_many_inst => bool" where
"is_push_many_PUSH29 PUSH_MANY_PUSH29 = True"
| "is_push_many_PUSH29 _ = False"
fun "is_push_many_PUSH30" :: "push_many_inst => bool" where
"is_push_many_PUSH30 PUSH_MANY_PUSH30 = True"
| "is_push_many_PUSH30 _ = False"
fun "is_push_many_PUSH31" :: "push_many_inst => bool" where
"is_push_many_PUSH31 PUSH_MANY_PUSH31 = True"
| "is_push_many_PUSH31 _ = False"
fun "is_push_many_PUSH32" :: "push_many_inst => bool" where
"is_push_many_PUSH32 PUSH_MANY_PUSH32 = True"
| "is_push_many_PUSH32 _ = False"


(* putting together the pieces *)
lift_definition PUSH_FEW :: "push_few_inst \<Rightarrow> push_inst" is id by auto
lift_definition PUSH_MANY :: "push_many_inst \<Rightarrow> push_inst" is id by auto

free_constructors cases_push_inst for
PUSH_FEW
| PUSH_MANY
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

(* general version for use when not case-splitting.
   we could have one of these each for PUSH_MANY and PUSH_FEW, but because that is an
   artificial distinction anyway there doesn't seem to be much point *)
fun push_gen :: "nat \<Rightarrow> nat" where
"push_gen n =
  0x60 + (n mod 32)"

lift_definition PUSH_GEN :: "nat \<Rightarrow> push_inst" is push_gen
proof-
  fix n :: nat

  have "n mod 32 < 32" using pos_mod_bound[of 32 n] by auto

  hence Upt32: "n mod 32 \<in> set (List.upt 0 32)" by auto

  hence "(0x60 + (n mod 32)) \<in> ((\<lambda> x . x + 0x60) ` set (List.upt 0 32))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x60)"] by auto

  hence Mapped : "(0x60 + (n mod 32)) \<in> set (map (\<lambda> x . x + 0x60) (List.upt 0 32))"
    by auto

  then show "push_gen n \<in> push_codes"
    using List.map_add_upt by auto
qed

(* dup instructions *)
definition dup_codes :: "nat set" where
"dup_codes = set (List.upt 0x80 0x90)"
declare dup_codes_def[simp add]
typedef dup_inst = dup_codes by auto
setup_lifting type_definition_dup_inst

lift_definition DUP_DUP1  :: "dup_inst" is "0x80" by auto
lift_definition DUP_DUP2  :: "dup_inst" is "0x81" by auto
lift_definition DUP_DUP3  :: "dup_inst" is "0x82" by auto 
lift_definition DUP_DUP4  :: "dup_inst" is "0x83" by auto
lift_definition DUP_DUP5  :: "dup_inst" is "0x84" by auto
lift_definition DUP_DUP6  :: "dup_inst" is "0x85" by auto
lift_definition DUP_DUP7  :: "dup_inst" is "0x86" by auto
lift_definition DUP_DUP8  :: "dup_inst" is "0x87" by auto
lift_definition DUP_DUP9  :: "dup_inst" is "0x88" by auto
lift_definition DUP_DUP10 :: "dup_inst" is "0x89" by auto
lift_definition DUP_DUP11 :: "dup_inst" is "0x8a" by auto
lift_definition DUP_DUP12 :: "dup_inst" is "0x8b" by auto
lift_definition DUP_DUP13 :: "dup_inst" is "0x8c" by auto
lift_definition DUP_DUP14 :: "dup_inst" is "0x8d" by auto
lift_definition DUP_DUP15 :: "dup_inst" is "0x8e" by auto
lift_definition DUP_DUP16 :: "dup_inst" is "0x8f" by auto

lift_definition DUP_INST :: "dup_inst => inst" is id by auto

free_constructors cases_dup_inst for
DUP_DUP1
| DUP_DUP2
| DUP_DUP3
| DUP_DUP4
| DUP_DUP5
| DUP_DUP6
| DUP_DUP7
| DUP_DUP8
| DUP_DUP9
| DUP_DUP10
| DUP_DUP11
| DUP_DUP12
| DUP_DUP13
| DUP_DUP14
| DUP_DUP15
| DUP_DUP16
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_dup_DUP1" :: "dup_inst => bool" where
"is_dup_DUP1 DUP_DUP1 = True"
| "is_dup_DUP1 _ = False"
fun "is_dup_DUP2" :: "dup_inst => bool" where
"is_dup_DUP2 DUP_DUP2 = True"
| "is_dup_DUP2 _ = False"
fun "is_dup_DUP3" :: "dup_inst => bool" where
"is_dup_DUP3 DUP_DUP3 = True"
| "is_dup_DUP3 _ = False"
fun "is_dup_DUP4" :: "dup_inst => bool" where
"is_dup_DUP4 DUP_DUP4 = True"
| "is_dup_DUP4 _ = False"
fun "is_dup_DUP5" :: "dup_inst => bool" where
"is_dup_DUP5 DUP_DUP5 = True"
| "is_dup_DUP5 _ = False"
fun "is_dup_DUP6" :: "dup_inst => bool" where
"is_dup_DUP6 DUP_DUP6 = True"
| "is_dup_DUP6 _ = False"
fun "is_dup_DUP7" :: "dup_inst => bool" where
"is_dup_DUP7 DUP_DUP7 = True"
| "is_dup_DUP7 _ = False"
fun "is_dup_DUP8" :: "dup_inst => bool" where
"is_dup_DUP8 DUP_DUP8 = True"
| "is_dup_DUP8 _ = False"
fun "is_dup_DUP9" :: "dup_inst => bool" where
"is_dup_DUP9 DUP_DUP9 = True"
| "is_dup_DUP9 _ = False"
fun "is_dup_DUP10" :: "dup_inst => bool" where
"is_dup_DUP10 DUP_DUP10 = True"
| "is_dup_DUP10 _ = False"
fun "is_dup_DUP11" :: "dup_inst => bool" where
"is_dup_DUP11 DUP_DUP11 = True"
| "is_dup_DUP11 _ = False"
fun "is_dup_DUP12" :: "dup_inst => bool" where
"is_dup_DUP12 DUP_DUP12 = True"
| "is_dup_DUP12 _ = False"
fun "is_dup_DUP13" :: "dup_inst => bool" where
"is_dup_DUP13 DUP_DUP13 = True"
| "is_dup_DUP13 _ = False"
fun "is_dup_DUP14" :: "dup_inst => bool" where
"is_dup_DUP14 DUP_DUP14 = True"
| "is_dup_DUP14 _ = False"
fun "is_dup_DUP15" :: "dup_inst => bool" where
"is_dup_DUP15 DUP_DUP15 = True"
| "is_dup_DUP15 _ = False"
fun "is_dup_DUP16" :: "dup_inst => bool" where
"is_dup_DUP16 DUP_DUP16 = True"
| "is_dup_DUP16 _ = False"

(* general version for use when not case-splitting *)
fun dup_gen :: "nat \<Rightarrow> nat" where
"dup_gen n =
  0x80 + (n mod 16)"

lift_definition DUP_GEN :: "nat \<Rightarrow> dup_inst" is dup_gen
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x80 + (n mod 16)) \<in> ((\<lambda> x . x + 0x80) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x80)"] by auto

  hence Mapped : "(0x80 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x80) (List.upt 0 16))"
    by auto

  then show "dup_gen n \<in> dup_codes"
    using List.map_add_upt by auto
qed

(* 
 * swap instructions 
 *)
definition swap_codes :: "nat set" where
"swap_codes = set (List.upt 0x90 0xa0)"
declare swap_codes_def[simp add]
typedef swap_inst = swap_codes by auto
setup_lifting type_definition_swap_inst

lift_definition SWAP_SWAP1  :: "swap_inst" is "0x90" by auto
lift_definition SWAP_SWAP2  :: "swap_inst" is "0x91" by auto
lift_definition SWAP_SWAP3  :: "swap_inst" is "0x92" by auto 
lift_definition SWAP_SWAP4  :: "swap_inst" is "0x93" by auto
lift_definition SWAP_SWAP5  :: "swap_inst" is "0x94" by auto
lift_definition SWAP_SWAP6  :: "swap_inst" is "0x95" by auto
lift_definition SWAP_SWAP7  :: "swap_inst" is "0x96" by auto
lift_definition SWAP_SWAP8  :: "swap_inst" is "0x97" by auto
lift_definition SWAP_SWAP9  :: "swap_inst" is "0x98" by auto
lift_definition SWAP_SWAP10 :: "swap_inst" is "0x99" by auto
lift_definition SWAP_SWAP11 :: "swap_inst" is "0x9a" by auto
lift_definition SWAP_SWAP12 :: "swap_inst" is "0x9b" by auto
lift_definition SWAP_SWAP13 :: "swap_inst" is "0x9c" by auto
lift_definition SWAP_SWAP14 :: "swap_inst" is "0x9d" by auto
lift_definition SWAP_SWAP15 :: "swap_inst" is "0x9e" by auto
lift_definition SWAP_SWAP16 :: "swap_inst" is "0x9f" by auto

lift_definition SWAP_INST :: "swap_inst => inst" is id by auto

free_constructors cases_swap_inst for
SWAP_SWAP1
| SWAP_SWAP2
| SWAP_SWAP3
| SWAP_SWAP4
| SWAP_SWAP5
| SWAP_SWAP6
| SWAP_SWAP7
| SWAP_SWAP8
| SWAP_SWAP9
| SWAP_SWAP10
| SWAP_SWAP11
| SWAP_SWAP12
| SWAP_SWAP13
| SWAP_SWAP14
| SWAP_SWAP15
| SWAP_SWAP16
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

fun "is_swap_SWAP1" :: "swap_inst => bool" where
"is_swap_SWAP1 SWAP_SWAP1 = True"
| "is_swap_SWAP1 _ = False"
fun "is_swap_SWAP2" :: "swap_inst => bool" where
"is_swap_SWAP2 SWAP_SWAP2 = True"
| "is_swap_SWAP2 _ = False"
fun "is_swap_SWAP3" :: "swap_inst => bool" where
"is_swap_SWAP3 SWAP_SWAP3 = True"
| "is_swap_SWAP3 _ = False"
fun "is_swap_SWAP4" :: "swap_inst => bool" where
"is_swap_SWAP4 SWAP_SWAP4 = True"
| "is_swap_SWAP4 _ = False"
fun "is_swap_SWAP5" :: "swap_inst => bool" where
"is_swap_SWAP5 SWAP_SWAP5 = True"
| "is_swap_SWAP5 _ = False"
fun "is_swap_SWAP6" :: "swap_inst => bool" where
"is_swap_SWAP6 SWAP_SWAP6 = True"
| "is_swap_SWAP6 _ = False"
fun "is_swap_SWAP7" :: "swap_inst => bool" where
"is_swap_SWAP7 SWAP_SWAP7 = True"
| "is_swap_SWAP7 _ = False"
fun "is_swap_SWAP8" :: "swap_inst => bool" where
"is_swap_SWAP8 SWAP_SWAP8 = True"
| "is_swap_SWAP8 _ = False"
fun "is_swap_SWAP9" :: "swap_inst => bool" where
"is_swap_SWAP9 SWAP_SWAP9 = True"
| "is_swap_SWAP9 _ = False"
fun "is_swap_SWAP10" :: "swap_inst => bool" where
"is_swap_SWAP10 SWAP_SWAP10 = True"
| "is_swap_SWAP10 _ = False"
fun "is_swap_SWAP11" :: "swap_inst => bool" where
"is_swap_SWAP11 SWAP_SWAP11 = True"
| "is_swap_SWAP11 _ = False"
fun "is_swap_SWAP12" :: "swap_inst => bool" where
"is_swap_SWAP12 SWAP_SWAP12 = True"
| "is_swap_SWAP12 _ = False"
fun "is_swap_SWAP13" :: "swap_inst => bool" where
"is_swap_SWAP13 SWAP_SWAP13 = True"
| "is_swap_SWAP13 _ = False"
fun "is_swap_SWAP14" :: "swap_inst => bool" where
"is_swap_SWAP14 SWAP_SWAP14 = True"
| "is_swap_SWAP14 _ = False"
fun "is_swap_SWAP15" :: "swap_inst => bool" where
"is_swap_SWAP15 SWAP_SWAP15 = True"
| "is_swap_SWAP15 _ = False"
fun "is_swap_SWAP16" :: "swap_inst => bool" where
"is_swap_SWAP16 SWAP_SWAP16 = True"
| "is_swap_SWAP16 _ = False"

(* general version for use when not case-splitting *)
fun swap_gen :: "nat \<Rightarrow> nat" where
"swap_gen n =
  0x90 + (n mod 16)"

lift_definition SWAP_GEN :: "nat \<Rightarrow> swap_inst" is swap_gen
proof-
  fix n :: nat

  have "n mod 16 < 16" using pos_mod_bound[of 16 n] by auto

  hence Upt32: "n mod 16 \<in> set (List.upt 0 16)" by auto

  hence "(0x90 + (n mod 16)) \<in> ((\<lambda> x . x + 0x90) ` set (List.upt 0 16))"
    using Set.imageI[OF Upt32, of "(\<lambda> x . x + 0x90)"] by auto

  hence Mapped : "(0x90 + (n mod 16)) \<in> set (map (\<lambda> x . x + 0x90) (List.upt 0 16))"
    by auto

  then show "swap_gen n \<in> swap_codes"
    using List.map_add_upt by auto
qed


(* 
 * log instructions 
 *)
definition log_codes where
"log_codes = set (List.upt 0xa0 0xa5)"
declare log_codes_def[simp]
typedef log_inst = log_codes by auto
setup_lifting type_definition_log_inst

lift_definition LOG_LOG0 :: "log_inst" is "0xa0" by auto
lift_definition LOG_LOG1 :: "log_inst" is "0xa1" by auto
lift_definition LOG_LOG2 :: "log_inst" is "0xa2" by auto
lift_definition LOG_LOG3 :: "log_inst" is "0xa3" by auto
lift_definition LOG_LOG4 :: "log_inst" is "0xa4" by auto

lift_definition LOG_INST :: "log_inst => inst" is id by auto

free_constructors cases_log_inst for
LOG_LOG0
| LOG_LOG1
| LOG_LOG2
| LOG_LOG3
| LOG_LOG4
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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

(* EIP615 instructions *)
definition eip615_codes where
"eip615_codes = set (List.upt 0xb0 0xba)"
declare eip615_codes_def[simp]
typedef eip615_inst = eip615_codes by auto
setup_lifting type_definition_eip615_inst

lift_definition EIP615_JUMPTO    :: "eip615_inst" is "0xb0" by auto
lift_definition EIP615_JUMPIF    :: "eip615_inst" is "0xb1" by auto
lift_definition EIP615_JUMPV     :: "eip615_inst" is "0xb2" by auto
lift_definition EIP615_JUMPSUB   :: "eip615_inst" is "0xb3" by auto
lift_definition EIP615_JUMPSUBV  :: "eip615_inst" is "0xb4" by auto
lift_definition EIP615_BEGINSUB  :: "eip615_inst" is "0xb5" by auto
lift_definition EIP615_BEGINDATA :: "eip615_inst" is "0xb6" by auto
lift_definition EIP615_RETURNSUB :: "eip615_inst" is "0xb7" by auto
lift_definition EIP615_PUTLOCAL  :: "eip615_inst" is "0xb8" by auto
lift_definition EIP615_GETLOCAL  :: "eip615_inst" is "0xb9" by auto

lift_definition EIP615_INST :: "eip615_inst => inst" is id by auto

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
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
"comms_codes = set (List.upt 0xf0 0xf6) \<union> {0xfa}"
declare comms_codes_def[simp]
typedef comms_inst = comms_codes by auto
setup_lifting type_definition_comms_inst

lift_definition COMMS_CREATE       :: "comms_inst" is "0xf0" by auto
lift_definition COMMS_CALL         :: "comms_inst" is "0xf1" by auto
lift_definition COMMS_CALLCODE     :: "comms_inst" is "0xf2" by auto
lift_definition COMMS_RETURN       :: "comms_inst" is "0xf3" by auto
lift_definition COMMS_DELEGATECALL :: "comms_inst" is "0xf4" by auto
lift_definition COMMS_CREATE2      :: "comms_inst" is "0xf5" by auto
lift_definition COMMS_STATICCALL   :: "comms_inst" is "0xfa" by auto

lift_definition COMMS_INST :: "comms_inst => inst" is id by auto

free_constructors cases_comms_inst for
COMMS_CREATE
| COMMS_CALL
| COMMS_CALLCODE
| COMMS_RETURN
| COMMS_DELEGATECALL
| COMMS_CREATE2
| COMMS_STATICCALL
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
"special_halt_codes = set (List.upt 0xfd 0x100)"
declare special_halt_codes_def[simp]
typedef special_halt_inst = special_halt_codes by auto
setup_lifting type_definition_special_halt_inst

lift_definition SPECIAL_HALT_REVERT       :: "special_halt_inst" is "0xfd" by auto
lift_definition SPECIAL_HALT_INVALID      :: "special_halt_inst" is "0xfe" by auto
lift_definition SPECIAL_HALT_SELFDESTRUCT :: "special_halt_inst" is "0xff" by auto

lift_definition SPECIAL_HALT_INST :: "special_halt_inst => inst" is id by auto

free_constructors cases_special_halt_inst for
SPECIAL_HALT_REVERT
| SPECIAL_HALT_INVALID
| SPECIAL_HALT_SELFDESTRUCT
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
definition good_codes :: "nat set" where
"good_codes = 
  stop_codes \<union>
  arith_codes \<union>
  compare_codes \<union>
  bits_codes \<union>
  keccak256_codes \<union>
  tx_data_codes \<union>
  chain_data_codes \<union>
  state_control_codes \<union>
  push_few_codes \<union>
  push_many_codes \<union>
  dup_codes \<union>
  swap_codes \<union>
  log_codes \<union>
  comms_codes \<union>
  special_halt_codes"

typedef good_inst = good_codes
  by(auto simp add: good_codes_def)
setup_lifting type_definition_good_inst

lift_definition GOOD_INST :: "good_inst \<Rightarrow> inst" is id
  by(auto simp add: good_codes_def)

definition bad_codes :: "nat set" where
"bad_codes = 
  {x . x < 256} - good_codes"

(* TODO: this will have to change if this constant becomes used as an opcode in the future *)
definition bad_code :: "nat" where
"bad_code = 0xcc"

typedef bad_inst = bad_codes
proof-
  have "bad_code \<in> bad_codes" 
    unfolding good_codes_def bad_codes_def bad_code_def
    by(auto)
  thus "\<exists>x. x \<in> bad_codes" by auto
qed
setup_lifting type_definition_bad_inst

lift_definition BAD_INST :: "bad_inst \<Rightarrow> inst" is id by(auto simp add: bad_codes_def)

lemma good_are_insts : "good_codes \<subseteq> {x . x < 256}"
  by(auto simp add: good_codes_def)

lemma good_bad : "good_codes \<union> bad_codes = {x . x < 256}"
  using good_are_insts unfolding bad_codes_def
  by blast

lemma cases_inst_helper :
"\<And>P y. y < 256 \<Longrightarrow>
           (\<And>x1. x1 \<in> stop_codes \<Longrightarrow> y = id x1 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x2. x2 \<in> arith_codes \<Longrightarrow> y = id x2 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x3. x3 \<in> compare_codes \<Longrightarrow> y = id x3 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x4. x4 \<in> bits_codes \<Longrightarrow> y = id x4 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x5. x5 \<in> keccak256_codes \<Longrightarrow> y = id x5 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x6. x6 \<in> tx_data_codes \<Longrightarrow> y = id x6 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x7. x7 \<in> chain_data_codes \<Longrightarrow> y = id x7 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x8. x8 \<in> state_control_codes \<Longrightarrow> y = id x8 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x9. x9 \<in> push_few_codes \<Longrightarrow> y = id x9 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x10. x10 \<in> push_many_codes \<Longrightarrow> y = id x10 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x11. x11 \<in> dup_codes \<Longrightarrow> y = id x11 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x12. x12 \<in> swap_codes \<Longrightarrow> y = id x12 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x13. x13 \<in> log_codes \<Longrightarrow> y = id x13 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x14. x14 \<in> eip615_codes \<Longrightarrow> y = id x14 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x15. x15 \<in> comms_codes \<Longrightarrow> y = id x15 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x16. x16 \<in> special_halt_codes \<Longrightarrow> y = id x16 \<Longrightarrow> P) \<Longrightarrow>
           (\<And>x17. x17 \<in> bad_codes \<Longrightarrow> y = id x17 \<Longrightarrow> P) \<Longrightarrow> P"
  sorry


(* "constructors" for each instruction type *)
free_constructors cases_inst for
STOP_INST
| ARITH_INST
| COMPARE_INST
| BITS_INST
| KECCAK256_INST
| TX_DATA_INST
| CHAIN_DATA_INST
| STATE_CONTROL_INST
| PUSH_FEW_INST
| PUSH_MANY_INST
| DUP_INST
| SWAP_INST
| LOG_INST
| EIP615_INST
| COMMS_INST
| SPECIAL_HALT_INST
| BAD_INST

(*
                      apply(transfer)
  apply(rule cases_inst_helper; blast)

  apply(transfer; force  simp only: bad_codes_def good_codes_def
List.upt_def
stop_codes_def arith_codes_def compare_codes_def bits_codes_def keccak256_codes_def
tx_data_codes_def chain_data_codes_def state_control_codes_def
push_few_codes_def push_many_codes_def dup_codes_def
swap_codes_def log_codes_def eip615_codes_def comms_codes_def
special_halt_codes_def 
)+

  apply(transfer; simp only: bad_codes_def good_codes_def
List.upt_def
stop_codes_def arith_codes_def compare_codes_def bits_codes_def keccak256_codes_def
tx_data_codes_def chain_data_codes_def state_control_codes_def
push_few_codes_def push_many_codes_def dup_codes_def
swap_codes_def log_codes_def eip615_codes_def comms_codes_def
special_halt_codes_def Nat.nat.rec; force)+
(*
                      apply(transfer;
  fastforce simp add: bad_codes_def good_codes_def
List.upt_def simp del: set_upt; fail)+
*)
(*
                      apply(match premises in I : "\<And> P y . y < 256"  \<Rightarrow>
\<open>simp only: stop_codes_def\<close>)
*)

(*
(rule cases_inst_helper; blast)[1])
*)
(*
  apply( auto simp del:set_upt simp add:List.upt_def)+
                      defer
               apply(transfer; force)+
  *)
*)


end
