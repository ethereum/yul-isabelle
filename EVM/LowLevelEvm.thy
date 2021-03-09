theory LowLevelEvm imports Main "HOL-Library.Numeral_Type" 
MiniEvm 
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
definition stop_codes  :: "nat list"  where "stop_codes = [0 :: nat]" 
declare stop_codes_def [simp add]
typedef stop_inst = "set stop_codes" by auto
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
definition arith_codes :: "nat list" where 
"arith_codes = (List.upt 0x01 0x0c)"

declare arith_codes_def [simp add]
typedef arith_inst = "set arith_codes" by auto
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
 * Bits + Comparisons
 *)
definition bits_compare_codes :: "nat list" where 
  "bits_compare_codes = (List.upt 0x10 0x1e)"
declare bits_compare_codes_def [simp add]
typedef bits_compare_inst = "set bits_compare_codes" by auto
setup_lifting type_definition_bits_compare_inst

lift_definition BITS_COMPARE_LT     :: "bits_compare_inst" is "0x10" by auto
lift_definition BITS_COMPARE_GT     :: "bits_compare_inst" is "0x11" by auto
lift_definition BITS_COMPARE_SLT    :: "bits_compare_inst" is "0x12" by auto
lift_definition BITS_COMPARE_SGT    :: "bits_compare_inst" is "0x13" by auto
lift_definition BITS_COMPARE_EQ     :: "bits_compare_inst" is "0x14" by auto
lift_definition BITS_COMPARE_ISZERO :: "bits_compare_inst" is "0x15" by auto
lift_definition BITS_COMPARE_AND    :: "bits_compare_inst" is "0x16" by auto
lift_definition BITS_COMPARE_OR     :: "bits_compare_inst" is "0x17" by auto
lift_definition BITS_COMPARE_XOR    :: "bits_compare_inst" is "0x18" by auto
lift_definition BITS_COMPARE_NOT    :: "bits_compare_inst" is "0x19" by auto
lift_definition BITS_COMPARE_BYTE   :: "bits_compare_inst" is "0x1a" by auto
lift_definition BITS_COMPARE_SHL    :: "bits_compare_inst" is "0x1b" by auto
lift_definition BITS_COMPARE_SHR    :: "bits_compare_inst" is "0x1c" by auto
lift_definition BITS_COMPARE_SAR    :: "bits_compare_inst" is "0x1d" by auto


lift_definition BITS_COMPARE_INST :: "bits_compare_inst \<Rightarrow> inst" is id by auto

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
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
definition keccak256_codes  :: "nat list"  where "keccak256_codes = [0x20 :: nat]" 
declare keccak256_codes_def [simp add]
typedef keccak256_inst = "set keccak256_codes" by auto
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
definition tx_data_codes :: "nat list"
  where 
  "tx_data_codes = (List.upt 0x30 0x40)"
declare tx_data_codes_def[simp add]
typedef tx_data_inst = "set tx_data_codes" by auto
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
definition chain_data_codes :: "nat list"
  where
  "chain_data_codes = List.upt 0x40 0x48"
declare chain_data_codes_def[simp add]
typedef chain_data_inst = "set chain_data_codes" by auto
setup_lifting type_definition_chain_data_inst

lift_definition CHAIN_DATA_BLOCKHASH   :: "chain_data_inst" is "0x40" by auto
lift_definition CHAIN_DATA_COINBASE    :: "chain_data_inst" is "0x41" by auto
lift_definition CHAIN_DATA_TIMESTAMP   :: "chain_data_inst" is "0x42" by auto
lift_definition CHAIN_DATA_NUMBER      :: "chain_data_inst" is "0x43" by auto
lift_definition CHAIN_DATA_DIFFICULTY  :: "chain_data_inst" is "0x44" by auto
lift_definition CHAIN_DATA_GASLIMIT    :: "chain_data_inst" is "0x45" by auto
lift_definition CHAIN_DATA_CHAINID     :: "chain_data_inst" is "0x46" by auto
lift_definition CHAIN_DATA_SELFBALANCE :: "chain_data_inst" is "0x47" by auto

lift_definition CHAIN_DATA_INST :: "chain_data_inst \<Rightarrow> inst" is id by auto

free_constructors cases_chain_data_inst for
CHAIN_DATA_BLOCKHASH
| CHAIN_DATA_COINBASE
| CHAIN_DATA_TIMESTAMP
| CHAIN_DATA_NUMBER
| CHAIN_DATA_DIFFICULTY
| CHAIN_DATA_GASLIMIT
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
definition state_control_codes :: "nat list" where
"state_control_codes = (List.upt 0x50 0x5c)"
declare state_control_codes_def[simp add]
typedef state_control_inst = "set state_control_codes" by auto
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
definition push_codes :: "nat list" where
"push_codes = (List.upt 0x60 0x80)"
declare push_codes_def[simp add]
typedef push_inst = "set push_codes" by auto
setup_lifting type_definition_push_inst

lift_definition PUSH_INST :: "push_inst \<Rightarrow> inst" is id by auto

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

  then show "make_push n \<in> set push_codes"
    using List.map_add_upt by auto
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

  then show "make_push n \<in> set push_codes"
    using List.map_add_upt by auto
qed

free_constructors cases_push_inst for PUSH_PUSH
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+ 

fun is_PUSH_PUSH :: "push_inst \<Rightarrow> bool" where
"is_PUSH_PUSH (PUSH_PUSH _) = True"

fun get_PUSH_PUSH :: "push_inst \<Rightarrow> nat" where
"get_PUSH_PUSH (PUSH_PUSH x) = nat_of_nat32 x"

fun is_PUSH_PUSH_n :: "push_inst \<Rightarrow> nat \<Rightarrow> bool" where
"is_PUSH_PUSH_n i x = (get_PUSH_PUSH i = x)"

(* 
 * dup instructions 
 *)
definition dup_codes :: "nat list" where
"dup_codes = (List.upt 0x80 0x90)"
declare dup_codes_def[simp add]
typedef dup_inst = "set dup_codes" by auto
setup_lifting type_definition_dup_inst

typedef nat16 = "{x :: nat . x < 16}"
proof
  have "0 < (16 :: nat)" by auto
  thus "0 \<in> {x :: nat . x < 16}" by(auto)
qed
setup_lifting type_definition_nat16

lift_definition DUP_INST :: "dup_inst => inst" is id by auto

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

  then show "make_dup n \<in> set dup_codes"
    using List.map_add_upt by auto
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

  then show "make_dup n \<in> set dup_codes"
    using List.map_add_upt by auto
qed

free_constructors cases_dup_inst for DUP_DUP
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+ 

fun is_DUP_DUP :: "dup_inst \<Rightarrow> bool" where
"is_DUP_DUP (DUP_DUP _) = True"

fun get_DUP_DUP :: "dup_inst \<Rightarrow> nat" where
"get_DUP_DUP (DUP_DUP x) = nat_of_nat16 x"

fun is_DUP_DUP_n :: "dup_inst \<Rightarrow> nat \<Rightarrow> bool" where
"is_DUP_DUP_n i x = (get_DUP_DUP i = x)"

(* 
 * swap instructions 
 *)
definition swap_codes :: "nat list" where
"swap_codes = (List.upt 0x90 0xa0)"
declare swap_codes_def[simp add]
typedef swap_inst = "set swap_codes" by auto
setup_lifting type_definition_swap_inst

lift_definition SWAP_INST :: "swap_inst => inst" is id by auto

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

  then show "make_swap n \<in> set swap_codes"
    using List.map_add_upt by auto
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

  then show "make_swap n \<in> set swap_codes"
    using List.map_add_upt by auto
qed

free_constructors cases_swap_inst for SWAP_SWAP
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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
"log_codes = (List.upt 0xa0 0xa5)"
declare log_codes_def[simp]
typedef log_inst = "set log_codes" by auto
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

(* 
 * EIP615 instructions 
 *)
definition eip615_codes where
"eip615_codes = (List.upt 0xb0 0xba)"
declare eip615_codes_def[simp]
typedef eip615_inst = "set eip615_codes" by auto
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
"comms_codes = (List.upt 0xf0 0xf6) @ [0xfa]"
declare comms_codes_def[simp]
typedef comms_inst = "set comms_codes" by auto
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
"special_halt_codes = (List.upt 0xfd 0x100)"
declare special_halt_codes_def[simp]
typedef special_halt_inst = "set special_halt_codes" by auto
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
definition good_codes :: "nat list" where
"good_codes = 
  stop_codes @
  arith_codes @
  bits_compare_codes @
  keccak256_codes @
  tx_data_codes @
  chain_data_codes @
  state_control_codes @
  push_codes @
  dup_codes @
  swap_codes @
  log_codes @
  comms_codes @
  special_halt_codes"

typedef good_inst = "set good_codes"
  by(auto simp add: good_codes_def)
setup_lifting type_definition_good_inst

lift_definition GOOD_INST :: "good_inst \<Rightarrow> inst" is id
  by(auto simp add: good_codes_def)

(* "more computable" approach to set differencing -
still not fast enough*)

(*
fun list_diff :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"list_diff l [] = l"
| "list_diff l (x#xs) =
   list_diff (remove1 x l) xs"

lemma list_diff_set :
  assumes H : "distinct l1"
  shows "set (list_diff l1 l2) = set l1 - set l2" using assms
proof(induction l2 arbitrary: l1)
case Nil
  then show ?case by auto
next
  case (Cons a l2)
  then show ?case 
    by(auto)
qed
*)
(*
definition bad_codes :: "nat list" where
"bad_codes = 
  list_diff (List.upt 0 256) good_codes"

lemma bad_codes_spec :
  shows "set bad_codes = set (List.upt 0 (256 :: nat)) - set good_codes"
  unfolding bad_codes_def list_diff_set[OF distinct_upt]
  by auto
*)

(* TODO: doing this by hand was pretty painful.
   If we had a better data structure than lists readily available,
   we could probably compute this in a reasonable way *)
definition bad_codes :: "nat list" where
"bad_codes =
  [0x0c, 0x0d, 0x0e, 0x0f,
   0x1e, 0x1f,
   0x21, 0x22, 0x23, 0x24, 0x25, 0x26, 0x27, 0x28, 0x29, 0x2a, 0x2b, 0x2c, 0x2d, 0x2e, 0x2f,
   0x48, 0x49, 0x4a, 0x4b, 0x4c, 0x4d, 0x4e, 0x4f,
   0x5c, 0x5d, 0x5e, 0x5f,
   0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa, 0xab, 0xac, 0xad, 0xae, 0xaf,
   0xb0, 0xb1, 0xb2, 0xb3, 0xb4, 0xb5, 0xb6, 0xb7, 0xb8, 0xb9, 0xba, 0xbb, 0xbc, 0xbd, 0xbe, 0xbf,
   0xc0, 0xc1, 0xc2, 0xc3, 0xc4, 0xc5, 0xc6, 0xc7, 0xc8, 0xc9, 0xca, 0xcb, 0xcc, 0xcd, 0xce, 0xcf,
   0xd0, 0xd1, 0xd2, 0xd3, 0xd4, 0xd5, 0xd6, 0xd7, 0xd8, 0xd9, 0xda, 0xdb, 0xdc, 0xdd, 0xde, 0xdf,
   0xe0, 0xe1, 0xe2, 0xe3, 0xe4, 0xe5, 0xe6, 0xe7, 0xe8, 0xe9, 0xea, 0xeb, 0xec, 0xed, 0xee, 0xef,
   0xf6, 0xf7, 0xf8, 0xf9,
   0xfb, 0xfc]"

typedef bad_inst = "set bad_codes" by(auto simp add: bad_codes_def)
setup_lifting type_definition_bad_inst

lift_definition BAD_INST :: "bad_inst \<Rightarrow> inst" is id by(auto simp add: bad_codes_def)

lemma good_are_insts : "set good_codes \<subseteq> {x . x < 256}"
  by(auto simp add: good_codes_def)

(*
lemma good_bad : "set good_codes \<union> set bad_codes = {x . x < 256}"
  unfolding bad_codes_def good_codes_def
  apply(auto)
*)
  
lemma cases_inst_helper :
  assumes Hy :  "(y :: nat) < 256"
  assumes H1 :  "(\<And>x1. x1 \<in> set stop_codes \<Longrightarrow> y = id x1 \<Longrightarrow> P)"
  assumes H2 :  "(\<And>x2. x2 \<in> set arith_codes \<Longrightarrow> y = id x2 \<Longrightarrow> P)"
  assumes H4 :  "(\<And>x4. x4 \<in> set bits_compare_codes \<Longrightarrow> y = id x4 \<Longrightarrow> P)"
  assumes H5 :  "(\<And>x5. x5 \<in> set keccak256_codes \<Longrightarrow> y = id x5 \<Longrightarrow> P)"
  assumes H6 :  "(\<And>x6. x6 \<in> set tx_data_codes \<Longrightarrow> y = id x6 \<Longrightarrow> P)"
  assumes H7 :  "(\<And>x7. x7 \<in> set chain_data_codes \<Longrightarrow> y = id x7 \<Longrightarrow> P)"
  assumes H8 :  "(\<And>x8. x8 \<in> set state_control_codes \<Longrightarrow> y = id x8 \<Longrightarrow> P)"
  assumes H9 :  "(\<And>x9. x9 \<in> set push_codes \<Longrightarrow> y = id x9 \<Longrightarrow> P)"
  assumes H10 : "(\<And>x10. x10 \<in> set dup_codes \<Longrightarrow> y = id x10 \<Longrightarrow> P)"
  assumes H11 : "(\<And>x11. x11 \<in> set swap_codes \<Longrightarrow> y = id x11 \<Longrightarrow> P)"
  assumes H12 : "(\<And>x12. x12 \<in> set log_codes \<Longrightarrow> y = id x12 \<Longrightarrow> P)"
  assumes H13 : "(\<And>x13. x13 \<in> set comms_codes \<Longrightarrow> y = id x13 \<Longrightarrow> P)"
  assumes H14 : "(\<And>x14. x14 \<in> set special_halt_codes \<Longrightarrow> y = id x14 \<Longrightarrow> P)"
  assumes H15 : "(\<And>x15. x15 \<in> set bad_codes \<Longrightarrow> y = id x15 \<Longrightarrow> P)"
  shows P

  sorry
(*

(* "constructors" for each instruction type *)
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
  defer
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)

  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)  
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail)
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 

(* apply(rule cases_inst_helper; blast) *)


(*
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
  apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
apply(transfer; auto simp: bad_codes_def good_codes_def; fail) 
*)

(*
  by (transfer; auto simp: bad_codes_spec good_codes_def; fail)+
*)

(*
                      apply(transfer;
  match conclusion in "x = y" for x y \<Rightarrow> \<open>transfer; 
  fastforce simp add: bad_codes_def good_codes_def
List.upt_def simp del: set_upt\<close>
      | match conclusion in"x \<noteq> y" for x y \<Rightarrow>  \<open>transfer; 
  fastforce simp add: bad_codes_def good_codes_def
List.upt_def simp del: set_upt\<close>
      | rule cases_inst_helper; blast)
*)


                   


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
  