theory LowLevelEvm imports Main "HOL-Library.Numeral_Type" MiniEvm "HOL-Library.Adhoc_Overloading"
begin

(* define EVM instruction syntax in terms of their representation as instruction-words *)
typedef inst = "{n :: nat . n \<le> 256 }" by auto
setup_lifting type_definition_inst

(* STOP *)
definition stop_codes  :: "nat set"  where "stop_codes = {0 :: nat}" 
declare stop_codes_def [simp add]
typedef stop_inst = "stop_codes" by auto
setup_lifting type_definition_stop_inst

lift_definition STOP_STOP :: stop_inst is "0x00 :: nat" by auto
free_constructors cases_stop_inst for STOP_STOP
  by (transfer; auto)+

lift_definition STOP_INST :: "stop_inst \<Rightarrow> inst" is id by auto

definition is_STOP :: "stop_inst \<Rightarrow> bool" where
"is_STOP x \<equiv> case x of STOP_STOP \<Rightarrow> True"

(* Arithmetic *)

definition arith_codes :: "nat set" where 
"arith_codes = set (List.upt 0x01 0x0c)"

declare arith_codes_def [simp add]
typedef arith_inst = "arith_codes" by auto
setup_lifting type_definition_arith_inst

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

lift_definition ARITH_INST :: "arith_inst \<Rightarrow> inst" is id by auto

(* comparisons *)
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

(* bits *)
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

(* keccak256 *)
definition keccak256_codes  :: "nat set"  where "keccak256_codes = {0x20 :: nat}" 
declare keccak256_codes_def [simp add]
typedef keccak256_inst = "keccak256_codes" by auto
setup_lifting type_definition_keccak256_inst

lift_definition KECCAK256_KECCAK256 :: keccak256_inst is "0x20 :: nat" by auto
free_constructors cases_keccak256_inst for KECCAK256_KECCAK256
  by (transfer; auto)+

(* transaction-specific data instructions *)
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

(* chain-specific data instructions *)
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

(* state and control instructions *)
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

(* push instructions *)
definition push_codes :: "nat set" where
"push_codes = set (List.upt 0x60 0x80)"
declare push_codes_def[simp add]
typedef push_inst = push_codes by auto
setup_lifting type_definition_push_inst

(* we split push into two sub-groups to avoid having a 32-way free_constructors theorem *)
definition push_few_codes :: "nat set" where
"push_few_codes = set (List.upt 0x60 0x70)"
declare push_few_codes_def[simp add]
typedef push_few_inst = push_few_codes by auto
setup_lifting type_definition_push_few_inst

lift_definition PUSHF_PUSH1  :: "push_few_inst" is "0x60" by auto
lift_definition PUSHF_PUSH2  :: "push_few_inst" is "0x61" by auto
lift_definition PUSHF_PUSH3  :: "push_few_inst" is "0x62" by auto
lift_definition PUSHF_PUSH4  :: "push_few_inst" is "0x63" by auto
lift_definition PUSHF_PUSH5  :: "push_few_inst" is "0x64" by auto
lift_definition PUSHF_PUSH6  :: "push_few_inst" is "0x65" by auto
lift_definition PUSHF_PUSH7  :: "push_few_inst" is "0x66" by auto
lift_definition PUSHF_PUSH8  :: "push_few_inst" is "0x67" by auto
lift_definition PUSHF_PUSH9  :: "push_few_inst" is "0x68" by auto
lift_definition PUSHF_PUSH10 :: "push_few_inst" is "0x69" by auto
lift_definition PUSHF_PUSH11 :: "push_few_inst" is "0x6a" by auto
lift_definition PUSHF_PUSH12 :: "push_few_inst" is "0x6b" by auto
lift_definition PUSHF_PUSH13 :: "push_few_inst" is "0x6c" by auto
lift_definition PUSHF_PUSH14 :: "push_few_inst" is "0x6d" by auto
lift_definition PUSHF_PUSH15 :: "push_few_inst" is "0x6e" by auto
lift_definition PUSHF_PUSH16 :: "push_few_inst" is "0x6f" by auto

free_constructors cases_push_few_inst for
PUSHF_PUSH1
| PUSHF_PUSH2
| PUSHF_PUSH3
| PUSHF_PUSH4
| PUSHF_PUSH5
| PUSHF_PUSH6
| PUSHF_PUSH7
| PUSHF_PUSH8
| PUSHF_PUSH9
| PUSHF_PUSH10
| PUSHF_PUSH11
| PUSHF_PUSH12
| PUSHF_PUSH13
| PUSHF_PUSH14
| PUSHF_PUSH15
| PUSHF_PUSH16
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

definition push_many_codes :: "nat set" where
"push_many_codes = set (List.upt 0x70 0x80)"
declare push_many_codes_def[simp add]
typedef push_many_inst = push_many_codes by auto
setup_lifting type_definition_push_many_inst

lift_definition PUSHM_PUSH17 :: "push_many_inst" is "0x70" by auto
lift_definition PUSHM_PUSH18 :: "push_many_inst" is "0x71" by auto
lift_definition PUSHM_PUSH19 :: "push_many_inst" is "0x72" by auto
lift_definition PUSHM_PUSH20 :: "push_many_inst" is "0x73" by auto
lift_definition PUSHM_PUSH21 :: "push_many_inst" is "0x74" by auto
lift_definition PUSHM_PUSH22 :: "push_many_inst" is "0x75" by auto
lift_definition PUSHM_PUSH23 :: "push_many_inst" is "0x76" by auto
lift_definition PUSHM_PUSH24 :: "push_many_inst" is "0x77" by auto
lift_definition PUSHM_PUSH25 :: "push_many_inst" is "0x78" by auto
lift_definition PUSHM_PUSH26 :: "push_many_inst" is "0x79" by auto
lift_definition PUSHM_PUSH27 :: "push_many_inst" is "0x7a" by auto
lift_definition PUSHM_PUSH28 :: "push_many_inst" is "0x7b" by auto
lift_definition PUSHM_PUSH29 :: "push_many_inst" is "0x7c" by auto
lift_definition PUSHM_PUSH30 :: "push_many_inst" is "0x7d" by auto
lift_definition PUSHM_PUSH31 :: "push_many_inst" is "0x7e" by auto
lift_definition PUSHM_PUSH32 :: "push_many_inst" is "0x7f" by auto

free_constructors cases_push_few_inst for
PUSHM_PUSH17
| PUSHM_PUSH18
| PUSHM_PUSH19
| PUSHM_PUSH20
| PUSHM_PUSH21
| PUSHM_PUSH22
| PUSHM_PUSH23
| PUSHM_PUSH24
| PUSHM_PUSH25
| PUSHM_PUSH26
| PUSHM_PUSH27
| PUSHM_PUSH28
| PUSHM_PUSH29
| PUSHM_PUSH30
| PUSHM_PUSH31
| PUSHM_PUSH32
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

(* putting together the pieces *)
lift_definition PUSHF :: "push_few_inst \<Rightarrow> push_inst" is id by auto
lift_definition PUSHM :: "push_many_inst \<Rightarrow> push_inst" is id by auto

free_constructors cases_push_inst for
PUSHF
| PUSHM
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

(* general version for use when not case-splitting.
   we could have one of these each for PUSHM and PUSHF, but because that is an
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

(*
free_constructors cases_push_inst for
PUSH_PUSH1
| PUSH_PUSH2
| PUSH_PUSH3
| PUSH_PUSH4
| PUSH_PUSH5
| PUSH_PUSH6
| PUSH_PUSH7
| PUSH_PUSH8
| PUSH_PUSH9
| PUSH_PUSH10
| PUSH_PUSH11
| PUSH_PUSH12
| PUSH_PUSH13
| PUSH_PUSH14
| PUSH_PUSH15
| PUSH_PUSH16
| PUSH_PUSH17
| PUSH_PUSH18
| PUSH_PUSH19
| PUSH_PUSH20
| PUSH_PUSH21
| PUSH_PUSH22
| PUSH_PUSH23
| PUSH_PUSH24
| PUSH_PUSH25
| PUSH_PUSH26
| PUSH_PUSH27
| PUSH_PUSH28
| PUSH_PUSH29
| PUSH_PUSH30
| PUSH_PUSH31
| PUSH_PUSH32
(* TODO: perhaps this is slower than we'd like. *)
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+
*)

(* dup instructions *)
definition dup_inst_codes :: "nat set" where
"dup_inst_codes = set (List.upt 0x80 0x90)"
declare dup_inst_codes_def[simp add]
typedef dup_inst = dup_inst_codes by auto
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

  then show "dup_gen n \<in> dup_inst_codes"
    using List.map_add_upt by auto
qed


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


(* swap instructions *)
definition swap_inst_codes :: "nat set" where
"swap_inst_codes = set (List.upt 0x90 0xa0)"
declare swap_inst_codes_def[simp add]
typedef swap_inst = swap_inst_codes by auto
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

  then show "swap_gen n \<in> swap_inst_codes"
    using List.map_add_upt by auto
qed

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

(* log instructions *)
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

free_constructors cases_log_inst for
LOG_LOG0
| LOG_LOG1
| LOG_LOG2
| LOG_LOG3
| LOG_LOG4
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

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

(* cross-contract communication instructions *)
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

(* special halting instructions *)
definition special_halt_codes where
"special_halt_codes = set (List.upt 0xfd 0x100)"
declare special_halt_codes_def[simp]
typedef special_halt_inst = special_halt_codes by auto
setup_lifting type_definition_special_halt_inst

lift_definition SPECIAL_HALT_REVERT       :: "special_halt_inst" is "0xfd" by auto
lift_definition SPECIAL_HALT_INVALID      :: "special_halt_inst" is "0xfe" by auto
lift_definition SPECIAL_HALT_SELFDESTRUCT :: "special_halt_inst" is "0xff" by auto

free_constructors cases_special_halt_inst for
SPECIAL_HALT_REVERT
| SPECIAL_HALT_INVALID
| SPECIAL_HALT_SELFDESTRUCT
  by(transfer;
     auto simp del:set_upt simp add:List.upt_def)+

(* putting it all together *)

(* we are leaving out EIP615 *)
definition good_inst_codes :: "nat set" where
"good_inst_codes = 
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

definition bad_inst_codes :: "nat set" where
"bad_inst_codes = 
  UNIV - good_inst_codes"
  

(*
typedef stop_others = "UNIV - stop_codes" unfolding stop_codes_def by auto
setup_lifting type_definition_stop_others
*)
(*
lift_definition 


lift_definition STOP_OTHER :: "

typedef inst_cmp = 
typedef inst_bits = "{n :: nat . (0x16 \<le> n \<and> n \<le> 0x1a)}" by auto
typedef inst_shift = "{n :: nat . (0x1b \<le> n \<and> n \<le> 0x1c

setup_lifting type_definition_inst
setup_lifting type_definition_bits

lift_definition EAND :: bits is "0x16" by auto
lift_definition EOR :: bits is "0x17" by auto
lift_definition EXOR :: bits is "0x18" by auto
lift_definition ENOT :: bits is "0x19" by auto
lift_definition EBYTE :: bits is "0x1A" by auto

free_constructors cases_bits for EAND | EOR | EXOR | ENOT | EBYTE
  by (transfer; auto)+

definition is_and :: "bits \<Rightarrow> bool" where "is_and x \<equiv> case x of EAND \<Rightarrow> True |  _ \<Rightarrow> False"

lift_definition BIT_INST :: "bits \<Rightarrow> inst" is "\<lambda>x. x" by auto

typedef other_inst = "{n::nat . n \<le> 256 \<and> n \<notin> {0x16, 0x17, 0x18, 0x19, 0x1a}}"
  by auto
setup_lifting type_definition_other_inst

lift_definition OTHER_INST :: "other_inst \<Rightarrow> inst" is "\<lambda>x . x" by auto

free_constructors cases_inst for BIT_INST | OTHER_INST
  by (transfer; auto)+

definition is_and_inst :: "inst \<Rightarrow> bool" where
  "is_and_inst x \<equiv> case x of (BIT_INST EAND) \<Rightarrow> True |
    (BIT_INST EOR) \<Rightarrow> False |
    (OTHER_INST x) \<Rightarrow> False |
    _ \<Rightarrow> False"


(* definitions for EVM syntax as well as
   EVM primitives not used in Yul *)

(*
definition is_two :: "num \<Rightarrow> bool" where
"is_two x 
  (case x of One \<Rightarrow> True | _ \<Rightarrow> False)"
*)
(*
datatype EVM_syn =
	 STOP
	|ADD
	|MUL
	|SUB
	|DIV
	|SDIV
	|MOD
	|SMOD
	|ADDMOD
	|MULMOD
	|EXP
	|SIGNEXTEND

| LT
	|GT					
	|SLT				
	|SGT				
	|EQ					
	|ISZERO			
	|AND				
	|OR					
	|XOR				
	|NOT				
	|BYTE				
	|SHL				
	|SHR				
	|SAR				

|	KECCAK256

|	ADDRESS 
	|BALANCE		
	|ORIGIN			
	|CALLER			
	|CALLVALUE
	|CALLDATALO
	|CALLDATASI
	|CALLDATACO
	|CODESIZE	
	|CODECOPY	
	|GASPRICE	
	|EXTCODESIZ
	|EXTCODECOP
	|RETURNDATA
	|RETURNDATACOPY
	|EXTCODEHASH

	|BLOCKHASH 
	|COINBASE	
	|TIMESTAMP
	|NUMBER			
	|DIFFICULTY
	|GASLIMIT	
	|CHAINID		
	|SELFBALANCE

| POP
	|MLOAD				
	|MSTORE			
	|MSTORE8		
	|SLOAD				
	|SSTORE			
	|JUMP				
	|JUMPI				
	|PC					
	|MSIZE				
	|GAS				
	|JUMPDEST	

	| PUSH1
	|PUSH2				
	|PUSH3				
	|PUSH4				
	|PUSH5				
	|PUSH6				
	|PUSH7				
	|PUSH8				
	|PUSH9				
	|PUSH10			
	|PUSH11			
	|PUSH12			
	|PUSH13			
	|PUSH14			
	|PUSH15			
	|PUSH16			
	|PUSH17			
	|PUSH18			
	|PUSH19			
	|PUSH20			
	|PUSH21			
	|PUSH22			
	|PUSH23			
	|PUSH24			
	|PUSH25			
	|PUSH26			
	|PUSH27			
	|PUSH28			
	|PUSH29			
	|PUSH30			
	|PUSH31			
	|PUSH32			

	| DUP1
	|DUP2				
	|DUP3				
	|DUP4				
	|DUP5				
	|DUP6				
	|DUP7				
	|DUP8				
	|DUP9				
	|DUP10				
	|DUP11				
	|DUP12				
	|DUP13				
	|DUP14				
	|DUP15				
	|DUP16				

| SWAP1 
	|SWAP2				
	|SWAP3				
	|SWAP4				
	|SWAP5				
	|SWAP6				
	|SWAP7				
	|SWAP8				
	|SWAP9				
	|SWAP10			
	|SWAP11			
	|SWAP12			
	|SWAP13			
	|SWAP14			
	|SWAP15			
	|SWAP16			

| LOG0
	|LOG1				
	|LOG2				
	|LOG3				
	|LOG4				

| CREATE
	|CALL				
	|CALLCODE	
	|RETURN			
	|DELEGATECA
	|CREATE2  
	|STATICCALL

|	REVERT  
	|INVALID  
	|SELFDESTRUCT
  
*)


print_antiquotations

definition hello1 [unfolded] :
"hello1  (0 :: nat)"

term "hello1"

datatype EVMI 
  EVMI "nat"

abbreviation  ESTOP  where
"ESTOP \<equiv> EVMI (0 :: nat)"

term "ESTOP"

abbreviation EADD where
"EADD \<equiv> EVMI 1"

abbreviation EMUL where
"EMUL \<equiv> EVMI 2"

abbreviation ESUB where
"ESUB \<equiv> EVMI 3"

abbreviation EDIV where
"EDIV \<equiv> EVMI 4"

abbreviation ESDIV where
"ESDIV \<equiv> EVMI 5"

abbreviation EMOD where
"EMOD \<equiv> EVMI 6"

abbreviation ESMOD where
"ESMOD \<equiv> EVMI 7"

abbreviation EADDMOD where
"EADDMOD \<equiv> EVMI 8"

abbreviation EMULMOD where
"EMULMOD \<equiv> EVMI 9"

abbreviation EEXP where
"EEXP \<equiv> EVMI 10"

abbreviation ESIGNEXTEND where
"ESIGNEXTEND \<equiv> EVMI 11"

(* --- *)

abbreviation ELT where
"ELT \<equiv> EVMI 16"

abbreviation EGT where
"EGT \<equiv> EVMI 17"

abbreviation ESLT where
"ESLT \<equiv> EVMI 18"

abbreviation ESGT where
"ESGT \<equiv> EVMI 19"

abbreviation EEQ where
"EEQ \<equiv> EVMI 20"

abbreviation EISZERO where
"EISZERO \<equiv> EVMI 21"

abbreviation EAND where
"EAND \<equiv> EVMI 22"

abbreviation EOR where
"EOR \<equiv> EVMI 23"

abbreviation EXOR where
"EXOR \<equiv> EVMI 24"

value "ESGT"

value "EVMI 1"

value "Suc 0 :: nat"

value "(\<lambda> i :: nat . (case i of (1 :: nat) \<Rightarrow> True))"


value "3 :: 8 word"
*)
*)

end
