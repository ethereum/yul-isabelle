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
definition compare_codes :: "nat set" where "compare_codes = {n :: nat . (0x10 \<le> n \<and> n \<le> 0x15)}"
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

definition bits_codes :: "nat set" where "bits_codes = {n :: nat . (0x16 \<le> n \<and> n \<le> 0x1f)}"
declare bits_codes_def [simp add]
typedef inst_bits = "bits_codes" by auto
setup_lifting type_definition_inst_bits

lift_definition BITS_AND  :: "inst_bits" is "0x16" by auto
lift_definition BITS_OR   ::
lift_definition BITS_XOR  ::
lift_definition BITS_NOT  ::
lift_definition BITS_BYTE ::
lift_definition BITS_SHL  ::
lift_definition BITS_SHR  ::
lift_definition BITS_SAR  ::



definition is_ADD :: "inst_arith \<Rightarrow> bool" where
"is_ADD x \<equiv> case x of ARITH_ADD \<Rightarrow> True | _ \<Rightarrow> False"

(*
typedef stop_others = "UNIV - stop_codes" unfolding stop_codes_def by auto
setup_lifting type_definition_stop_others
*)
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

end
