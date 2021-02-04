theory MiniEvm
  imports YulSemanticsCommon
    "HOL-Library.Adhoc_Overloading"
    "HOL-Word.Word"
begin

(* based on
https://github.com/ethereum/solidity/blob/develop/libevmasm/Instruction.h
*)

(* EVM is unityped; everything is 256-bit word *)
type_synonym eint = "256 word"

consts keccak256 :: "eint \<Rightarrow> eint"

record estate =
  memory :: "eint \<Rightarrow> eint"
  storage :: "eint \<Rightarrow> eint"
  flag :: YulFlag
  calldata :: "eint list"

definition dummy_estate :: estate where
"dummy_estate =
  \<lparr> memory = \<lambda> _ . word_of_int 0
  , storage = \<lambda> _ . word_of_int 0
  , flag = Executing
  , calldata = [] \<rparr>"

consts mkBuiltin ::
  "'x \<Rightarrow> ('g, 'v, 't) function_sig'"

(* 1st number = number of arguments
   2nd number = number of returns *)

fun mkNames :: "String.literal list \<Rightarrow> ('t YulTypedName list)"
  where
"mkNames [] = []"
| "mkNames (s1 # st) =
  YulTypedName s1 YulDefaultType # mkNames st"

(* TODO: have a version of these thast lifts from
  ('g, unit) State Result
  (useful for handling builtins that can fail)
*)
definition mkBuiltin_0_0 ::
"('g, unit) State \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_0_0 f =
  \<lparr> f_sig_arguments = mkNames []
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . case vs of
      [] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None) \<rparr>"

definition mkBuiltin_1_0 ::
"('v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_1_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'']
    , f_sig_returns = mkNames []
    , f_sig_body = YulBuiltin
      (\<lambda> vs . case vs of
        [v] \<Rightarrow> Result 
                (\<lambda> g . 
                  (case f v g of
                    ((), g') \<Rightarrow> ([], g')))
        | _ \<Rightarrow> Error (STR ''Argument arity error'') None) \<rparr>"

definition mkBuiltin_1_1 ::
"('v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_1_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))\<rparr>"

definition mkBuiltin_2_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_2_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))\<rparr>"

definition mkBuiltin_2_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_2_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))\<rparr>"

definition mkBuiltin_2_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_2_2 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames [STR ''r1'', STR ''r2'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)) \<rparr>"


definition mkBuiltin_3_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_3_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)) \<rparr>"

definition mkBuiltin_3_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_3_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)) \<rparr>"

definition mkBuiltin_3_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('g, 'v, 't) function_sig'" where
"mkBuiltin_3_2 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames [STR ''r1'', STR ''r2'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)) \<rparr>"

adhoc_overloading mkBuiltin
  mkBuiltin_0_0
  mkBuiltin_1_0
  mkBuiltin_1_1
  mkBuiltin_2_0
  mkBuiltin_2_1
  mkBuiltin_2_2
  mkBuiltin_3_0
  mkBuiltin_3_1
  mkBuiltin_3_2

(*
 * EVM instruction semantics
 *)

(*
 * Stop + arithmetic
 *)

fun stop :: "(estate, unit) State" where
"stop s = ((), s \<lparr> flag := Halt \<rparr>)"

(* TODO: Eth-Isabelle does not directly use HOL-Word primitives for arithmetic
   operations - instead it converts to integers, does integer operations, and then converts back.
   Using the library primitives feels cleaner, but we should make sure the semantics are the same. *)
fun add :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"add i1 i2 s = (plus_word_inst.plus_word i1 i2, s)"

fun mul :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"mul i1 i2 s = (times_word_inst.times_word i1 i2, s)"

fun sub :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"sub i1 i2 s = (minus_word_inst.minus_word i1 i2, s)"

fun divd :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"divd i1 i2 s = (divide_word_inst.divide_word i1 i2, s)"

(* get minimum-valued word (2's complement) *)
definition ssmallest :: "('a :: len0) word" where
"ssmallest =
 (Word.setBit (Word.word_of_int 0 :: 'a word) (size (Word.word_of_int 0 :: 'a word) - 1))"

(* absolute value - NB this does not work for minimum signed value*)
fun word_abs :: "('a :: len) word \<Rightarrow> 'a word" where
"word_abs w =
  (if sint w < 0 then times_word_inst.times_word (word_of_int (-1)) w else w)"

(* helper for signed division.
   TODO: double check this is what we want *)
fun sdivd' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"sdivd' i1 i2 = 
  (if (i1 = ssmallest \<and> i2 = Word.word_of_int(-1))
   then ssmallest
   else 
   (case ((sint i1 < 0), (sint i2 < 0)) of
    (True, True) \<Rightarrow>
      times_word_inst.times_word (word_of_int (-1)) 
                                 (divide_word_inst.divide_word (word_abs i1) (word_abs i2))
    | (False, False) \<Rightarrow>
      times_word_inst.times_word (word_of_int (-1)) 
                                 (divide_word_inst.divide_word (word_abs i1) (word_abs i2))
    | _ \<Rightarrow> (divide_word_inst.divide_word (word_abs i1) (word_abs i2))))"

fun sdivd :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"sdivd i1 i2 s = (sdivd' i1 i2, s)"

fun modu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"modu' i1 i2 =
  (if i2 = word_of_int 0 then word_of_int 0
   else modulo_word_inst.modulo_word i1 i2)"

fun modu :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"modu i1 i2 s = (modu' i1 i2, s)"

fun smodu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"smodu' i1 i2 =
  (if sint i1 < 0 then
    times_word_inst.times_word (word_of_int (-1)) (modu' (word_abs i1) (word_abs i2))
   else modu' (word_abs i1) (word_abs i2))"

fun smodu :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"smodu i1 i2 s = 
  (smodu' i1 i2, s)"

value "word_of_int (257) :: 8 word"

(* TODO: should we write all the arithmetic operations this way?
*)
fun addmod :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"addmod i1 i2 i3 s =
  (if i3 = word_of_int 0 then (word_of_int 0, s)
   else
   (word_of_int ((uint i1) + (uint i2)  mod (uint i3)), s))"

fun mulmod :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"mulmod i1 i2 i3 s =
  (if i3 = word_of_int 0 then (word_of_int 0, s)
   else
   (word_of_int ((uint i1) * (uint i2)  mod (uint i3)), s))"

(* TODO: for large exponents this could be inefficient *)
fun exp :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"exp i1 i2 s =
  (word_of_int ((uint i1) ^ (nat (uint i2))), s)"

fun signextend' :: "('a :: len) word \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word"
  where
"signextend' w b idx 0 = w"
| "signextend' w b idx signloc =
   (if idx \<le> signloc then w
    else signextend' (bit_operations_word_inst.set_bit_word w idx b) b (idx - 1) signloc)"

(* TODO: make sure this does the right thing - I have tested on a couple of cases *)
fun signextend :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"signextend len w s =
  (if uint len \<ge> 31 then (w, s)
   else
   (let signloc = 8 * (nat (uint len) + 1) - 1 in
   (let signbit = bit_operations_word_inst.test_bit_word w signloc in
   (signextend' w signbit (255) signloc, s))))"

(*
 * Keccak256
 * TODO: Find a way to port Keccak implementation from the Lem one in Eth-Isabelle
 * Ideally, without pulling in all of Lem as a dependency.
 *)
fun keccak :: "eint \<Rightarrow> (estate, eint) State" where
"keccak i s =
  (keccak256 i, s)"


(*
 * Transaction metadata
 * (Address - Extcodehash)
 * TODO
 *)

(*
	ADDRESS = 0x30,		///< get address of currently executing account
	BALANCE,			///< get balance of the given account
	ORIGIN,				///< get execution origination address
	CALLER,				///< get caller address
	CALLVALUE,			///< get deposited value by the instruction/transaction responsible for this execution
	CALLDATALOAD,		///< get input data of current environment
	CALLDATASIZE,		///< get size of input data in current environment
	CALLDATACOPY,		///< copy input data in current environment to memory
	CODESIZE,			///< get size of code running in current environment
	CODECOPY,			///< copy code running in current environment to memory
	GASPRICE,			///< get price of gas in current environment
	EXTCODESIZE,		///< get external code size (from another contract)
	EXTCODECOPY,		///< copy external code (from another contract)
	RETURNDATASIZE = 0x3d,	///< get size of return data buffer
	RETURNDATACOPY = 0x3e,	///< copy return data in current environment to memory
	EXTCODEHASH = 0x3f,	///< get external code hash (from another contract)

*)

(*
 * Transaction metadata
 * (Blockhash - Selfbalance)
 *)

(*
	BLOCKHASH = 0x40,	///< get hash of most recent complete block
	COINBASE,			///< get the block's coinbase address
	TIMESTAMP,			///< get the block's timestamp
	NUMBER,				///< get the block's number
	DIFFICULTY,			///< get the block's difficulty
	GASLIMIT,			///< get the block's gas limit
	CHAINID,			///< get the config's chainid param
	SELFBALANCE,		///< get balance of the current account
*)

(*
 * Stack, Memory, Storage, and Control Flow
 *)
(*
	POP = 0x50,			///< remove item from stack
	MLOAD,				///< load word from memory
	MSTORE,				///< save word to memory
	MSTORE8,			///< save byte to memory
	SLOAD,				///< load word from storage
	SSTORE,				///< save word to storage
	JUMP,				///< alter the program counter
	JUMPI,				///< conditionally alter the program counter
	PC,					///< get the program counter
	MSIZE,				///< get the size of active memory
	GAS,				///< get the amount of available gas
	JUMPDEST,			///< set a potential jump destination
*)

(*
 * Push instructions (not used)
 * Dup instructions (not used)
 * Swap instructions (not used)
 *)

(* 
 * Log instructions 
 * TODO
*)

(*
	LOG0 = 0xa0,		///< Makes a log entry; no topics.
	LOG1,				///< Makes a log entry; 1 topic.
	LOG2,				///< Makes a log entry; 2 topics.
	LOG3,				///< Makes a log entry; 3 topics.
	LOG4,				///< Makes a log entry; 4 topics.
*)

(*
 * EIP615 instructions (not used)
 *)

(*
 * Contract creation and cross-contract calls
 * (Implement these later)
 *)
(*
	CREATE = 0xf0,		///< create a new account with associated code
	CALL,				///< message-call into an account
	CALLCODE,			///< message-call with another account's code only
	RETURN,				///< halt execution returning output data
	DELEGATECALL,		///< like CALLCODE but keeps caller's value and sender
	CREATE2 = 0xf5,		///< create new account with associated code at address `sha3(0xff + sender + salt + init code) % 2**160`
	STATICCALL = 0xfa,	///< like CALL but disallow state modifications
*)

(*
 * Halting instructions
 *)
(*
	REVERT = 0xfd,		///< halt execution, revert state and return output data
	INVALID = 0xfe,		///< invalid instruction for expressing runtime errors (e.g., division-by-zero)
	SELFDESTRUCT = 0xff	///< halt execution and register account for later deletion
*)

end
