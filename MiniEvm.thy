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
  (* Memory is byte-indexed *)
  memory :: "eint \<Rightarrow> 8 word"
  (* Storage is word-indexed *)
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

fun ei_stop :: "(estate, unit) State" where
"ei_stop s = ((), s \<lparr> flag := Halt \<rparr>)"

(* TODO: Eth-Isabelle does not directly use HOL-Word primitives for arithmetic
   operations - instead it converts to integers, does integer operations, and then converts back.
   Using the library primitives feels cleaner, but we should make sure the semantics are the same. *)
fun ei_add :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_add i1 i2 s = (plus_word_inst.plus_word i1 i2, s)"

fun ei_mul :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_mul i1 i2 s = (times_word_inst.times_word i1 i2, s)"

fun ei_sub :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sub i1 i2 s = (minus_word_inst.minus_word i1 i2, s)"

fun ei_div :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_div i1 i2 s = (divide_word_inst.divide_word i1 i2, s)"

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

fun ei_sdiv :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sdiv i1 i2 s = (sdivd' i1 i2, s)"

fun modu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"modu' i1 i2 =
  (if i2 = word_of_int 0 then word_of_int 0
   else modulo_word_inst.modulo_word i1 i2)"

fun ei_mod :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_mod i1 i2 s = (modu' i1 i2, s)"

fun smodu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"smodu' i1 i2 =
  (if sint i1 < 0 then
    times_word_inst.times_word (word_of_int (-1)) (modu' (word_abs i1) (word_abs i2))
   else modu' (word_abs i1) (word_abs i2))"

fun ei_smod :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_smod i1 i2 s = 
  (smodu' i1 i2, s)"

value "word_of_int (257) :: 8 word"

(* TODO: should we write all the arithmetic operations this way?
*)
fun ei_addmod :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_addmod i1 i2 i3 s =
  (if i3 = word_of_int 0 then (word_of_int 0, s)
   else
   (word_of_int ((uint i1) + (uint i2)  mod (uint i3)), s))"

fun ei_mulmod :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_mulmod i1 i2 i3 s =
  (if i3 = word_of_int 0 then (word_of_int 0, s)
   else
   (word_of_int ((uint i1) * (uint i2)  mod (uint i3)), s))"

(* TODO: for large exponents this could be inefficient *)
fun ei_exp :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_exp i1 i2 s =
  (word_of_int ((uint i1) ^ (nat (uint i2))), s)"

fun signextend' :: "('a :: len) word \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word"
  where
"signextend' w b idx 0 = w"
| "signextend' w b idx signloc =
   (if idx \<le> signloc then w
    else signextend' (bit_operations_word_inst.set_bit_word w idx b) b (idx - 1) signloc)"

(* TODO: make sure this does the right thing - I have tested on a couple of cases *)
fun ei_signextend :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_signextend len w s =
  (if uint len \<ge> 31 then (w, s)
   else
   (let signloc = 8 * (nat (uint len) + 1) - 1 in
   (let signbit = bit_operations_word_inst.test_bit_word w signloc in
   (signextend' w signbit (255) signloc, s))))"

(*
 * Comparison and Bitwise Operations
 *)
fun ei_lt :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_lt i1 i2 s =
  (if uint i1 < uint i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_gt :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_gt i1 i2 s =
  (if uint i1 > uint i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_slt :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_slt i1 i2 s =
  (if sint i1 < sint i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_sgt :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sgt i1 i2 s =
  (if sint i1 > sint i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_eq :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_eq i1 i2 s =
  (if i1 = i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_iszero :: "eint \<Rightarrow> (estate, eint) State" where
"ei_iszero i1 s =
  (if i1 = word_of_int 0
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_and :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_and i1 i2 s =
  (bit_operations_word_inst.bitAND_word i1 i2, s)"

fun ei_or :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_or i1 i2 s =
  (bit_operations_word_inst.bitOR_word i1 i2, s)"

fun ei_xor :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_xor i1 i2 s =
  (bit_operations_word_inst.bitXOR_word i1 i2, s)"

fun ei_not :: "eint \<Rightarrow> (estate, eint) State" where
"ei_not i1 s =
  (bit_operations_word_inst.bitNOT_word i1, s)"

value "scast ((word_of_int (-1) :: 8 word)) :: 256 word"

(* note that rsplit goes from most \<rightarrow> least significant digits
   (this is the opposite of how test_bit_word works)
*)
fun ei_byte :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_byte idx word s = 
  (if (uint idx) \<ge> 32 then (word_of_int 0, s)
   else
   (let bytes = (word_rsplit word :: 8 word list) in
    (ucast (bytes ! nat (uint idx)), s)))"

fun shl_many :: "('a :: len) word \<Rightarrow> int \<Rightarrow> 'a word" where
"shl_many w n =
  (if n \<le> 0 then w
   else shl_many (shiftl1 w) (n-1))"

fun ei_shl :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_shl i1 i2 s = 
  (shl_many i1 (uint i2), s)"

fun shr_many :: "('a :: len) word \<Rightarrow> int \<Rightarrow> 'a word" where
"shr_many w n =
  (if n \<le> 0 then w
   else shr_many (shiftr1 w) (n-1))"

fun ei_shr :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_shr i1 i2 s = 
  (shr_many i1 (uint i2), s)"

fun ei_sar :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sar i1 i2 s = 
  (sshiftr i1 (nat (uint i2)), s)"

value "sint (sshiftr (word_of_int (-128) :: 8 word) 1)"

(*
 * Keccak256
 * TODO: Find a way to port Keccak implementation from the Lem one in Eth-Isabelle
 * Ideally, without pulling in all of Lem as a dependency.
 *)
fun ei_keccak :: "eint \<Rightarrow> (estate, eint) State" where
"ei_keccak i s =
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
 * TODO
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
 * TODO: track memory, storage for gas purposes
 *)

fun ei_pop :: "eint \<Rightarrow> (estate, unit) State" where
"ei_pop i1 s = ((), s)"

fun get_mrange :: "estate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word list" where
"get_mrange st min_idx 0 = []"
| "get_mrange st min_idx (Suc num_bytes') =
   memory st (word_of_int (int min_idx)) # get_mrange st (min_idx + 1) num_bytes'"

(* mload = get 32 bytes from given location in memory *)
(* TODO: make sure endianness is correct here *)
fun ei_mload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_mload i1 s =
  (let bytes = get_mrange s (nat (uint i1)) 32 in
  (word_rcat bytes, s))"

(* TODO: this feels like it will be inefficient.
   We might want to consider a different representation for memory *)
fun put_mem :: "estate \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> estate" where
"put_mem st min_idx data =
 (st \<lparr> memory :=
       (\<lambda> i . 
        (if uint i \<ge> int min_idx \<and> uint i < int (min_idx + length data)
         then data ! (nat (uint i) - min_idx)
         else memory st i)) \<rparr>)"

fun ei_mstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore idx value st =
  (let bytes = word_rsplit value :: 8 word list in
   ((), put_mem st (nat (uint idx)) bytes))"

fun ei_mstore8 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore8 idx value st =
  ((), put_mem st (nat (uint idx)) [(Word.ucast value) :: 8 word])"

fun ei_sload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_sload idx st =
 (storage st idx, st)" 

fun ei_sstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_sstore idx value st =
  ((), (st \<lparr> storage := (\<lambda> i . if i = idx then value else storage st i) \<rparr>))"

(* jump, jumpi, pc = not supported here *)

(* msize - TODO *)

(* gas - TODO *)

(* jumpdest = not supported here, unless we need a NOP for some reason *)
fun ei_jumpdest :: "(estate, unit) State" where
"ei_jumpdest st = ((), st)"

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
 * (Implement these later) TODO
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

(* TODO: we have not yet implemented return-value *)
fun ei_revert :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_revert _ _ st =
  ((), (st \<lparr> flag := Revert \<rparr>))"

(* TODO: it looks like invalid might need to be polymorphic in number of arguments.
   Treating it as (0, 0) for now, since this will lead to an arity error in other cases. *)
fun ei_invalid :: "(estate, unit) State" where
"ei_invalid st = ((), (st \<lparr> flag := Throw \<rparr>))"

(* TODO: make proper use of the argument here *)
fun ei_selfdestruct :: "eint \<Rightarrow> (estate, unit) State" where
"ei_selfdestruct _ st =
  ((), (st \<lparr> flag := SelfDestruct \<rparr>))"

end
