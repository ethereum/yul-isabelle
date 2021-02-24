theory MiniEvm
  imports YulDialect
    (*"HOL-Library.Word"*)
    "HOL-Word.Word"
    "Keccak/Keccak"
begin

(* based on
https://github.com/ethereum/solidity/blob/develop/libevmasm/Instruction.h
*)


datatype logentry =
  Log0 "8 word list"
  | Log1 "8 word list" eint
  | Log2 "8 word list" eint eint
  | Log3 "8 word list" eint eint eint
  | Log4 "8 word list" eint eint eint eint

record estate_core =
  (* Memory is byte-indexed *)
  e_memory :: "8 word list"
  (* Storage is word-indexed *)
  e_storage :: "eint \<Rightarrow> eint"
  e_flag :: YulFlag
  e_log :: "logentry list"

record estate_resource = estate_core +
  e_msize :: eint
  e_gas :: eint  

record estate_data = estate_resource +
  e_codedata :: "8 word list"
  e_calldata :: "8 word list"
(*  e_outputdata :: "8 word list" *)
  e_returndata :: "8 word list"

record estate_metadata = estate_data +
  e_address :: eint
  e_origin :: eint
  e_caller :: eint
  e_callvalue :: eint
  e_gasprice :: eint
  e_blockhash :: eint
  e_coinbase :: eint
  e_timestamp :: eint
  e_blocknumber :: eint
  e_difficulty :: eint
  e_gaslimit :: eint
  e_chainid :: eint
  e_selfbalance :: eint

(* TODO: we could also add external programs as
   Isabelle functions here
 *)
record estate = estate_metadata +
  e_extcode :: "eaddr \<Rightarrow> 8 word list"
  (* e_extcode_sem :: *)
  e_balances :: "eaddr \<Rightarrow> eint"
  (* tracking account existence is needed for balance *)
  e_acct_exists :: "eaddr \<Rightarrow> bool"
  (* tracking "dead"-ness of accounts is needed for extcodehash *)
  e_acct_live :: "eaddr \<Rightarrow> bool"

(*
  this can't be in estate because of positivity constraint 
*)
record estate_ext_sem = estate +
  e_extcode_sem :: "eaddr \<Rightarrow> (estate, unit) State"

(*
record estate_core_resource = estate_core_data +
  msize :: eint
  gas :: eint
*)

(* record estate_core_intercontract = ... *)
definition dummy_estate :: estate where
"dummy_estate =
  \<lparr> e_memory = []
  , e_storage = \<lambda> _ . word_of_int 0  
  , e_flag = Executing
  , e_log = []
  , e_msize = word_of_int 0
  , e_gas = word_of_int 0
  , e_codedata = []
  , e_calldata = []
\<comment> \<open>  , e_outputdata = [] \<close>
  , e_returndata = []
  , e_address = word_of_int 0
  , e_origin = word_of_int 0
  , e_caller = word_of_int 0
  , e_callvalue = word_of_int 0
  , e_gasprice = word_of_int 0
  , e_blockhash = word_of_int 0
  , e_coinbase = word_of_int 0
  , e_timestamp = word_of_int 0
  , e_blocknumber = word_of_int 0
  , e_difficulty = word_of_int 0
  , e_gaslimit = word_of_int 0
  , e_chainid = word_of_int 0
  , e_selfbalance = word_of_int 0 
  , e_extcode = (\<lambda> _ . [])
  , e_balances = (\<lambda> _ . word_of_int 0)
  , e_acct_exists = (\<lambda> _ . False)
  , e_acct_live = (\<lambda> _ . False)

  \<rparr>"


(*
 * EVM instruction semantics
 *)

(*
 * Stop + arithmetic
 *)

fun ei_stop :: "(estate, unit) State" where
"ei_stop s = ((), s \<lparr> e_flag := Halt \<rparr>)"

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

(* new sign extend implementation for better compatibility with Isabelle2021 *)
fun signextend' :: "('a :: len) word \<Rightarrow> nat \<Rightarrow> 'a word" where
"signextend' w n =
  (let signloc = 8 * (n + 1) - 1 in
   \<comment> \<open>all zeroes, except for sign bit we are extending\<close>
   (let testmask = word_of_int (2 ^ (signloc)) in
   \<comment> \<open>all ones at bits lower than sign bit we are extending\<close>
   (let mask = word_of_int (2 ^ (signloc) - 1) in
    (if w AND testmask = word_of_int 0
     then w AND mask
     else w OR (NOT mask)))))"

(*
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
*)

(* TODO: make sure this does the right thing - I have tested on a couple of cases *)
fun ei_signextend :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_signextend len w s =
  (if uint len \<ge> 31 then (w, s)
   else
   (signextend' w (unat len), s))"


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


(*
 * Keccak256
 *)

(* helper for pulling values from a list, adding default value if the end is reached *)
fun take_default :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"take_default n dfl ls =
  take n ls @ (replicate (n - length ls) dfl)"

(* helper for pulling word values from a list, adding zero-word value if the end is reached *)
fun take_padded :: "nat \<Rightarrow> ('a :: len) word list \<Rightarrow> 'a word list" where
"take_padded n ls = take_default n (word_of_int 0) ls"

fun ei_keccak256 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_keccak256 idx sz st =
  (Keccak.keccak (take_padded (unat sz) (drop (unat idx) (e_memory st))), st)"


(*
 * Transaction metadata
 * (Address - Extcodehash)
 *)

fun ei_address :: "(estate, eint) State" where
"ei_address s = (e_address s, s)"

fun ei_balance :: "eint \<Rightarrow> (estate, eint) State" where
"ei_balance acctid s = 
  ((if e_acct_exists s (ucast acctid)
    then e_balances s (ucast acctid) 
    else word_of_int 0)
  , s)"

fun ei_origin :: "(estate, eint) State" where
"ei_origin s = (e_origin s, s)"

fun ei_caller :: "(estate, eint) State" where
"ei_caller s = (e_caller s, s)"

fun ei_callvalue :: "(estate, eint) State" where
"ei_callvalue s = (e_callvalue s, s)"

(* Helper for calldataload.
   Pad call data, then return 32 bytes starting at byte n *)
fun bulk_load :: "nat \<Rightarrow> 8 word list \<Rightarrow> eint" where
"bulk_load n wl = word_rcat (take_padded 32 (drop n wl))"

fun ei_calldataload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_calldataload loc s = 
 (bulk_load (unat loc) (e_calldata s), s)"

fun ei_calldatasize :: "(estate, eint) State" where
"ei_calldatasize s = (Word.word_of_int (int (length (e_calldata s))), s)"

(* helper for calldatacopy, extcodecopy, returndatacopy *)
fun bulk_copy :: 
"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"bulk_copy to_idx from_idx n_bytes mem ext_data =
 (let loaded_bytes = take_padded n_bytes (drop from_idx ext_data) in
  take to_idx mem @ loaded_bytes @ drop (to_idx + n_bytes) mem)"

fun ei_calldatacopy :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_calldatacopy to_idx from_idx n_bytes s = 
 ((), (s \<lparr> e_memory := bulk_copy (unat to_idx) (unat from_idx) (unat n_bytes)
                                 (e_memory s) (e_calldata s) \<rparr>))"

fun ei_codesize :: "(estate, eint) State" where
"ei_codesize s = (Word.word_of_int (int (length (e_codedata s))), s)"

fun ei_codecopy :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_codecopy to_idx from_idx n_bytes s =
  ((), (s \<lparr> e_memory := bulk_copy (unat to_idx) (unat from_idx) (unat n_bytes)
                                  (e_memory s) (e_codedata s) \<rparr>))"

fun ei_gasprice :: "(estate, eint) State" where
"ei_gasprice s = (e_gasprice s, s)"

fun ei_extcodesize :: "eint \<Rightarrow> (estate, eint) State" where
"ei_extcodesize acctid s = (word_of_int (int (length (e_extcode s (ucast acctid)))), s)"

fun ei_extcodecopy :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_extcodecopy acctid to_idx from_idx n_bytes s =
  ((), (s \<lparr> e_memory := bulk_copy (unat to_idx) (unat from_idx) (unat n_bytes)
                                  (e_memory s) (e_extcode s (ucast acctid)) \<rparr>))"

fun ei_returndatasize :: "(estate, eint) State" where
"ei_returndatasize s =
  (word_of_int (int (length (e_returndata s))), s)"

fun ei_returndatacopy :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_returndatacopy to_idx from_idx n_bytes s = 
  ((), (s \<lparr> e_memory := bulk_copy (unat to_idx) (unat from_idx) (unat n_bytes)
                                  (e_memory s) (e_returndata s) \<rparr>))"

fun ei_extcodehash :: "eint \<Rightarrow> (estate, eint) State" where
"ei_extcodehash acctid s =
 ((if e_acct_live s (ucast acctid)
   then Keccak.keccak (e_extcode s (ucast acctid))
   else word_of_int 0)
 , s)"

(*
 * Transaction metadata
 * (Blockhash - Selfbalance)
 *)

fun ei_blockhash :: "(estate, eint) State" where
"ei_blockhash st = (e_blockhash st, st)"

fun ei_coinbase :: "(estate, eint) State" where
"ei_coinbase st = (e_coinbase st, st)"

fun ei_timestamp :: "(estate, eint) State" where
"ei_timestamp st = (e_timestamp st, st)"

fun ei_number :: "(estate, eint) State" where
"ei_number st = (e_blocknumber st, st)"

fun ei_difficulty :: "(estate, eint) State" where
"ei_difficulty st = (e_difficulty st, st)"

fun ei_gaslimit :: "(estate, eint) State" where
"ei_gaslimit st = (e_gaslimit st, st)"

fun ei_chainid :: "(estate, eint) State" where
"ei_chainid st = (e_chainid st, st)"

fun ei_selfbalance :: "(estate, eint) State" where
"ei_selfbalance st = (e_selfbalance st, st)"

(*
 * Stack, Memory, Storage, and Control Flow
 * TODO: track memory, storage for gas purposes
 *)

(* another helper for accessing memory *)
fun get_mrange :: "estate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ebyte list" where
"get_mrange st idx sz =
  (take_padded sz (drop idx (e_memory st)))"

fun ei_pop :: "eint \<Rightarrow> (estate, unit) State" where
"ei_pop i1 s = ((), s)"

(* mload = get 32 bytes from given location in memory *)
(* TODO: make sure endianness is correct here *)
fun ei_mload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_mload i1 s =
  (let bytes = get_mrange s (nat (uint i1)) 32 in
  (word_rcat bytes, s))"

fun ei_mstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore idx value st =
  (let bytes = word_rsplit value :: 8 word list in
  ((),
   (st \<lparr> e_memory := bulk_copy (unat idx) 0 32 (e_memory st) bytes \<rparr>)))"

fun ei_mstore8 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore8 idx value st =
  (let bytes = [(Word.ucast value) :: 8 word] in
  ((),
   (st \<lparr> e_memory := bulk_copy (unat idx) 0 32 (e_memory st) bytes \<rparr>)))"

fun ei_sload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_sload idx st =
 (e_storage st idx, st)" 

fun ei_sstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_sstore idx value st =
  ((), (st \<lparr> e_storage := (\<lambda> i . if i = idx then value else e_storage st i) \<rparr>))"

(* jump, jumpi, pc = not supported here *)

(* msize -
   TODO currently the implementation does not actually update this field *)
fun ei_msize :: "(estate, eint) State" where
"ei_msize st = (e_msize st, st)"

(* gas -
   TODO currently the implementation does not actually update this field *)
fun ei_gas :: "(estate, eint) State" where
"ei_gas st = (e_gas st, st)"

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
*)

fun ei_log0 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log0 start end st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log0 (get_mrange st (unat start) (unat end - unat start))] \<rparr>))"

fun ei_log1 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log1 start end t1 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log1 (get_mrange st (unat start) (unat end - unat start)) t1] \<rparr>))"

fun ei_log2 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log2 start end t1 t2 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log2 (get_mrange st (unat start) (unat end - unat start)) t1 t2] \<rparr>))"

fun ei_log3 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log3 start end t1 t2 t3 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log3 (get_mrange st (unat start) (unat end - unat start)) t1 t2 t3] \<rparr>))"

fun ei_log4 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State"
  where
"ei_log4 start end t1 t2 t3 t4 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log4 (get_mrange st (unat start) (unat end - unat start)) t1 t2 t3 t4] \<rparr>))"

(*
 * EIP615 instructions (not used)
 *)

(*
 * Contract creation and cross-contract calls
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

(* TODO: where to generate the new address? It might be ideal to do this in
   the global semantics. For now we just always return 0. Global semantics
   should probably replace this with the correct value. *)
fun ei_create :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_create value idx sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := Create value (get_mrange s (unat idx) (unat sz)) \<rparr>))"

fun ei_call :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_call gas target value in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := Call gas target value (get_mrange s (unat in_idx) (unat in_sz)) out_idx out_sz \<rparr> ))"

fun ei_callcode :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_callcode gas target value in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := CallCode gas target value (get_mrange s (unat in_idx) (unat in_sz)) out_idx out_sz \<rparr> ))"

fun ei_return :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_return idx sz s =
  (()
  , (s \<lparr> e_flag := Return (get_mrange s (unat idx) (unat sz)) \<rparr>))"

fun ei_delegatecall ::  "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_delegatecall gas target in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := DelegateCall gas target (get_mrange s (unat in_idx) (unat in_sz)) out_idx out_sz \<rparr> ))"

fun ei_create2 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_create2 value idx sz salt s =
  (word_of_int 0
  , (s \<lparr> e_flag := Create2 value (get_mrange s (unat idx) (unat sz)) salt \<rparr>))"

fun ei_staticcall ::  "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_staticcall gas target in_idx in_sz out_idx out_sz s =
  (word_of_int 0, 
  (s \<lparr> e_flag := StaticCall gas target (get_mrange s (unat in_idx) (unat in_sz)) out_idx out_sz \<rparr>))"
(*
 * Halting instructions
 *)

(* TODO: we have not yet implemented return-value *)
fun ei_revert :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_revert _ _ st =
  ((), (st \<lparr> e_flag := Revert \<rparr>))"

(* TODO: it looks like invalid might need to be polymorphic in number of arguments.
   Treating it as (0, 0) for now, since this will lead to an arity error in other cases. *)
fun ei_invalid :: "(estate, unit) State" where
"ei_invalid st = ((), (st \<lparr> e_flag := Throw \<rparr>))"

(* TODO: make proper use of the argument here *)
fun ei_selfdestruct :: "eint \<Rightarrow> (estate, unit) State" where
"ei_selfdestruct _ st =
  ((), (st \<lparr> e_flag := SelfDestruct \<rparr>))"


end
