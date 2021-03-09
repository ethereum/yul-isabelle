theory MiniEvmFlat
  imports "../YulDialect"
    "HOL-Library.Word"
    "../Keccak/Keccak"
    "../Word_Lib/Bits_Int"
    "../YulSemanticsSingleStep"
begin

(* based on
https://github.com/ethereum/solidity/blob/develop/libevmasm/Instruction.h
*)

(*
  this version of minevm uses a "flat" record layout rather than extension
*)

(*
type_synonym edata = "eint \<Rightarrow> 8 word"
*)

type_synonym edata = "8 word list"

datatype logentry =
  Log0 "8 word list"
  | Log1 "8 word list" eint
  | Log2 "8 word list" eint eint
  | Log3 "8 word list" eint eint eint
  | Log4 "8 word list" eint eint eint eint

record estate_core =
  (* Memory is byte-indexed *)
  (* e_memory :: "8 word list" *)
  es_memory :: "edata"
  (* Storage is word-indexed *)
  es_storage :: "eint \<Rightarrow> eint"
  es_flag :: YulFlag
  es_log :: "logentry list"

record estate_resource =
  es_msize :: eint
  es_gas :: eint  

record estate_data =
  es_codedata :: "edata"
  es_calldata :: "edata"
  es_returndata :: "edata"

record estate_metadata = 
  es_address :: eint
  es_origin :: eint
  es_caller :: eint
  es_callvalue :: eint
  es_gasprice :: eint
  es_blockhash :: eint
  es_coinbase :: eint
  es_timestamp :: eint
  es_blocknumber :: eint
  es_difficulty :: eint
  es_gaslimit :: eint
  es_chainid :: eint
  es_selfbalance :: eint

(* TODO: we could also add external programs as
   Isabelle functions here
 *)
record estate_ext = 
  es_extcode :: "eaddr \<Rightarrow> edata"
  (* e_extcode_sem :: *)
  es_balances :: "eaddr \<Rightarrow> eint"
  (* tracking account existence is needed for balance *)
  es_acct_exists :: "eaddr \<Rightarrow> bool"
  (* tracking "dead"-ness of accounts is needed for extcodehash *)
  es_acct_live :: "eaddr \<Rightarrow> bool"

record estate =
  es_core :: "estate_core"
  es_resource :: "estate_resource"
  es_data :: "estate_data"
  es_metadata :: "estate_metadata"
  es_ext :: "estate_ext"

abbreviation e_memory where "e_memory \<equiv> es_memory o es_core"
abbreviation e_storage where "e_storage \<equiv> es_storage o es_core"
abbreviation e_flag where "e_flag \<equiv> es_flag o es_core"
abbreviation e_log where "e_log \<equiv> es_log o es_core"

abbreviation e_msize where "e_msize \<equiv> es_msize o es_resource"
abbreviation e_gas where "e_gas \<equiv> es_gas o es_resource"

abbreviation e_codedata where "e_codedata \<equiv> es_codedata o es_data"
abbreviation e_calldata where "e_calldata \<equiv> es_calldata o es_data"
abbreviation e_returndata where "e_returndata \<equiv> es_returndata o es_data"

abbreviation e_address where "e_address \<equiv> es_address o es_metadata"
abbreviation e_origin where "e_origin \<equiv> es_origin o es_metadata"
abbreviation e_caller where "e_caller \<equiv> es_caller o es_metadata"
abbreviation e_callvalue where "e_callvalue \<equiv> es_callvalue o es_metadata"
abbreviation e_gasprice where "e_gasprice \<equiv> es_gasprice o es_metadata"
abbreviation e_blockhash where "e_blockhash \<equiv> es_blockhash o es_metadata"
abbreviation e_coinbase where "e_coinbase \<equiv> es_coinbase o es_metadata"
abbreviation e_timestamp where "e_timestamp \<equiv> es_timestamp o es_metadata"
abbreviation e_blocknumber where "e_blocknumber \<equiv> es_blocknumber o es_metadata"
abbreviation e_difficulty where "e_difficulty \<equiv> es_difficulty o es_metadata"
abbreviation e_gaslimit where "e_gaslimit \<equiv> es_gaslimit o es_metadata"
abbreviation e_chainid where "e_chainid \<equiv> es_chainid o es_metadata"
abbreviation e_selfbalance where "e_selfbalance \<equiv> es_selfbalance o es_metadata"

abbreviation e_extcode where "e_extcode \<equiv> es_extcode o es_ext"
abbreviation e_balances where "e_balances \<equiv> es_balances o es_ext"
abbreviation e_acct_exists where "e_acct_exists \<equiv> es_acct_exists o es_ext"
abbreviation e_acct_live where "e_acct_live \<equiv> es_acct_live o es_ext"

abbreviation e_memory_update where  "e_memory_update \<equiv> es_core_update o es_memory_update"
abbreviation e_storage_update where "e_storage_update \<equiv> es_core_update o es_storage_update"
abbreviation e_flag_update where "e_flag_update \<equiv> es_core_update o es_flag_update"
abbreviation e_log_update where "e_log_update \<equiv> es_core_update o es_log_update"

abbreviation e_msize_update where "e_msize_update \<equiv> es_resource_update o es_msize_update"
abbreviation e_gas_update where "e_gas_update \<equiv> es_resource_update o es_gas_update"

abbreviation e_codedata_update where
"e_codedata_update \<equiv> es_data_update o es_codedata_update"
abbreviation e_calldata_update where
"e_calldata_update \<equiv> es_data_update o es_calldata_update"
abbreviation e_returndata_update where
"e_returndata_update \<equiv> es_data_update o es_returndata_update"

abbreviation e_address_update where
"e_address_update == es_metadata_update o es_address_update"
abbreviation e_origin_update where
"e_origin_update == es_metadata_update o es_origin_update"
abbreviation e_caller_update where
"e_caller_update == es_metadata_update o es_caller_update"
abbreviation e_callvalue_update where
"e_callvalue_update == es_metadata_update o es_callvalue_update"
abbreviation e_gasprice_update where
"e_gasprice_update == es_metadata_update o es_gasprice_update"
abbreviation e_blockhash_update where
"e_blockhash_update == es_metadata_update o es_blockhash_update"
abbreviation e_coinbase_update where
"e_coinbase_update == es_metadata_update o es_coinbase_update"
abbreviation e_timestamp_update where
"e_timestamp_update == es_metadata_update o es_timestamp_update"
abbreviation e_blocknumber_update where
"e_blocknumber_update == es_metadata_update o es_blocknumber_update"
abbreviation e_difficulty_update where
"e_difficulty_update == es_metadata_update o es_difficulty_update"
abbreviation e_gaslimit_update where
"e_gaslimit_update == es_metadata_update o es_gaslimit_update"
abbreviation e_chainid_update where
"e_chainid_update == es_metadata_update o es_chainid_update"
abbreviation e_selfbalance_update where
"e_selfbalance_update == es_metadata_update o es_selfbalance_update"

abbreviation e_extcode_update where
"e_extcode_update == es_ext_update o es_extcode_update"
abbreviation e_balances_update where
"e_balances_update == es_ext_update o es_balances_update"
abbreviation e_acct_exists_update where
"e_acct_exists_update == es_ext_update o es_acct_exists_update"
abbreviation e_acct_live_update where
"e_acct_live_update == es_ext_update o es_acct_live_update"


definition dummy_estate :: estate where
"dummy_estate =
  \<lparr> es_core =
    \<lparr> es_memory = []
    , es_storage = \<lambda> _ . word_of_int 0  
    , es_flag = Executing
    , es_log = [] \<rparr>
  , es_resource =
    \<lparr> es_msize = word_of_int 0
    , es_gas = word_of_int 0 \<rparr>
  , es_data =
    \<lparr> es_codedata = []
    , es_calldata = []
    , es_returndata = [] \<rparr>
  , es_metadata =
    \<lparr> es_address = word_of_int 0
    , es_origin = word_of_int 0
    , es_caller = word_of_int 0
    , es_callvalue = word_of_int 0
    , es_gasprice = word_of_int 0
    , es_blockhash = word_of_int 0
    , es_coinbase = word_of_int 0
    , es_timestamp = word_of_int 0
    , es_blocknumber = word_of_int 0
    , es_difficulty = word_of_int 0
    , es_gaslimit = word_of_int 0
    , es_chainid = word_of_int 0
    , es_selfbalance = word_of_int 0 \<rparr>
  , es_ext =
    \<lparr> es_extcode = (\<lambda> _ . [])
    , es_balances = (\<lambda> _ . word_of_int 0)
    , es_acct_exists = (\<lambda> _ . False)
    , es_acct_live = (\<lambda> _ . False) \<rparr>
  \<rparr>"

(*
 * Helper functions for EVM instruction semantics
 *)

definition ssmallest :: "('a :: len) word" where
"ssmallest =
  word_of_int (2 ^ (LENGTH('a) - 1))"

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

fun modu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"modu' i1 i2 =
  (if i2 = word_of_int 0 then word_of_int 0
   else modulo_word_inst.modulo_word i1 i2)"

fun smodu' :: "('a :: len) word \<Rightarrow> 'a word \<Rightarrow> 'a word" where
"smodu' i1 i2 =
  (if sint i1 < 0 then
    times_word_inst.times_word (word_of_int (-1)) (modu' (word_abs i1) (word_abs i2))
   else modu' (word_abs i1) (word_abs i2))"

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

fun shl_many :: "('a :: len) word \<Rightarrow> int \<Rightarrow> 'a word" where
"shl_many w n =
  (if n \<le> 0 then w
   else shl_many (shiftl1 w) (n-1))"

fun shr_many :: "('a :: len) word \<Rightarrow> int \<Rightarrow> 'a word" where
"shr_many w n =
  (if n \<le> 0 then w
   else shr_many (shiftr1 w) (n-1))"

(* helper for pulling values from a list, adding default value if the end is reached *)

fun take_default :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"take_default n dfl ls =
  take n ls @ (replicate (n - length ls) dfl)"

(* get sz number of bytes starting at start*)

fun edata_gets :: "nat \<Rightarrow> nat \<Rightarrow> edata \<Rightarrow> 8 word list" where
"edata_gets start sz d =
  take_default sz (word_of_int 0) (drop start d)"

(* get bytes from start to (end - 1) *)
fun edata_gets_range :: "nat \<Rightarrow> nat \<Rightarrow> edata \<Rightarrow> 8 word list" where
"edata_gets_range start end d =
 (edata_gets start (end - start) d)"

(* Helper for calldataload.
   return eint of 32 bytes starting at byte n *)
fun bulk_load :: "nat \<Rightarrow> edata \<Rightarrow> eint" where
"bulk_load n d = word_rcat (edata_gets n 32 d)"

(* helper for calldatacopy, extcodecopy, returndatacopy *)
fun bulk_copy :: 
"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> edata \<Rightarrow> edata \<Rightarrow> edata" where
"bulk_copy to_idx from_idx n_bytes mem ext_data =
 (let loaded_bytes = take_default n_bytes (word_of_int 0) (drop from_idx ext_data) in
  take to_idx mem @ loaded_bytes @ drop (to_idx + n_bytes) mem)"

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
(*
definition ssmallest :: "('a :: len) word" where
"ssmallest =
 (Word.setBit (Word.word_of_int 0 :: 'a word) (size (Word.word_of_int 0 :: 'a word) - 1))"
*)


fun ei_sdiv :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sdiv i1 i2 s = (sdivd' i1 i2, s)"

fun ei_mod :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_mod i1 i2 s = (modu' i1 i2, s)"

fun ei_smod :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_smod i1 i2 s = 
  (smodu' i1 i2, s)"


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
  (semiring_bit_operations_word_inst.and_word i1 i2, s)"

fun ei_or :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_or i1 i2 s =
  (semiring_bit_operations_word_inst.or_word i1 i2, s)"

fun ei_xor :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_xor i1 i2 s =
  (semiring_bit_operations_word_inst.xor_word i1 i2, s)"

fun ei_not :: "eint \<Rightarrow> (estate, eint) State" where
"ei_not i1 s =
  (ring_bit_operations_word_inst.not_word i1, s)"

(* note that rsplit goes from most \<rightarrow> least significant digits
   (this is the opposite of how test_bit_word works)
*)
fun ei_byte :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_byte idx word s = 
  (if (uint idx) \<ge> 32 then (word_of_int 0, s)
   else
   (let bytes = (word_rsplit word :: 8 word list) in
    (ucast (bytes ! nat (uint idx)), s)))"

fun ei_shl :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_shl i1 i2 s = 
  (shl_many i1 (uint i2), s)"

fun ei_shr :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_shr i1 i2 s = 
  (shr_many i1 (uint i2), s)"

fun ei_sar :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_sar i1 i2 s = 
  (sshiftr i1 (nat (uint i2)), s)"

(*
 * Keccak256
 *)

fun ei_keccak256 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_keccak256 idx sz st =
  (Keccak.keccak (edata_gets (unat idx) (unat sz) (e_memory st)), st)"


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

fun ei_calldataload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_calldataload loc s = 
 (bulk_load (unat loc) (e_calldata s), s)"

fun ei_calldatasize :: "(estate, eint) State" where
"ei_calldatasize s = (word_of_int (int (length (e_calldata s))), s)"

fun ei_calldatacopy :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_calldatacopy to_idx from_idx n_bytes s = 
 ((), (s \<lparr> e_memory := bulk_copy (unat to_idx) (unat from_idx) (unat n_bytes)
                                 (e_memory s) (e_calldata s) \<rparr>))"

fun ei_codesize :: "(estate, eint) State" where
"ei_codesize s = (word_of_int (int (length (e_codedata s))), s)"

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
   then Keccak.keccak (edata_gets  0 (length (e_extcode s (ucast acctid)))
                                     (e_extcode s (ucast acctid)))
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

fun ei_pop :: "eint \<Rightarrow> (estate, unit) State" where
"ei_pop i1 s = ((), s)"

(* mload = get 32 bytes from given location in memory *)
(* TODO: make sure endianness is correct here *)
fun ei_mload :: "eint \<Rightarrow> (estate, eint) State" where
"ei_mload i1 s =
  (let bytes = edata_gets (nat (uint i1)) 32 (e_memory s)  in
  (word_rcat bytes, s))"

fun ei_mstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore idx value st =
  (let bytes = word_rsplit value :: 8 word list in
  ((),
   (st \<lparr> e_memory := bulk_copy (unat idx) 0 32 (e_memory st)
                               (bytes)  \<rparr>)))"

fun ei_mstore8 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_mstore8 idx value st =
  (let bytes = [(Word.ucast value) :: 8 word] in
  ((),
   (st \<lparr> e_memory := bulk_copy (unat idx) 0 32 (e_memory st) 
                               (bytes) \<rparr>)))"

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

(* edata_gets (unat start) (unat end - unat start) (e_memory st) *)

fun ei_log0 :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log0 start end st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log0 (edata_gets (unat start) (unat end - unat start) (e_memory st))] \<rparr>))"

fun ei_log1 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log1 start end t1 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log1 (edata_gets (unat start) (unat end - unat start) (e_memory st)) t1] \<rparr>))"

fun ei_log2 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log2 start end t1 t2 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log2 (edata_gets (unat start) (unat end - unat start) (e_memory st)) t1 t2] \<rparr>))"

fun ei_log3 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_log3 start end t1 t2 t3 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log3 (edata_gets (unat start) (unat end - unat start) (e_memory st)) t1 t2 t3] \<rparr>))"

fun ei_log4 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State"
  where
"ei_log4 start end t1 t2 t3 t4 st =
  (()
  , (st \<lparr> e_log := e_log st @ 
            [Log4 (edata_gets (unat start) (unat end - unat start) (e_memory st)) t1 t2 t3 t4] \<rparr>))"

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
  , (s \<lparr> e_flag := Create value (edata_gets (unat idx) (unat sz) (e_memory s)) \<rparr>))"
(* edata_gets (unat start) (unat end - unat start) (e_memory st) *)
fun ei_call :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_call gas target value in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := Call gas target value (edata_gets (unat in_idx) (unat in_sz) (e_memory s)) out_idx out_sz \<rparr> ))"

fun ei_callcode :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_callcode gas target value in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := CallCode gas target value (edata_gets (unat in_idx) (unat in_sz) (e_memory s)) out_idx out_sz \<rparr> ))"

fun ei_return :: "eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State" where
"ei_return idx sz s =
  (()
  , (s \<lparr> e_flag := Return (edata_gets (unat idx) (unat sz) (e_memory s)) \<rparr>))"

fun ei_delegatecall ::  "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_delegatecall gas target in_idx in_sz out_idx out_sz s =
  (word_of_int 0
  , (s \<lparr> e_flag := DelegateCall gas target (edata_gets (unat in_idx) (unat in_sz) (e_memory s)) out_idx out_sz \<rparr> ))"

fun ei_create2 :: "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_create2 value idx sz salt s =
  (word_of_int 0
  , (s \<lparr> e_flag := Create2 value (edata_gets (unat idx) (unat sz) (e_memory s)) salt \<rparr>))"

fun ei_staticcall ::  "eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State" where
"ei_staticcall gas target in_idx in_sz out_idx out_sz s =
  (word_of_int 0, 
  (s \<lparr> e_flag := StaticCall gas target (edata_gets (unat in_idx) (unat in_sz) (e_memory s)) out_idx out_sz \<rparr>))"
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


(*
 * dialect
 *)
definition yulBuiltinsMini :: "(estate, eint, unit) function_sig locals" where
"yulBuiltinsMini = make_locals
  [ (STR ''add'', mkBuiltin ei_add)
  , (STR ''mul'', mkBuiltin ei_mul)
  , (STR ''not'', mkBuiltin ei_not)
  , (STR ''lt'', mkBuiltin ei_lt)
  , (STR ''mstore'', mkBuiltin ei_mstore) ]"

(*
 * full dialect
 *)



definition yulBuiltins :: "(estate, eint, unit) function_sig locals" where
"yulBuiltins = make_locals
  [ (STR ''stop'', mkBuiltin ei_stop)
  , (STR ''add'', mkBuiltin ei_add)
  , (STR ''mul'', mkBuiltin ei_mul)
  , (STR ''sub'', mkBuiltin ei_sub)
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
  , (STR ''returndatasize'', mkBuiltin ei_returndatasize)
  , (STR ''returndatacopy'', mkBuiltin ei_returndatacopy)
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



definition EvmDialectMini :: "(estate, eint, unit) YulDialect" where
"EvmDialectMini =
  \<lparr> is_truthy = (\<lambda> x . (x \<noteq> word_of_int 0))
  , init_state = dummy_estate
  , default_val = word_of_int 0
  , builtins = yulBuiltinsMini
  , set_flag = 
      (\<lambda> f st . (st \<lparr> e_flag := f \<rparr>))
  , get_flag = e_flag \<rparr>"

definition EvmDialect :: "(estate, eint, unit) YulDialect" where
"EvmDialect =
  \<lparr> is_truthy = (\<lambda> x . (x \<noteq> word_of_int 0))
  , init_state = dummy_estate
  , default_val = word_of_int 0
  , builtins = yulBuiltins
  , set_flag = 
      (\<lambda> f st . (st \<lparr> e_flag := f \<rparr>))
  , get_flag = e_flag \<rparr>"


definition eval where "eval \<equiv> \<lambda> x . case (evalYul EvmDialect x 10000) of
  ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g)"

definition eval' where
"eval' n x = (case (evalYul EvmDialect x 10000) of
  ErrorResult x y \<Rightarrow> Inr x | YulResult g \<Rightarrow> Inl (global g))"

definition loop_yul :: "(eint, unit) YulStatement" where
"loop_yul \<equiv>
YUL{
    for { let x := 2 } lt(x, 10) { x := add(x, 1) } {
        mstore(mul(x, 5), mul(x, 0x1))
    }
}"



definition mulcheck_yul :: "(eint, unit) YulStatement" where
"mulcheck_yul \<equiv>
  YUL{ mul(2, 5) }
"

(*
value "
(case (eval loop_yul) of
  Inl x \<Rightarrow> edata_gets 0 72 (e_memory x))"
*)

definition dbg_info where
"dbg_info x =
  (case x of
    YulResult g \<Rightarrow> (vals g, locals g, cont g))"

definition final_mem_get where
"final_mem_get x =
  (case x of
    YulResult g \<Rightarrow> e_memory (global g))"

value "final_mem_get (evalYul EvmDialect loop_yul 100000)"

(*
 20 \<Rightarrow> ~8 copies of funs
*)

(* x is not getting updated by post ?! *)

definition not_yul :: "(eint, unit) YulStatement" where
"not_yul \<equiv>
YUL{
  mstore(0,not(1))
}"

value "final_mem_get (evalYul EvmDialect not_yul 10000)"


end
