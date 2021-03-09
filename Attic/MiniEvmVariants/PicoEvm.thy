theory PicoEvm
  imports "../YulDialect"
    "HOL-Library.Word"
    "../Keccak/Keccak"
    "../Word_Lib/Bits_Int"
    "../YulSemanticsSingleStep"
begin

(* Experiments in trying to find performance bottleneck in EVM *)

(* necessary instructions (for loop, exp)
  - not
  - mstore
  - exp
  - add
  - mul
*)

type_synonym edata = "eint \<Rightarrow> 8 word"

record estate_core =
  (* Memory is byte-indexed *)
  (* e_memory :: "8 word list" *)
  e_memory :: "edata"
  (* Storage is word-indexed *)
  e_storage :: "eint \<Rightarrow> eint"
  e_flag :: YulFlag

(* helpers *)

fun byte_list_to_edata :: "8 word list \<Rightarrow> edata" where
"byte_list_to_edata l n =
  (if unat n < length l then l ! unat n
   else 0)"

fun edata_gets :: "nat \<Rightarrow> nat \<Rightarrow> edata \<Rightarrow> 8 word list" where
"edata_gets start 0 d = []"
| "edata_gets start sz d =
   d (word_of_int (int start)) # edata_gets (start + 1) (sz - 1) d"

(* insts *)
fun bulk_copy :: 
"nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> edata \<Rightarrow> edata \<Rightarrow> edata" where
"bulk_copy to_idx from_idx n_bytes mem ext_data =
 (\<lambda> idx .
  (if to_idx \<le> unat idx \<and> unat idx < to_idx + n_bytes
   then ext_data (word_of_int (int (from_idx + (unat idx - to_idx))))
   else mem idx))"

fun ei_add :: "eint \<Rightarrow> eint \<Rightarrow> (estate_core, eint) State" where
"ei_add i1 i2 s = (plus_word_inst.plus_word i1 i2, s)"

fun ei_mul :: "eint \<Rightarrow> eint \<Rightarrow> (estate_core, eint) State" where
"ei_mul i1 i2 s = (times_word_inst.times_word i1 i2, s)"

fun ei_not :: "eint \<Rightarrow> (estate_core, eint) State" where
"ei_not i1 s =
  (ring_bit_operations_word_inst.not_word i1, s)"

fun ei_lt :: "eint \<Rightarrow> eint \<Rightarrow> (estate_core, eint) State" where
"ei_lt i1 i2 s =
  (if uint i1 < uint i2
   then (word_of_int 1, s)
   else (word_of_int 0, s))"

fun ei_mstore :: "eint \<Rightarrow> eint \<Rightarrow> (estate_core, unit) State" where
"ei_mstore idx value st =
  (let bytes = word_rsplit value :: 8 word list in
  ((),
   (st \<lparr> e_memory := bulk_copy (unat idx) 0 32 (e_memory st)
                               (byte_list_to_edata bytes)  \<rparr>)))"

(*
 * dialect
 *)
definition yulBuiltins :: "(estate_core, eint, unit) function_sig locals" where
"yulBuiltins = make_locals
  [ (STR ''add'', mkBuiltin ei_add)
  , (STR ''mul'', mkBuiltin ei_mul)
  , (STR ''not'', mkBuiltin ei_not)
  , (STR ''lt'', mkBuiltin ei_lt)
  , (STR ''mstore'', mkBuiltin ei_mstore) ]"

definition dummy_estate :: estate_core where
"dummy_estate =
  \<lparr> e_memory = \<lambda> _ . word_of_int 0
  , e_storage = \<lambda> _ . word_of_int 0  
  , e_flag = Executing \<rparr>"


definition EvmDialect :: "(estate_core, eint, unit) YulDialect" where
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

value "
(case (eval loop_yul) of
  Inl x \<Rightarrow> edata_gets 0 72 (e_memory x))"

definition not_yul :: "(eint, unit) YulStatement" where
"not_yul \<equiv>
YUL{
  mstore(0,not(1))
}"

value "
(case (eval not_yul) of
  Inl x \<Rightarrow> edata_gets 0 32 (e_memory x))"




end