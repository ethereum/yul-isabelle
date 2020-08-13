theory AbiTypes imports Complex_Main "HOL-Word.Word" "HOL-Library.Multiset" Ok

begin

(* based on
https://solidity.readthedocs.io/en/v0.5.12/abi-spec.html
*)

(* Abstract representation types of (structured) ABI data
   i.e., encoder input/decoder output *)
datatype abi_type =
  Tuint "nat"
  | Tsint "nat"
  | Taddr
  (* uint, sint : synonyms for uint256/sint256 *)
  | Tbool
  (* tfixed, ufixed : synonyms for 
     fixed(128, 18) and ufixed (128,18) *)
  | Tfixed "nat" "nat"
  | Tufixed "nat" "nat"
  (* fixed length bytes *)
  | Tfbytes "nat"
  (* function selector *)
  | Tfunction
  (* fixed length array *)
  | Tfarray "abi_type" "nat"
  | Ttuple "abi_type list"
  (* dynamically sized *)
  | Tbytes
  | Tstring
  | Tarray "abi_type"


definition max_u256 :: "nat" where
"max_u256 = 2 ^ 256 - 1"


(* for use in termination proofs (encoder/decoder)
   some of the termination proofs can't be completed automatically
   due to the size of the mutually recurisve functions involved
   so we use this as a measure *)

fun abi_type_measure :: "abi_type \<Rightarrow> nat"
and abi_type_list_measure :: "abi_type list \<Rightarrow> nat" where
"abi_type_measure (Ttuple ts) = 1 + abi_type_list_measure ts"
| "abi_type_measure (Tfarray t n) = 1 + n + n * (abi_type_measure t)"
| "abi_type_measure (Tarray t) = 1 + (1 + max_u256) +  (1 + max_u256) * abi_type_measure t" 
| "abi_type_measure _ = 1"

| "abi_type_list_measure [] = 1"
| "abi_type_list_measure (th#tt) =
    1 + abi_type_measure th + abi_type_list_measure tt"

(* count number of elements with zero-size encodings *)
fun abi_type_empties :: "abi_type \<Rightarrow> nat"
and abi_type_list_empties :: "abi_type list \<Rightarrow> nat" where
"abi_type_empties (Ttuple []) = 1"
| "abi_type_empties (Ttuple (th#tt)) = abi_type_list_empties (th#tt) + 1"
| "abi_type_empties (Tfarray t n) = n * (abi_type_empties t) + 1"
| "abi_type_empties _ = 0"

| "abi_type_list_empties [] = 0"
| "abi_type_list_empties (h#t) = abi_type_empties h + abi_type_list_empties t"

(* well-formedness of ABI types *)
fun abi_type_valid where
"abi_type_valid (Tuint n) = 
    (0 < n \<and> n \<le> 256 \<and> n mod 8 = 0)"
| "abi_type_valid (Tsint n) = 
    (0 < n \<and> n \<le> 256 \<and> n mod 8 = 0)"
| "abi_type_valid (Tfixed m n) =
  (8 \<le> m \<and> m \<le> 256 \<and> m mod 8 = 0 \<and> 0 < n \<and> n \<le> 80)"
| "abi_type_valid (Tufixed m n) =
  (8 \<le> m \<and> m \<le> 256 \<and> m mod 8 = 0 \<and> 0 < n \<and> n \<le> 80)"
| "abi_type_valid (Tfbytes m) =
  (0 < m \<and> m \<le> 32)"
| "abi_type_valid (Tfarray t _) = abi_type_valid t"
| "abi_type_valid (Ttuple ts) =
    list_all abi_type_valid ts"
| "abi_type_valid (Tarray t) = abi_type_valid t"
| "abi_type_valid _ = True"

fun abi_type_isdynamic :: "abi_type \<Rightarrow> bool" where
"abi_type_isdynamic (Tfarray t n) = (abi_type_isdynamic t)"
| "abi_type_isdynamic (Tbytes) = True"
| "abi_type_isdynamic (Tstring) = True"
| "abi_type_isdynamic (Tarray t) = True"
| "abi_type_isdynamic (Ttuple l) =
    list_ex abi_type_isdynamic l"
| "abi_type_isdynamic _ = False"

fun abi_type_isstatic :: "abi_type \<Rightarrow> bool" where
"abi_type_isstatic t = (\<not> (abi_type_isdynamic t))"

(* Abstract representation of (structured) ABI data *)
datatype abi_value =
  Vuint "nat" "int"
  | Vsint "nat" "int"
  | Vaddr "int"
  | Vbool "bool"
  | Vfixed "nat" "nat" "rat"
  | Vufixed "nat" "nat" "rat"
  (* tfixed, ufixed : synonyms for 
     fixed(128, 18) and ufixed (128,18) *)
  (* fixed length bytes *)
  | Vfbytes "nat" "8 word list"
  (* function selector
     first int is a 20-bit address
     second is a 4-byte selector *)
  | Vfunction "int" "int"
  (* fixed length array *)
  | Vfarray "abi_type" "nat" "abi_value list"
  | Vtuple "abi_type list" "abi_value list"
  (* dynamically sized *)
  | Vbytes "8 word list"
  | Vstring "char list" (* TODO: UTF8 support *)
  | Varray "abi_type" "abi_value list"

fun abi_get_type :: "abi_value \<Rightarrow> abi_type" where
"abi_get_type (Vuint n _) = Tuint n"
| "abi_get_type (Vsint n _) = Tsint n"
| "abi_get_type (Vaddr _) = Taddr"
| "abi_get_type (Vbool _) = Tbool"
| "abi_get_type (Vfixed m n _) = Tfixed m n"
| "abi_get_type (Vufixed m n _) = Tufixed m n"
| "abi_get_type (Vfbytes n _) = Tfbytes n"
| "abi_get_type (Vfunction _ _) = Tfunction"
| "abi_get_type (Vfarray t n _) = Tfarray t n"
| "abi_get_type (Vtuple ts _) = Ttuple ts"
| "abi_get_type (Vbytes _) = Tbytes"
| "abi_get_type (Vstring _) = Tstring"
| "abi_get_type (Varray t _) = Tarray t"

fun max_uint :: "nat \<Rightarrow> int" where
"max_uint n =
    ((2 :: int) ^ n) - 1"

(* two's complement sizes *)
fun min_sint :: "nat \<Rightarrow> int" where
"min_sint n =
  (-1) * ((2 :: int) ^ (n - 1))"

fun max_sint :: "nat \<Rightarrow> int" where
"max_sint n =
  ((2 :: int) ^ (n - 1)) - 1"

(* fixed-point numbers *)
fun int_of_fixed :: "nat \<Rightarrow> rat \<Rightarrow> int option" where
"int_of_fixed n r =
  (case Rat.quotient_of (r * (10 ^ n)) of
    (num, den) \<Rightarrow>
      (if den = 1 then Some num else None))"

(* validity checks on abstract data *)
definition uint_value_valid :: "nat \<Rightarrow> int \<Rightarrow> bool" where
"uint_value_valid n i = (0 \<le> i \<and> i \<le> max_uint n)"  

definition sint_value_valid :: "nat \<Rightarrow> int \<Rightarrow> bool" where
"sint_value_valid n i = (min_sint n \<le> i \<and> i \<le> max_sint n)"  

definition addr_value_valid :: "int \<Rightarrow> bool" where
"addr_value_valid i = uint_value_valid 160 i"

definition bool_value_valid :: "bool \<Rightarrow> bool" where
"bool_value_valid b = True"

definition fixed_value_valid :: "nat \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> bool" where
"fixed_value_valid m n r =
  (case int_of_fixed n r of
      None \<Rightarrow> False
      | Some i \<Rightarrow> min_sint m \<le> i \<and> i \<le> max_sint m)"

definition ufixed_value_valid :: "nat \<Rightarrow> nat \<Rightarrow> rat \<Rightarrow> bool" where
"ufixed_value_valid m n r =
  (case int_of_fixed n r of
      None \<Rightarrow> False
      | Some i \<Rightarrow> 0 \<le> i \<and> i \<le> max_uint m)"

definition fbytes_value_valid :: "nat \<Rightarrow> 8 word list \<Rightarrow> bool" where
"fbytes_value_valid n l = (length l = n)"

definition function_value_valid :: "int \<Rightarrow> int \<Rightarrow> bool" where
"function_value_valid i1 i2 = 
  (uint_value_valid 160 i1 \<and> uint_value_valid 32 i2)"

(* auxiliary checks for structured/recursive ABI data *)
definition farray_value_valid_aux :: "abi_type \<Rightarrow> nat \<Rightarrow> abi_value list \<Rightarrow> bool" where
"farray_value_valid_aux t n l = 
    (length l = n \<and> 
      list_all (\<lambda> v . abi_get_type v = t) l)"

definition tuple_value_valid_aux :: "abi_type list \<Rightarrow> abi_value list \<Rightarrow> bool" where
"tuple_value_valid_aux ts vs = (List.map abi_get_type vs = ts)"

definition bytes_value_valid :: "8 word list \<Rightarrow> bool" where
"bytes_value_valid bs = uint_value_valid 256 (int (length bs))"

definition string_value_valid :: "char list \<Rightarrow> bool" where
"string_value_valid s = uint_value_valid 256 (int (length s))"

definition array_value_valid_aux :: "abi_type \<Rightarrow> abi_value list \<Rightarrow> bool" where
"array_value_valid_aux t l = 
  (uint_value_valid 256 (int (length l)) \<and> list_all (\<lambda> v . abi_get_type v = t) l)"

(* additional checks beyond typechecking to ensure
   values are permitted *)
fun abi_value_valid_aux :: "abi_value \<Rightarrow> bool" where
"abi_value_valid_aux (Vuint n i) = uint_value_valid n i"
| "abi_value_valid_aux (Vsint n i) = sint_value_valid n i"
| "abi_value_valid_aux (Vaddr i) = addr_value_valid i"
| "abi_value_valid_aux (Vbool b) = bool_value_valid b"
| "abi_value_valid_aux (Vfixed m n r) = fixed_value_valid m n r"
| "abi_value_valid_aux (Vufixed m n r) = ufixed_value_valid m n r"
| "abi_value_valid_aux (Vfbytes n l) = fbytes_value_valid n l"
| "abi_value_valid_aux (Vfunction i1 i2) = function_value_valid i1 i2"
| "abi_value_valid_aux (Vfarray t n l) =
    (farray_value_valid_aux t n l \<and>
     list_all abi_value_valid_aux l)"
| "abi_value_valid_aux (Vtuple ts vs) =
    (tuple_value_valid_aux ts vs \<and>
     list_all abi_value_valid_aux vs)"
| "abi_value_valid_aux (Vbytes bs) = bytes_value_valid bs"
| "abi_value_valid_aux (Vstring s) = string_value_valid s"
| "abi_value_valid_aux (Varray t l) =
  (array_value_valid_aux t l \<and>
   list_all abi_value_valid_aux l)"

fun abi_value_valid :: "abi_value \<Rightarrow> bool" where
"abi_value_valid v =
  (abi_type_valid (abi_get_type v) \<and>
   abi_value_valid_aux v)"

definition list_sum :: "int list \<Rightarrow> int" where
"list_sum xs = List.foldl (+) 0 xs"

(* foldr is easier to reason about *)
definition list_sumr :: "int list \<Rightarrow> int" where
"list_sumr xs = List.foldr (+) xs 0"

(* size in bytes of a (static) ABI datum *)
(* TODO: figure out how function decoding is supposed to work. *)
fun abi_static_size :: "abi_type \<Rightarrow> int" where
"abi_static_size (Tuint n) = 32"
| "abi_static_size (Tsint n) = 32"
| "abi_static_size (Taddr) = 32"
| "abi_static_size (Tbool) = 32"
| "abi_static_size (Tfixed _ _) = 32"
| "abi_static_size (Tufixed _ _) = 32"
| "abi_static_size (Tfbytes _) = 32"
| "abi_static_size (Tfunction) = 32"
| "abi_static_size (Tfarray t n) =
    n * (abi_static_size t)"
| "abi_static_size (Ttuple ts) =
    List.foldl (\<lambda> (a :: int) (b :: int) . (a + b))
               0
               (List.map abi_static_size ts)"
(* the caller of this function should check that we are static *)
| "abi_static_size _ = 0"

(* 
  Upper bound on encoded size of (canonically-encoded) dynamic ABI data
  This is necessary because if the canonically-encoded size > ~2^256,
  A "compressed" non-canonical encoding may exist, but not a canonical one.
  See AbincodeCorrect.thy for details
  
  This calculation is designed to be simpler than a precise calculation of
  encoded length. This is important because it forms part of the specification
  (shows up as a premise to encoder-correctness theorems).
  We assume everything needs a 32-byte head in addition to its body encoding.
*)
fun abi_dynamic_size_bound :: "abi_value \<Rightarrow> int" where
"abi_dynamic_size_bound v =
  (if abi_type_isstatic (abi_get_type v) then abi_static_size (abi_get_type v)
   else (case v of
          Vfarray t n l \<Rightarrow> n * 32 + list_sum (map abi_dynamic_size_bound l)
          | Vtuple ts vs \<Rightarrow> (length vs * 32) + list_sum (map abi_dynamic_size_bound vs)
          | Varray t l \<Rightarrow> 32 + (length l * 32) + list_sum (map abi_dynamic_size_bound l)
          | Vbytes bs \<Rightarrow> 32 + length bs + 32
          | Vstring s \<Rightarrow> 32 + length s + 32))" (* extra 32 at end is for byte padding *)

(* this should capture the exact size of dynamic structures
   its correctness hasn't been proven and in practice we use the upper bound given above
   the implementation is retained partly to demonstrate how much simpler the
   upper-bound calculation is. *)
fun abi_dynamic_size_precise :: "abi_value \<Rightarrow> int" where
"abi_dynamic_size_precise v =
  (if abi_type_isstatic (abi_get_type v) then abi_static_size (abi_get_type v)
   else (case v of
          Vfarray t n l \<Rightarrow> n * 32 + list_sum (map abi_dynamic_size_precise l)
          | Vtuple ts vs \<Rightarrow> (list_sum (map (abi_static_size o abi_get_type) (filter (abi_type_isstatic o abi_get_type) vs))) + 
                             list_sum (map (\<lambda> x . 32 + abi_dynamic_size_precise x) (filter (abi_type_isdynamic o abi_get_type) vs))
          | Varray t l \<Rightarrow> 
              (if abi_type_isstatic t then 32 + list_sum (map abi_dynamic_size_precise l)
                                      else  32 + (length l * 32) + list_sum (map abi_dynamic_size_precise l))
          | Vbytes bs \<Rightarrow> 32 + length bs
          | Vstring s \<Rightarrow> 32 + length s))"



end