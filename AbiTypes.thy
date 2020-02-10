theory AbiTypes imports Complex_Main "HOL-Word.Word" "HOL-Library.Multiset"

begin

(* based on
https://solidity.readthedocs.io/en/v0.5.12/abi-spec.html
*)

value "Word.slice 0 ((word_of_int 2) :: 4 word) :: 1 word"

datatype abi_type =
  Tuint "nat"
  | Tsint "nat"
  | Taddr
  (* uint, sint : synonyms for uint256/sint256 *)
  | Tbool
  | Tfixed "nat" "nat"
  | Tufixed "nat" "nat"
  (* tfixed, ufixed : synonyms for 
     fixed(128, 18) and ufixed (128,18) *)
  (* fixed length bytes *)
  | Tfbytes "nat"
  | Tfunction
  (* fixed length array *)
  | Tfarray "abi_type" "nat"
  | Ttuple "abi_type list"
  (* dynamically sized *)
  | Tbytes
  | Tstring
  | Tarray "abi_type"

(* for use in termination proofs
   some of the termination proofs can't be completed automatically
   due to the size of the mutually recurisve functions involved. *)

definition max_u256 :: "nat" where
"max_u256 = 2 ^ 256 - 1"

(* do not use this outside of proofs - it will blow up. *)
fun abi_type_measure :: "abi_type \<Rightarrow> nat"
and abi_type_list_measure :: "abi_type list \<Rightarrow> nat" where
"abi_type_measure (Ttuple ts) = 1 + abi_type_list_measure ts"
| "abi_type_measure (Tfarray t n) = 1 + n + (abi_type_measure t)"
| "abi_type_measure (Tarray t) = 1 + max_u256 + abi_type_measure t" (* curious about this one *)
| "abi_type_measure _ = 1"

| "abi_type_list_measure [] = 1"
| "abi_type_list_measure (th#tt) =
    abi_type_measure th + abi_type_list_measure tt + 1"


(* count number of elements with zero-size encodings *)
fun abi_type_empties :: "abi_type \<Rightarrow> nat"
and abi_type_list_empties :: "abi_type list \<Rightarrow> nat" where
"abi_type_empties (Ttuple []) = 1"
| "abi_type_empties (Ttuple (th#tt)) = abi_type_list_empties (th#tt) + 1"
| "abi_type_empties (Tfarray t n) = n * (abi_type_empties t) + 1"
| "abi_type_empties _ = 0"

| "abi_type_list_empties [] = 0"
| "abi_type_list_empties (h#t) = abi_type_empties h + abi_type_list_empties t"
  
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

(* additional checks beyond type well-formedness to ensure
   values are permitted *)
fun abi_value_valid_aux :: "abi_value \<Rightarrow> bool" where
"abi_value_valid_aux (Vuint n i) =
  (0 \<le> i \<and> i \<le> max_uint n)"
| "abi_value_valid_aux (Vsint n i) =
  (min_sint n \<le> i \<and> i \<le> max_sint n)"
| "abi_value_valid_aux (Vaddr i) =
  (0 \<le> i \<and> i \<le> max_uint 160)"
| "abi_value_valid_aux (Vbool b) = True"
| "abi_value_valid_aux (Vfixed m n r) =
    (case int_of_fixed n r of
      None \<Rightarrow> False
      | Some i \<Rightarrow> min_sint m \<le> i \<and> i \<le> max_sint m)"
| "abi_value_valid_aux (Vufixed m n r) =
    (case int_of_fixed n r of
      None \<Rightarrow> False
      | Some i \<Rightarrow> 0 \<le> i \<and> i \<le> max_uint m)"
| "abi_value_valid_aux (Vfbytes n l) =
    (length l = n)"
| "abi_value_valid_aux (Vfunction i1 i2) =
    (0 \<le> i1 \<and> i1 \<le> max_uint 160 \<and>
     0 \<le> i2 \<and> i2 \<le> max_uint 32)"
| "abi_value_valid_aux (Vfarray t n l) =
    (length l = n \<and> 
      list_all (\<lambda> v . abi_get_type v = t) l)"
| "abi_value_valid_aux (Vtuple ts vs) =
    (List.map abi_get_type vs = ts)"
(* in practice are there any restrictions on bytes? *)
| "abi_value_valid_aux (Vbytes _) = True"
| "abi_value_valid_aux (Vstring _) = True"
| "abi_value_valid_aux (Varray t l) =
    list_all (\<lambda> v . abi_get_type v = t) l"


fun abi_value_valid :: "abi_value \<Rightarrow> bool" where
"abi_value_valid v =
  (abi_type_valid (abi_get_type v) \<and>
   abi_value_valid_aux v)"

(* helpers for static value decoding *)
(* getting the size in bytes of a (presumed static) ABI element *)
(* TODO: figure out how function decoding is supposed to work. *)
(* TODO: enforce somewhere that sizes are less than 2 ^ 256 *)
fun abi_static_size :: "abi_type \<Rightarrow> int" where
"abi_static_size (Tuint n) = 32"
| "abi_static_size (Tsint n) = 32"
| "abi_static_size (Taddr) = 32"
| "abi_static_size (Tbool) = 32"
| "abi_static_size (Tfixed _ _) = 32"
| "abi_static_size (Tufixed _ _) = 32"
| "abi_static_size (Tfbytes _) = 32"
| "abi_static_size (Tfarray t n) =
    n * (abi_static_size t)"
| "abi_static_size (Ttuple ts) =
    List.foldl (\<lambda> (a :: int) (b :: int) . (a + b))
               0
               (List.map abi_static_size ts)"
(* the caller of this function should check that we are static *)
| "abi_static_size _ = 0"



end