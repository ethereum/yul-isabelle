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
fun abi_type_measure :: "abi_type \<Rightarrow> nat"
and abi_type_list_measure :: "abi_type list \<Rightarrow> nat" where
"abi_type_measure (Ttuple ts) = 2 + abi_type_list_measure ts"
| "abi_type_measure (Tfarray t n) = 2 + n + (abi_type_measure t)"
| "abi_type_measure (Tarray t) = 2 + abi_type_measure t" (* curious about this one *)
| "abi_type_measure _ = 1"

| "abi_type_list_measure [] = 0"
| "abi_type_list_measure (th#tt) =
    abi_type_measure th + abi_type_list_measure tt"

(* count number of elements with zero-size encodings *)
fun abi_type_empties :: "abi_type \<Rightarrow> nat"
and abi_type_list_empties :: "abi_type list \<Rightarrow> nat" where
"abi_type_empties (Ttuple []) = 1"
| "abi_type_empties (Ttuple (th#tt)) = abi_type_list_empties (th#tt)"
| "abi_type_empties (Tfarray t n) = n * (abi_type_empties t)"
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

(* NB the caller of these functions will pass in a long
   enough list *)
fun decode_uint :: "8 word list \<Rightarrow> int" where
"decode_uint l =
  (Word.uint (Word.word_rcat (take 32 l) :: 256 word))"

fun decode_sint :: "8 word list \<Rightarrow> int" where
"decode_sint l =
  (Word.sint (Word.word_rcat (take 32 l) :: 256 word))"

fun decode_bool :: "8 word list \<Rightarrow> bool option" where
"decode_bool l =
  (let i = decode_uint l in
   (if i = 0 then Some False
              else if i = 1 then Some True
              else None))"

fun decode_ufixed :: "nat \<Rightarrow> 8 word list \<Rightarrow> rat" where
"decode_ufixed n l =
  (let i = decode_uint l in (Rat.of_int i / (10 ^ n)))"

fun decode_fixed :: "nat \<Rightarrow> 8 word list \<Rightarrow> rat" where
"decode_fixed n l =
  (let i = decode_sint l in (Rat.of_int i / (10 ^ n)))"

(* extract byte strings of known length *)
fun decode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"decode_fbytes n l = (take n l)"

(* here, again, we assume we have been passed a correct length byte string
   other than booleans, we aren't doing value checks here *)
(* TODO: enforce that correct size word list was passed in?
   otherwise we risk discarding data *)
function (sequential) decode_static_nocheck :: "abi_type \<Rightarrow> 8 word list \<Rightarrow> abi_value option" 
and decode_static_nocheck_arr :: "abi_type \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> abi_value list option"
and decode_static_nocheck_tup :: "abi_type list \<Rightarrow> 8 word list \<Rightarrow> abi_value list option" where
"decode_static_nocheck (Tuint n) l =
   Some (Vuint n (decode_uint l))"
| "decode_static_nocheck (Tsint n) l =
   Some (Vsint n (decode_uint l))"
| "decode_static_nocheck Taddr l =
   Some (Vaddr (decode_uint l))"
| "decode_static_nocheck Tbool l =
   (case decode_bool l of
      None \<Rightarrow> None
      | Some b \<Rightarrow> Some (Vbool b))"
| "decode_static_nocheck (Tfixed m n) l =
    Some (Vfixed m n (decode_fixed m l))"
| "decode_static_nocheck (Tufixed m n) l =
    Some (Vufixed m n (decode_ufixed m l))"
| "decode_static_nocheck (Tfbytes n) l =
    Some (Vfbytes n (decode_fbytes n l))"
| "decode_static_nocheck (Tfarray t n) l =
  (case decode_static_nocheck_arr t n l of
    None \<Rightarrow> None
    | Some vs \<Rightarrow> Some (Vfarray t n vs))"
| "decode_static_nocheck (Ttuple ts) l = 
  (case decode_static_nocheck_tup ts l of
    None \<Rightarrow> None
    | Some vs \<Rightarrow> Some (Vtuple ts vs))"
| "decode_static_nocheck _ _ = None"

| "decode_static_nocheck_arr t 0 l = Some []"
| "decode_static_nocheck_arr t (Suc n) l =
    (case decode_static_nocheck t 
                   (take (nat (abi_static_size t)) l) of
      None \<Rightarrow> None
      | Some v \<Rightarrow> (case decode_static_nocheck_arr t n
                       (drop (nat (abi_static_size t)) l) of
          None \<Rightarrow> None
          | Some vs \<Rightarrow> Some (v#vs)))"

| "decode_static_nocheck_tup [] l = Some []"
| "decode_static_nocheck_tup (t#ts) l =
    (case decode_static_nocheck t 
                   (take (nat (abi_static_size t)) l) of
      None \<Rightarrow> None
      | Some v \<Rightarrow> (case decode_static_nocheck_tup ts 
                       (drop (nat (abi_static_size t)) l) of
          None \<Rightarrow> None
          | Some vs \<Rightarrow> Some (v#vs)))"
  by pat_completeness auto
(*
termination
apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> abi_type_measure t + length l
      | Inr (Inl (t, n, l)) \<Rightarrow> abi_type_measure t + n + length l + 1
      | Inr (Inr (ts, l)) \<Rightarrow> abi_type_list_measure ts + length l + 1))")
apply(auto)
  apply(case_tac t) apply(auto)
  done
*)
termination
  sorry
(*
apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> abi_type_empties t + length l + 1
      | Inr (Inl (t, n, l)) \<Rightarrow> (n * abi_type_empties t) + length l 
      | Inr (Inr (ts, l)) \<Rightarrow> abi_type_list_empties ts + length l))")       
        apply(auto)
      apply(case_tac ts, auto)
  apply(case_tac l, auto)
  done
*)

fun bytes_to_string :: "8 word list \<Rightarrow> char list" where
"bytes_to_string bs =
  List.map (\<lambda> b . char_of_integer (integer_of_int (Word.uint b))) bs"

(* TODO: consider returning a nat everywhere to make it easier to keep track
   of how much we have read, for the purposes of tuple indexing *)
function decode_nocheck :: "abi_type \<Rightarrow> 8 word list \<Rightarrow> (abi_value * 8 word list) option"
and decode_dyn_nocheck_array :: "abi_type \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> (abi_value list * 8 word list) option"
(* returned nat is the length of all the heads; input nat is running count of head length. *)
and decode_dyn_nocheck_tuple_heads :: "abi_type list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 
                ((abi_value + (nat * abi_type)) list * nat * 8 word list) option"
(* NB the nat parameter is an index of how many bytes into our overall tuple encoding we are *)
and decode_dyn_nocheck_tuple_tails :: "(abi_value + (nat * abi_type)) list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 
                (abi_value list * 8 word list) option"
  where
"decode_nocheck t l =
  (if abi_type_isstatic t
    then
      if length l < nat (abi_static_size t) then None
      else (case decode_static_nocheck t l of
            None \<Rightarrow> None
            | Some v \<Rightarrow> Some (v, drop (nat (abi_static_size t)) l))
   else
    (case t of
      Tfarray t n \<Rightarrow>
        (case decode_dyn_nocheck_array t n l of
          None \<Rightarrow> None
          | Some (vs, l') \<Rightarrow> Some (Vfarray t n vs, l'))
      | Tarray t \<Rightarrow>
       if length l < 32 then None
        else let n = nat (decode_uint (take 32 l)) in
        (case decode_dyn_nocheck_array t n l of
          None \<Rightarrow> None
          | Some (vs, l') \<Rightarrow> Some (Varray t vs, l'))
      | Ttuple ts \<Rightarrow>
        (case decode_dyn_nocheck_tuple_heads ts 0 l of
          None \<Rightarrow> None
          | Some (tails, n, l') \<Rightarrow>
            (case decode_dyn_nocheck_tuple_tails tails n l' of
              None \<Rightarrow> None
              | Some (vs, l'') \<Rightarrow> Some (Vtuple ts vs, l'')))
      | Tbytes \<Rightarrow>
        if length l < 32 then None
        else let sz = nat (decode_uint (take 32 l)) in
             if length (drop 32 l) < sz then None
             else Some (Vbytes (take sz (drop 32 l)), (drop (sz + 32) l))
      | Tstring \<Rightarrow> 
        if length l < 32 then None
        else let sz = nat (decode_uint (take 32 l)) in
             if length (drop 32 l) < sz then None
             else Some (Vstring (bytes_to_string (take sz (drop 32 l))), drop (sz + 32) l)
      | _ \<Rightarrow> None))"

(*| "decode_dyn_nocheck_array t 0 [] = Some ([], [])"
| "decode_dyn_nocheck_array t n [] = None" *)
| "decode_dyn_nocheck_array t 0 l = Some ([], l)"
| "decode_dyn_nocheck_array t (Suc n') l =
    (case decode_nocheck t l of
      None \<Rightarrow> None
      | Some (v, l') \<Rightarrow> (case decode_dyn_nocheck_array t n' l' of
                          None \<Rightarrow> None
                          | Some (vt, l'') \<Rightarrow> Some (v#vt, l'')))"

(* need to do something with updating indices here *)
(* Also. how do we deal with ill-formed data such that the tails
and heads overlap? *)
| "decode_dyn_nocheck_tuple_heads [] n l = Some ([], n, l)"
| "decode_dyn_nocheck_tuple_heads (th#tt) n l =
    (if abi_type_isstatic th
      then (case decode_nocheck th l of
        None \<Rightarrow> None
        | Some (v, l') \<Rightarrow>
          (case decode_dyn_nocheck_tuple_heads tt (n + nat (abi_static_size th))  l' of
            None \<Rightarrow> None
            | Some (tails, n', l'') \<Rightarrow> Some (Inl v # tails, n', l'')))
    else
      (if length l < 32 then None
       else let sz = nat (decode_uint (take 32 l)) in
            (case decode_dyn_nocheck_tuple_heads tt (n + 32) (drop 32 l) of
              None \<Rightarrow> None
              | Some (tails, n', l') \<Rightarrow> Some (Inr (sz, th) # tails, n', l'))))"

| "decode_dyn_nocheck_tuple_tails [] _ l = Some ([], l)"
| "decode_dyn_nocheck_tuple_tails (Inl v # t) n l =
   (case decode_dyn_nocheck_tuple_tails t n l of
      None \<Rightarrow> None
      | Some (vs, l') \<Rightarrow> Some (v#vs, l'))"
(* is it too strict to force offset to equal n? *)
| "decode_dyn_nocheck_tuple_tails (Inr (offset, typ) # t) n l =
  (if offset \<noteq> n then None
   else (case decode_nocheck typ l of
          None \<Rightarrow> None
          | Some (v, l') \<Rightarrow>
            let n' = n + (length l - length l') in
            (case decode_dyn_nocheck_tuple_tails t n' l' of
              None \<Rightarrow> None
              | Some (vs, l'') \<Rightarrow> Some (v#vs, l''))))"
  by pat_completeness auto
termination
  sorry
(*
  apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (Inl (t, l)) \<Rightarrow> abi_type_measure t + length l
      | Inl (Inr (t, n, l)) \<Rightarrow> abi_type_measure t + n + length l + 1
      | Inr (Inl (ts, n, l)) \<Rightarrow> abi_type_list_measure ts + length l + 1
      | Inr (Inr (tls, n, l)) \<Rightarrow>  length l + 1))")
              apply(fastforce)
             apply(fastforce)
            apply(fastforce)
  apply(clarsimp)
apply(fastforce)
              apply(auto)
  apply(case_tac l)
*)

(* head = offset at which tail can be found
   tail = encoding of dynamic object *)

(* functions: TODO *)

(* fun abi_encode ::
    abi_value \<Rightarrow> 8 word list option *)
(* fun abi_decode ::
    8 word list \<Rightarrow> abi_value option *)

(* need an ABI types data type*)
(* do we represent these here as words, or
   as abstract types? *)

(*
datatype AbiValueWord =
  Uint "nat" "256 word"
  | Sint "nat" "256 word"
  | Addr "160 word"
  (* uint, sint : synonyms for uint256/sint256 *)
  | Bl "8 word"
  | Fixed "nat" "nat" "256 word"
  | Ufixed "nat" "nat" "256 word"
  | Bytes "nat" "256 word"
  | Function "160 word" "32 word"
*)

end