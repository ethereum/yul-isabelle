theory AbiDecode imports AbiTypes Hex Ok
begin

(* An decoder for the Solidity ABI.
   It supports decoding from all byte-strings representing
   valid Solidity-ABI encoded data
   (not limited to canonical encodings) *)

(* Functions for decoding basic data-types.*)
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

(* bytes, fbytes, and strings will be padded to multiples of
   32 bytes. skip_padding skips this padding. *)
fun skip_padding :: "nat \<Rightarrow> nat" where
"skip_padding n =
  (case divmod_nat n 32 of
    (_, 0) \<Rightarrow> n
    | (_, rem) \<Rightarrow> n + 32 - rem)"

(* Ensure padding is zeroes.
   This is necessary for static encoder and static
   decoder to be inverses. *)
fun check_padding :: "nat \<Rightarrow> 8 word list \<Rightarrow> bool" where
"check_padding n l =
  (let p = skip_padding n in
  ((p \<le> length l) \<and> (drop n (take p l) = replicate (p - n) (word_of_int 0))))" 


(* Extract byte strings of known length *)
fun decode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list option" where
"decode_fbytes n l =
  (if check_padding n l then Some (take n l)
   else None)"


fun decode_function_sel :: "8 word list \<Rightarrow> (int * int) option" where
"decode_function_sel bs =
  (if check_padding 24 bs then
      Some (Word.uint (Word.word_rcat (take 20 bs) :: 160 word),
            Word.uint (Word.word_rcat (take 4 (drop 20 bs)) :: 32 word))
   else None)"

fun bytes_to_string :: "8 word list \<Rightarrow> char list" where
"bytes_to_string bs =
  List.map (\<lambda> b . char_of_integer (integer_of_int (Word.uint b))) bs"

(* Lemma for decoder termination *)
lemma abi_type_list_measure_replicate :
  "\<And> t . abi_type_list_measure (replicate n t)
           =  1 + n + (n * abi_type_measure t)"
proof(induction n)
  case 0
  then show ?case
    by(simp)
next
  case (Suc n)
  then show ?case 
    by(simp)
qed

(* Construct decoder error messages *)
fun decode_err :: "char list \<Rightarrow> (int * 8 word list) \<Rightarrow> char list"
  where
"decode_err s (ix, l) =
  s @ '' at byte '' @ decwrite (nat ix) @ '' of '' @ decwrite (length l) @ ''.''"

(* Decoder for static data *)
function (sequential) decode_static :: "abi_type \<Rightarrow> (int * 8 word list) \<Rightarrow> abi_value orerror" 
and decode_static_tup :: "abi_type list \<Rightarrow> (int * 8 word list) \<Rightarrow> abi_value list orerror" where
"decode_static (Tuint n) (ix, l) =
   (let l' = drop (nat ix) l in
   (let res = decode_uint l' in
    (if uint_value_valid n res then Ok (Vuint n res)
     else Err (decode_err ''Invalid uint'' (ix, l)))))"
| "decode_static (Tsint n) (ix, l) =
   (let l' = drop (nat ix) l in
   (let res = decode_sint l' in
    (if sint_value_valid n res then Ok (Vsint n res)
     else Err (decode_err ''Invalid sint'' (ix, l)))))"
| "decode_static Taddr (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_uint l' in
    (if addr_value_valid res then Ok (Vaddr res)
     else Err (decode_err ''Invalid address'' (ix, l)))))"
| "decode_static Tbool (ix, l) =
  (let l' = drop (nat ix) l in
   (case decode_bool l' of
      None \<Rightarrow> Err (decode_err ''Invalid bool'' (ix, l))
      | Some b \<Rightarrow> Ok (Vbool b)))"
| "decode_static (Tfixed m n) (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_fixed n l' in
    (if fixed_value_valid m n res then Ok (Vfixed m n res)
     else Err (decode_err ''Invalid fixed'' (ix, l)))))"
| "decode_static (Tufixed m n) (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_ufixed n l' in
    (if ufixed_value_valid m n res then Ok (Vufixed m n res)
     else Err (decode_err ''Invalid ufixed'' (ix, l)))))"
| "decode_static (Tfbytes n) (ix, l) =
  (let l' = drop (nat ix) l in
   (case decode_fbytes n l' of
      Some res \<Rightarrow> (if fbytes_value_valid n res then Ok (Vfbytes n res)
                    else Err (decode_err ''Invalid fbytes'' (ix, l)))
      | None \<Rightarrow> Err (decode_err ''invalid fbytes padding'' (ix, l))))"

| "decode_static (Tfunction) (ix, l) =
    (let l' = drop (nat ix) l in
      (case decode_function_sel l' of
        Some (i, j) \<Rightarrow> (if function_value_valid i j then Ok (Vfunction i j)
                        else Err (decode_err ''Invalid function'' (ix, l)))
        | None \<Rightarrow> Err (decode_err ''invalid function padding'' (ix, l))))"
    
| "decode_static (Tfarray t n) (ix, l) =
  (case decode_static_tup (List.replicate n t) (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok vs \<Rightarrow> 
        (if farray_value_valid_aux t n vs then Ok (Vfarray t n vs)
         else Err (decode_err ''Invalid farray'' (ix, l))))"
| "decode_static (Ttuple ts) (ix, l) = 
  (case decode_static_tup ts (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok vs \<Rightarrow> 
      (if tuple_value_valid_aux ts vs then Ok (Vtuple ts vs)
       else Err (decode_err ''Invalid tuple'' (ix, l))))"
| "decode_static _ (ix, l) = Err (decode_err ''Ran static parser on dynamic array'' (ix, l))"
| "decode_static_tup [] (ix, l) = Ok []"
| "decode_static_tup (t#ts) (ix, l) =
    (case decode_static t (ix, l) of
      Err s \<Rightarrow> Err s
      | Ok v \<Rightarrow> (case decode_static_tup ts 
                       (ix + (abi_static_size t), l) of
          Err s \<Rightarrow> Err s
          | Ok vs \<Rightarrow> Ok (v#vs)))"
  by pat_completeness auto

termination
proof(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> 1 + abi_type_measure t
      | Inr (ts, l) \<Rightarrow> abi_type_list_measure ts))"; (auto; fail)?)
  show "\<And>t n ix l.
       (Inr (replicate n t, ix, l), Inl (Tfarray t n, ix, l))
       \<in> measure (\<lambda>x. case x of Inl (t, l) \<Rightarrow> 1 + abi_type_measure t 
                              | Inr (ts, l) \<Rightarrow> abi_type_list_measure ts)"
    by(auto simp add:abi_type_list_measure_replicate)
next
  fix t ts
  show "\<And> ix l.
       (Inl (t, ix, l), Inr (t # ts, ix, l))
       \<in> measure (\<lambda>x. case x of Inl (t, l) \<Rightarrow> 1 + abi_type_measure t 
                              | Inr (ts, l) \<Rightarrow> abi_type_list_measure ts)"
    by(cases ts; auto)
qed

(* Another measure for termination *)
fun tails_measure :: "(abi_value + (abi_type * nat)) list \<Rightarrow> nat" where
"tails_measure [] = 1"
| "tails_measure ((Inl _)#ts) = 1 + tails_measure ts"
| "tails_measure ((Inr (t, _))#ts) =
    abi_type_measure t + tails_measure ts"

fun abi_size_lower_bound :: "abi_type \<Rightarrow> int" where
"abi_size_lower_bound t =
 (if abi_type_isstatic t then abi_static_size t
  else 32)"

(* Implementation of the core decoder
   End-users should call decode instead (see below), which implements
   top-level validity checks 
*)
function (sequential) decode' :: "abi_type \<Rightarrow> (int * 8 word list) \<Rightarrow> (abi_value * int) orerror"

(* first returned nat is the length of all the heads (used for computing offsets); 
   second returned nat is number of bytes consumed;
   input nat is running count of head length. *)
and decode'_dyn_tuple_heads :: "abi_type list \<Rightarrow> int \<Rightarrow> (int * 8 word list) \<Rightarrow> 
                (abi_value option list *  (int option) list * int * int) orerror"
(* list parameter gives an offset for each field that still needs to be parsed
   the int parameter is an index of how many bytes into our overall tuple encoding we are *)
and decode'_dyn_tuple_tails :: "(int option) list \<Rightarrow> abi_type list \<Rightarrow> abi_value option list \<Rightarrow> 
                                int \<Rightarrow> (int * 8 word list) \<Rightarrow> 
                (abi_value list * int) orerror"
where
"decode' t (ix, l) =
(if ix < 0 then Err (decode_err ''Tried to decode at a negative index'' (ix, l))
 else (if (ix > length l) then Err (decode_err ''Tried to decode at an index out of range'' (ix, l))
 else
 (let l' = drop (nat ix) l in
  
  (if abi_type_isstatic t
    then
      if int (length l) < (abi_static_size t) + ix 
      then Err (decode_err ''Too few bytes for given static type'' (ix, l))
      else (case decode_static t (ix, l) of
            Err s \<Rightarrow> Err s
            | Ok v \<Rightarrow> Ok (v, (abi_static_size t)))
   else
    (case t of
      Tfarray t n \<Rightarrow>
        (let ts = List.replicate (nat n) t in
        (case decode'_dyn_tuple_heads ts 0 (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
            (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vs, bytes_parsed') \<Rightarrow> Ok (Vfarray t n vs, bytes_parsed + bytes_parsed'))))
      | Tarray t \<Rightarrow>
       if int (length l) < 32 + ix 
       then Err (decode_err ''Too few bytes; could not read array size'' (ix, l))
       else
         (let n = (decode_uint (take 32 l')) in
          \<comment> \<open>check data length against a lower bound for size of encoded data \<close>
          if int (length l) < 32 + (n * abi_size_lower_bound t) + ix
          then Err (decode_err ''Bytes remaining less than lower bound on array size'' (ix, l))
          else
          (let ts = List.replicate (nat n) t in
          (case decode'_dyn_tuple_heads ts 0 (ix + 32, l) of
            Err s \<Rightarrow> Err s
            | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
              (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix + 32, l) of
                Err s \<Rightarrow> Err s
                | Ok (vs, bytes_parsed') \<Rightarrow> Ok (Varray t vs, bytes_parsed + bytes_parsed' + 32)))))
      | Ttuple ts \<Rightarrow>
        (case decode'_dyn_tuple_heads ts 0 (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
            (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vs, bytes_parsed') \<Rightarrow> Ok (Vtuple ts vs, bytes_parsed + bytes_parsed')))
      | Tbytes \<Rightarrow>
        if int (length l) < 32 + ix
        then Err (decode_err ''Too few bytes; could not read bytestream size'' (ix, l))
        else let sz = (decode_uint (take 32 l')) in
             if int (length l) < sz + 32 + ix
             then Err (decode_err ''Fewer bytes remaining than bytestream size'' (ix, l))
             else (if check_padding (nat sz) (drop 32 l') 
                   then Ok (Vbytes (take (nat sz) (drop 32 l')), int(skip_padding (nat sz)) + 32)
                   else Err (decode_err ''Invalid bytes padding'' (ix, l)))
      | Tstring \<Rightarrow> 
        if int(length l) < 32 + ix 
        then Err (decode_err ''Too few bytes; could not read string size'' (ix, l))
        else let sz = (decode_uint (take 32 l')) in
             if int (length l) < sz + 32 + ix
             then Err (decode_err ''Fewer bytes remaining than string size'' (ix, l))
             else (if check_padding (nat sz) (drop 32 l') 
             then Ok (Vstring (bytes_to_string (take (nat sz) (drop 32 l')))
                     , int (skip_padding (nat sz)) + 32)
                   else Err (decode_err ''Invalid string padding'' (ix, l)))
      | _ \<Rightarrow> Err (decode_err ''This should be dead code'' (ix, l)))))))"

(* indices ix are the index of the start of the overall tuple we are encoding *)
| "decode'_dyn_tuple_heads [] n (ix, l) = Ok ([], [], n, 0)"
| "decode'_dyn_tuple_heads (th#tt) n (ix, l) =
  (let l' = drop (nat (ix + n)) l in
    (if abi_type_isstatic th
      then (case decode' th (ix + n, l) of
        Err s \<Rightarrow> Err s
        | Ok (v, bytes_parsed) \<Rightarrow>
          (case decode'_dyn_tuple_heads tt (n + nat (abi_static_size th)) (ix, l) of
            Err s \<Rightarrow> Err s
            | Ok (vos, idxs, n', bytes_parsed') \<Rightarrow> 
                Ok (Some v # vos, None#idxs, n', bytes_parsed + bytes_parsed')))
    else
      (if length l' < 32 then Err (decode_err ''Too few bytes; could not read tuple head'' (ix, l))
       else let sz = (decode_sint (take 32 l')) in
            (case decode'_dyn_tuple_heads tt (n + 32) (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vos, idxs, n', bytes_parsed) \<Rightarrow> 
                  Ok (None # vos, (Some (ix + sz))#idxs, n', bytes_parsed + 32)))))"

| "decode'_dyn_tuple_tails [] [] []  _ (ix, l) = Ok ([], 0)"
| "decode'_dyn_tuple_tails (None#t) (th#tt) (Some vh#vt) offset (ix, l) = 
   (case decode'_dyn_tuple_tails t tt vt offset (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok (vs, bytes_parsed) \<Rightarrow> Ok (vh#vs, bytes_parsed))"

| "decode'_dyn_tuple_tails ((Some toffset)#t) (th#tt) (None#vt) offset (ix, l) =
   (let ix' = toffset in
       (case decode' th (ix', l) of
              Err s \<Rightarrow> Err s
              | Ok (v, bytes_parsed) \<Rightarrow>
                     let offset' = offset + bytes_parsed in
                     (case decode'_dyn_tuple_tails t tt vt offset' (ix, l) of
                           Err s \<Rightarrow> Err s
                           | Ok (vs, bytes_parsed') \<Rightarrow> 
                              Ok (v#vs, bytes_parsed + bytes_parsed'))))                          
      "

| "decode'_dyn_tuple_tails _ _ _ _ (ix, l) = Err (decode_err ''Should be dead code'' (ix, l))"

  by pat_completeness auto

fun somes :: "'a option list \<Rightarrow> 'a list" where
"somes [] = []"
| "somes (None#t) = somes t"
| "somes (Some h#t) = h # somes t"

lemma abi_type_measure_nonzero :
  "abi_type_measure t > 0"
  by(induction t; auto)

(* Termination proof for decoder
   (Automation fails to prove termination in a reasonable amount of time)
*)
termination decode'
proof(relation 
"measure (\<lambda> x .
    (case x of
       Inl (t, (ix, l)) \<Rightarrow> 1 + abi_type_measure t
      | Inr (Inl (ts,  n, (ix, l))) \<Rightarrow> abi_type_list_measure ts
      | Inr (Inr (idxs, ts, vs, n, (ix, l))) \<Rightarrow> abi_type_list_measure ts))";
      (auto simp add:abi_type_list_measure_replicate; fail)?)

  fix t ix l x x13
  show
    "\<And> xa xb.
       \<not> ix < 0 \<Longrightarrow>
       \<not> int (length l) < ix \<Longrightarrow>
       x = drop (nat ix) l \<Longrightarrow>
       \<not> abi_type_isstatic t \<Longrightarrow>
       t = Tarray x13 \<Longrightarrow>
       \<not> int (length l) < 32 + ix \<Longrightarrow>
       xa = decode_uint (take 32 x) \<Longrightarrow>
       xb = replicate (nat xa) x13 \<Longrightarrow>
       (Inr (Inl (xb, 0, ix + 32, l)), Inl (t, ix, l))
       \<in> measure
           (\<lambda>x. case x of Inl (t, ix, l) \<Rightarrow> 1 + abi_type_measure t 
                        | Inr (Inl (ts, n, ix, l)) \<Rightarrow> abi_type_list_measure ts
                        | Inr (Inr (idxs, ts, vs, n, ix, l)) \<Rightarrow> abi_type_list_measure ts)"

    using abi_type_measure_nonzero[of x13]
          Word.uint_lt[of "(word_rcat (take 32 (drop (nat ix) l)) :: 256 word)"]
    by(auto simp add: abi_type_list_measure_replicate max_u256_def intro:Nat.add_less_mono)
next
  fix t ix l x x13
  show
    "\<And> xa xb a xc y xd ya xe yb.
       \<not> ix < 0 \<Longrightarrow>
       \<not> int (length l) < ix \<Longrightarrow>
       x = drop (nat ix) l \<Longrightarrow>
       \<not> abi_type_isstatic t \<Longrightarrow>
       t = Tarray x13 \<Longrightarrow>
       \<not> int (length l) < 32 + ix \<Longrightarrow>
       xa = decode_uint (take 32 x) \<Longrightarrow>
       xb = replicate (nat xa) x13 \<Longrightarrow>
       decode'_dyn_tuple_heads xb 0 (ix + 32, l) = Ok a \<Longrightarrow>
       (xc, y) = a \<Longrightarrow>
       (xd, ya) = y \<Longrightarrow>
       (xe, yb) = ya \<Longrightarrow>
       decode'_decode'_dyn_tuple_heads_decode'_dyn_tuple_tails_dom 
          (Inr (Inl (xb, 0, ix + 32, l))) \<Longrightarrow>
       (Inr (Inr (xd, xb, xc, xe, ix + 32, l)), Inl (t, ix, l))
       \<in> measure (\<lambda>x. case x of Inl (t, ix, l) \<Rightarrow> 1 + abi_type_measure t 
                              | Inr (Inl (ts, n, ix, l)) \<Rightarrow> abi_type_list_measure ts
                              | Inr (Inr (idxs, ts, vs, n, ix, l)) \<Rightarrow> abi_type_list_measure ts)"
   using abi_type_measure_nonzero[of x13]
          Word.uint_lt[of "(word_rcat (take 32 (drop (nat ix) l)) :: 256 word)"]
   by(auto simp add: abi_type_list_measure_replicate max_u256_def intro:Nat.add_less_mono)
next
  fix th tt
  show
    "\<And> n ix l x.
       x = drop (nat (ix + n)) l \<Longrightarrow>
       abi_type_isstatic th \<Longrightarrow>
       (Inl (th, ix + n, l), Inr (Inl (th # tt, n, ix, l)))
       \<in> measure (\<lambda>x. case x of Inl (t, ix, l) \<Rightarrow> 1 + abi_type_measure t 
                              | Inr (Inl (ts, n, ix, l)) \<Rightarrow> abi_type_list_measure ts 
                              | Inr (Inr (idxs, ts, vs, n, ix, l)) \<Rightarrow> abi_type_list_measure ts)"
    by(cases tt; auto)
next
  fix tt
  show
    "\<And> toffset t th vt offset ix l x.
       x = toffset \<Longrightarrow>
       (Inl (th, x, l), Inr (Inr (Some toffset # t, th # tt, None # vt, offset, ix, l)))
       \<in> measure (\<lambda>x. case x of Inl (t, ix, l) \<Rightarrow> 1 + abi_type_measure t 
                              | Inr (Inl (ts, n, ix, l)) \<Rightarrow> abi_type_list_measure ts 
                              | Inr (Inr (idxs, ts, vs, n, ix, l)) \<Rightarrow> abi_type_list_measure ts)"
    by(cases tt; auto)
qed

fun decode :: "abi_type \<Rightarrow> 8 word list \<Rightarrow> abi_value orerror" where
"decode t l =
  (if abi_type_valid t then
    (case decode' t (0, l) of
      Err s \<Rightarrow> Err s
      | Ok (v, _) \<Rightarrow> Ok v)
   else Err ''Invalid ABI type'')"

end