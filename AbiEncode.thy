theory AbiEncode imports AbiTypes
begin

(* a minimal ABI encoder, used mostly for sanity checking/testing
the decoder (AbiDecoder.thy) *)

(* TODO: decide whether to add checks to these encoders,
   or to do so outside *)
fun encode_int :: "int \<Rightarrow> 8 word list" where
"encode_int i =
  Word.word_rsplit (Word.word_of_int i :: 256 word)"

fun encode_bool :: "bool \<Rightarrow> 8 word list" where
"encode_bool True = encode_int 1"
| "encode_bool False = encode_int 0"

fun encode_fixed :: "nat \<Rightarrow> rat \<Rightarrow> 8 word list" where
"encode_fixed n r =
  encode_int (fst (Rat.quotient_of (r * (10 ^ n))))"

fun encode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"encode_fbytes n l = 
  take n l"

fun encode_static :: "abi_value \<Rightarrow> 8 word list option" where
"encode_static (Vuint n i) = Some (encode_int i)"
| "encode_static (Vsint n i) = Some (encode_int i)"
| "encode_static (Vaddr a) = Some (encode_int a)"
| "encode_static (Vbool b) = Some (encode_bool b)"
| "encode_static (Vfixed m n r) = Some (encode_fixed n r)"
| "encode_static (Vufixed m n r) = Some (encode_fixed n r)"
| "encode_static (Vfbytes n l) = Some (encode_fbytes n l)"
| "encode_static (Vfarray t n l) =
    (case List.those (List.map encode_static l) of
      None \<Rightarrow> None
      | Some bs \<Rightarrow> Some (List.concat bs))"
| "encode_static (Vtuple ts vs) =
        (case List.those (List.map encode_static vs) of
          None \<Rightarrow> None
         | Some bs \<Rightarrow> Some (List.concat bs))"
| "encode_static _ = None"

(* for dynamic tuples, we need to do the following:
   - encode heads
   - encode all values (map)
   - encode tail *)

fun string_to_bytes :: "char list \<Rightarrow> 8 word list" where
"string_to_bytes s = 
  List.map (\<lambda> c . word_of_int (int_of_integer (integer_of_char c))) s"

(* pad a byte stream to a multiple of 32 bytes *)
fun pad_bytes :: "8 word list \<Rightarrow> 8 word list" where
"pad_bytes l = 
  (case divmod_nat (length l) 32 of
        (_, 0) \<Rightarrow> l
        | (_, rem) \<Rightarrow> l @ (List.replicate rem (Word.word_of_int 0)))"

fun heads_length :: "(8 word list + abi_value) list \<Rightarrow> nat" where
"heads_length [] = 0"
| "heads_length (Inl bs # t) = length bs + heads_length t"
| "heads_length (Inr v # t) = 32 + heads_length t"

fun encode :: "abi_value \<Rightarrow> 8 word list option" 
and encode_tuple_heads :: "abi_value list \<Rightarrow> (int * 8 word list) list \<Rightarrow> 8 word list option" 
(*
and encode_tuple_tails :: "(8 word list + abi_value) list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list option" where *)

and encode_tuple_tails :: "(abi_value) list \<Rightarrow> (int * 8 word list) list option" where
"encode v =
  (if abi_type_isstatic (abi_get_type v) then
      encode_static v
   else (case v of
          Vfarray t n vs \<Rightarrow>
          (case List.those (List.map encode vs) of
                None \<Rightarrow> None
                | Some bss \<Rightarrow> Some (List.concat bss))
          | Varray t vs \<Rightarrow>
            (case List.those (List.map encode vs) of
                None \<Rightarrow> None
                | Some bss \<Rightarrow> Some (encode_int (int (length vs)) @ List.concat bss))
          | Vtuple ts vs \<Rightarrow> 
              (case encode_tuple_tails vs of
                None \<Rightarrow> None
                | Some bvs \<Rightarrow>
                  (case encode_tuple_heads vs bvs of
                        None \<Rightarrow> None
                        | Some bs \<Rightarrow> Some bs))
          | Vbytes l \<Rightarrow> Some (encode_int (length l) @ pad_bytes l)
          | Vstring s \<Rightarrow> let bs = string_to_bytes s in
                         Some (encode_int (length bs) @ pad_bytes bs)
          | _ \<Rightarrow> None))"

(* need to refactor for cleaner termination proof
idea: encode tails first?
ok, now we need some kind of way to get which tail we are on
what is n? n should be the offset of the current tail
this means we need some way to get the current offset
*)
| "encode_tuple_heads [] [] = Some ([])"
| "encode_tuple_heads (v#vs) ((offset, bs)#bss) =
    (if abi_type_isstatic (abi_get_type v) then
        (case encode v of
          None \<Rightarrow> None
          | Some enc \<Rightarrow> (case (encode_tuple_heads vs bss) of
                          None \<Rightarrow> None
                          | Some enc' \<Rightarrow> Some (enc @ enc')))
    else (case (encode_tuple_heads vs bss) of
                None \<Rightarrow> None
                | Some enc \<Rightarrow> Some (encode_int (offset) @ enc)))
    "
| "encode_tuple_heads _ _ = None"

(* OK - we need to make it so that we track the length of the entire thing
   so far.



 *)
(* abi_static_size *)
| "encode_tuple_tails [] = Some []"
| "encode_tuple_tails (v # rest) =
    (case encode_tuple_tails rest of
                None \<Rightarrow> None
                | Some ts \<Rightarrow> (if abi_type_isstatic (abi_get_type v)
                                then Some ((abi_static_size (abi_get_type v), [])#ts)
                                else (case encode v of None \<Rightarrow> None
                                            | Some enc \<Rightarrow> Some ((int (length enc + 32), enc)#ts))))"
        
          

value "Word.word_of_int (-1) :: 256 word"

end