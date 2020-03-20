theory AbiEncode imports AbiTypes Ok
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

(* pad a byte stream to a multiple of 32 bytes *)
fun pad_bytes :: "8 word list \<Rightarrow> 8 word list" where
"pad_bytes l = 
  (case divmod_nat (length l) 32 of
        (_, 0) \<Rightarrow> l
        | (_, rem) \<Rightarrow> l @ (List.replicate (32 - rem) (Word.word_of_int 0)))"

fun encode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"encode_fbytes n l = 
  pad_bytes (take n l)"

fun encode_static :: "abi_value \<Rightarrow> 8 word list orerror" where
"encode_static (Vuint n i) = Ok (encode_int i)"
| "encode_static (Vsint n i) = Ok (encode_int i)"
| "encode_static (Vaddr a) = Ok (encode_int a)"
| "encode_static (Vbool b) = Ok (encode_bool b)"
| "encode_static (Vfixed m n r) = Ok (encode_fixed n r)"
| "encode_static (Vufixed m n r) = Ok (encode_fixed n r)"
| "encode_static (Vfbytes n l) = Ok (encode_fbytes n l)"
| "encode_static (Vfarray t n l) =
    (case those_err (List.map encode_static l) of
      Err s \<Rightarrow> Err s
      | Ok bs \<Rightarrow> Ok (List.concat bs))"
| "encode_static (Vtuple ts vs) =
        (case those_err (List.map encode_static vs) of
          Err s \<Rightarrow> Err s
         | Ok bs \<Rightarrow> Ok (List.concat bs))"
| "encode_static _ = Err ''Called static encoder on dynamic value''"


fun string_to_bytes :: "char list \<Rightarrow> 8 word list" where
"string_to_bytes s = 
  List.map (\<lambda> c . word_of_int (int_of_integer (integer_of_char c))) s"

fun heads_length :: "(abi_value) list \<Rightarrow> int" where
"heads_length [] = 0"
| "heads_length (h#t) = 
    (let tyh = (abi_get_type h) in
    (if abi_type_isstatic tyh
        then abi_static_size tyh + heads_length t
        else 32 + heads_length t))"


(* 3 stages
   first calculate heads length
   then do encode_tails
   finally, encode heads
*)

fun encode' :: "abi_value \<Rightarrow> 8 word list orerror" 

(* int input is length of heads so far
   first output is heads
   second output is tails *)
and encode'_tuple_heads :: "abi_value list \<Rightarrow> (int * 8 word list) list \<Rightarrow> int \<Rightarrow> 8 word list \<Rightarrow> (8 word list) orerror"
(*
and encode_tuple_tails :: "(8 word list + abi_value) list \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list option" where *)

and encode'_tuple_tails :: "(abi_value) list \<Rightarrow> int \<Rightarrow> (int * 8 word list) list orerror" where
"encode' v =
  (if abi_type_isstatic (abi_get_type v) then
      encode_static v
   else (case v of
          Vfarray t n vs \<Rightarrow>
          (case encode'_tuple_tails vs 0  of
            Err s \<Rightarrow> Err s
            | Ok bvs \<Rightarrow> (case encode'_tuple_heads vs bvs (heads_length vs) []  of
                            Err s \<Rightarrow> Err s
                            | Ok bs \<Rightarrow> Ok bs))
          | Varray t vs \<Rightarrow>
           (case encode'_tuple_tails vs 0 of
            Err s \<Rightarrow> Err s
            | Ok bvs \<Rightarrow> (case encode'_tuple_heads vs bvs (heads_length vs) [] of
                            Err s \<Rightarrow> Err s
                            | Ok bs \<Rightarrow> Ok (encode_int (length vs) @ bs)))
          | Vtuple ts vs \<Rightarrow> 
              (case encode'_tuple_tails vs 0 of
                Err s \<Rightarrow> Err s
                | Ok bvs \<Rightarrow>
                  (case encode'_tuple_heads vs bvs (heads_length vs) [] of
                        Err s \<Rightarrow> Err s
                        | Ok bs \<Rightarrow> Ok bs))
          | Vbytes l \<Rightarrow> Ok (encode_int (length l) @ pad_bytes l)
          | Vstring s \<Rightarrow> let bs = string_to_bytes s in
                         Ok (encode_int (length bs) @ pad_bytes bs)
          | _ \<Rightarrow> Err ''Should be dead code (encode')''))"

(* need to refactor for cleaner termination proof
idea: encode tails first?
ok, now we need some kind of way to get which tail we are on
what is n? n should be the offset of the current tail
this means we need some way to get the current offset
*)
| "encode'_tuple_heads [] [] headlen tails = Ok (tails)"
| "encode'_tuple_heads (v#vs) ((offset, bs)#bss) headlen tails =
    (if abi_type_isstatic (abi_get_type v) then
        (case encode' v of
          Err s \<Rightarrow> Err s
          | Ok enc \<Rightarrow> (case (encode'_tuple_heads vs bss headlen tails) of
                          Err s \<Rightarrow> Err s
                          | Ok enc' \<Rightarrow> Ok (enc @ enc')))
    else (case (encode'_tuple_heads vs bss (headlen) (tails @ bs)) of
                Err s \<Rightarrow> Err s
                | Ok enc \<Rightarrow> Ok (encode_int (offset + headlen) @ enc)))
    "
(* offset + headlen? offset + headlen + 32? *)
| "encode'_tuple_heads _ _ _ _ = Err ''Should be dead code (encode'_tuple_heads)''"

(* OK - we need to make it so that we track the length of the entire thing
   so far.



 *)
(* len_total tracks where the tail starts, including lengths of all heads *)
(* the issue is that we're starting from the wrong place?  *)
(* we need a way to calculate the lengths of all heads before we start encoding tails (?)

*)
| "encode'_tuple_tails [] _ = Ok []"
| "encode'_tuple_tails (v # rest) len_total =
  (if abi_type_isstatic (abi_get_type v)
      then 
                                (case encode'_tuple_tails rest
                                                         (len_total) of
                                  Err s \<Rightarrow> Err s
                                  | Ok ts \<Rightarrow> Ok ((len_total, [])#ts))
      else (case encode' v of Err s \<Rightarrow> Err s
        | Ok enc \<Rightarrow> 
          let len_total' = len_total + int (length enc) in 
          (case encode'_tuple_tails rest len_total' of
                                  Err s \<Rightarrow> Err s
                                  | Ok ts \<Rightarrow> Ok ((len_total, enc)#ts))))"
        

definition encode :: "abi_value \<Rightarrow> 8 word list orerror"  where
"encode v =
  (if abi_value_valid v then encode' v
   else Err ''Invalid ABI value'')"

(* encoding tails
idea: we can encode the data part of the tails without knowing heads
however, when encoding heads, we need information from the tails
*)

value "Word.word_of_int (-1) :: 256 word"

end