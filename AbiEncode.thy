theory AbiEncode imports AbiTypes Ok
begin

(* An encoder for the Solidity ABI.
   It is designed to produce "canonical" encodings; that is,
   it will produce outputs that match Solidity's output *)

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
        (d, 0) \<Rightarrow> l
        | (d, Suc rem) \<Rightarrow> l @ (List.replicate (32 - (Suc rem)) (Word.word_of_int 0)))"

fun encode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"encode_fbytes n l = 
  pad_bytes (take n l)"

(* TODO: do we need to capture the process of 
    calculating the selector with Keccak?
    If we wanted we could use Eth-Isabelle's implementation.
    For now we assume the 4-byte selector is precomputed *)
fun encode_function_sel :: "int \<Rightarrow> int \<Rightarrow> 8 word list" where
"encode_function_sel addr sel =
  pad_bytes (
    Word.word_rsplit (Word.word_of_int addr :: 160 word) @
    Word.word_rsplit (Word.word_of_int sel :: 32 word))"

(* NB: This function is part of the spec. See AbiEncodeSpec.thy.
*)
fun encode_static :: "abi_value \<Rightarrow> 8 word list orerror" where
"encode_static (Vuint n i) = Ok (encode_int i)"
| "encode_static (Vsint n i) = Ok (encode_int i)"
| "encode_static (Vaddr a) = Ok (encode_int a)"
| "encode_static (Vbool b) = Ok (encode_bool b)"
| "encode_static (Vfixed m n r) = Ok (encode_fixed n r)"
| "encode_static (Vufixed m n r) = Ok (encode_fixed n r)"
| "encode_static (Vfbytes n l) = Ok (encode_fbytes n l)"
| "encode_static (Vfunction addr sel) =
    Ok (encode_function_sel addr sel)"
| "encode_static (Vfarray t n l) =
    (case those_err (List.map encode_static l) of
      Err s \<Rightarrow> Err s
      | Ok bs \<Rightarrow> Ok (List.concat bs))"
| "encode_static (Vtuple ts vs) =
        (case those_err (List.map encode_static vs) of
          Err s \<Rightarrow> Err s
         | Ok bs \<Rightarrow> Ok (List.concat bs))"
| "encode_static _ = Err ''Called static encoder on dynamic value''"

(* TODO: This does not (I believe) support Unicode/UTF8 *)
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


(* 
   Auxiliary encoder functions that do the "heavy lifting" of encoding.
   This encoder operates in 3 stages:
   1. Calculate heads length
   2. Encode tails (if data is dynamic)
   3. Encode heads (if data is dynamic)

   NB: this function does not do validity checking on parameters.
   Implementations should call encode (see below) instead, which does.
*)
fun encode' :: "abi_value \<Rightarrow> 8 word list orerror" 

(* Given a list of (offset, tail-bytes) pairs
   We return a pair of byte-lists
   First is heads; second is tails. *)
and encode'_tuple_heads :: "abi_value list \<Rightarrow> (int * 8 word list) list \<Rightarrow> (8 word list * 8 word list) orerror"

(* first int input is length of tails so far *)
(* second int input is length of all (encoded) head-bytes
   for this data structure (statically calculated) *)
and encode'_tuple_tails :: "(abi_value) list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> (int * 8 word list) list orerror" where
"encode' v =
  (if abi_type_isstatic (abi_get_type v) then
      encode_static v
   else (case v of
          Vfarray t n vs \<Rightarrow>
          (case encode'_tuple_tails vs 0 (heads_length vs) of
            Err s \<Rightarrow> Err s
            | Ok bvs \<Rightarrow> (case encode'_tuple_heads vs bvs  of
                            Err s \<Rightarrow> Err s
                            | Ok (heads, tails) \<Rightarrow> Ok (heads @ tails)))
          | Varray t vs \<Rightarrow>
           (case encode'_tuple_tails vs 0 (heads_length vs) of
            Err s \<Rightarrow> Err s
            | Ok bvs \<Rightarrow> (case encode'_tuple_heads vs bvs  of
                            Err s \<Rightarrow> Err s
                            | Ok (heads, tails) \<Rightarrow> Ok (encode_int (length vs) @ heads @ tails)))
          | Vtuple ts vs \<Rightarrow> 
              (case encode'_tuple_tails vs 0 (heads_length vs) of
                Err s \<Rightarrow> Err s
                | Ok bvs \<Rightarrow>
                  (case encode'_tuple_heads vs bvs  of
                        Err s \<Rightarrow> Err s
                        | Ok (heads, tails) \<Rightarrow> Ok (heads @ tails)))
          | Vbytes l \<Rightarrow> Ok (encode_int (length l) @ pad_bytes l)
          | Vstring s \<Rightarrow> let bs = string_to_bytes s in
                         Ok (encode_int (length bs) @ pad_bytes bs)
          | _ \<Rightarrow> Err ''Should be dead code (encode')''))"

| "encode'_tuple_heads [] []  = Ok ([], [])"
| "encode'_tuple_heads (v#vs) ((offset, bs)#bss) =
    (if abi_type_isstatic (abi_get_type v) then
        (case encode' v of
          Err s \<Rightarrow> Err s
          | Ok head1 \<Rightarrow> (case (encode'_tuple_heads vs bss) of
                          Err s \<Rightarrow> Err s
                          | Ok (heads', tails) \<Rightarrow> Ok ((head1 @ heads'), (bs@tails))))
    else (case (encode'_tuple_heads vs bss) of
                Err s \<Rightarrow> Err s
                | Ok (heads, tails)  \<Rightarrow> Ok ((encode_int offset @ heads), (bs @ tails))))
    "
| "encode'_tuple_heads _ _   = Err ''Should be dead code (encode'_tuple_heads)''"

(* len_total tracks where the tail starts, including lengths of all heads *)
| "encode'_tuple_tails [] _ _ = Ok []"
| "encode'_tuple_tails (v # rest) headlen len_total =
  (if abi_type_isstatic (abi_get_type v)
      then 
                                (case encode'_tuple_tails rest headlen
                                                         (len_total) of
                                  Err s \<Rightarrow> Err s
                                  | Ok ts \<Rightarrow>  Ok ((len_total + headlen, [])#ts))
      else (case encode' v of Err s \<Rightarrow> Err s
        | Ok enc \<Rightarrow> 
          let len_total' = len_total + int (length enc) in 
          (case encode'_tuple_tails rest headlen len_total' of
                                  Err s \<Rightarrow> Err s
                                  | Ok ts \<Rightarrow> 
                                    (if sint_value_valid 256 (len_total + headlen) then Ok ((len_total + headlen, enc)#ts)
                                     else Err ''Encoded value is too long''))))"
        

definition encode :: "abi_value \<Rightarrow> 8 word list orerror"  where
"encode v =
  (if abi_value_valid v then encode' v
   else Err ''Invalid ABI value'')"

end