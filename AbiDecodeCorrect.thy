theory AbiDecodeCorrect imports AbiEncodeSpec AbiDecode

begin

(* if a valid encoding exists for our value,
   the decoder will give it to us *)
lemma abi_decode_succeed :
  "\<And> v full_code .
     can_encode_as v full_code 0 (length full_code) \<Longrightarrow>
     decode (abi_get_type v) full_code = Ok v"
  sorry

lemma abi_decode_succeed_converse :
  "\<And> v full_code .
    decode (abi_get_type v) full_code = Ok v \<Longrightarrow>
    can_encode_as v full_code 0 (length full_code)"
  sorry

end