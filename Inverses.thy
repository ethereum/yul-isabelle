theory Inverses imports AbiEncodeCorrect AbiDecodeCorrect
begin

lemma abi_encode_correct :
  assumes H : "encode (v::abi_value) = Ok (code::8 word list)"
  shows "can_encode_as v (code::8 word list) (0)"
proof(-)
  show ?thesis using abi_encode_succeed[of v code "[]" "[]"] H
    by auto
qed

lemma abi_encode_correct_converse :
  assumes H : "can_encode_as v (code::8 word list) (0)"
  assumes Hbound : "sint_value_valid (256 :: nat) (abi_dynamic_size_bound v)"
  shows "\<exists> (code' :: 8 word list) . encode (v::abi_value) = Ok (code'::8 word list)"
proof(-)
  show ?thesis using encode_correct_converse[OF H Hbound]
    by auto
qed

theorem encode_decode :
  assumes H : "encode v = Ok bytes"
  shows "decode (abi_get_type v) bytes = Ok v"
proof(-)

  have 0 : "can_encode_as v bytes 0" using abi_encode_correct[OF H] by auto

  show ?thesis using abi_decode_correct[OF 0] by auto
qed

(* why the extra "abi_dynamic_size_bound" premise here?
   this is to guard against decoding a "highly compressed" huge byte string
   that has no canonical encoding due to its size *)
theorem decode_encode :
  assumes H : "decode (abi_get_type v) bytes = Ok v"
  assumes Hbound : "sint_value_valid (256 :: nat) (abi_dynamic_size_bound v)"

shows "\<exists> bytes' . encode v = Ok bytes'"
proof(-)

  have 0 : "can_encode_as v bytes 0" using abi_decode_correct_converse[OF H] by auto

  show ?thesis using abi_encode_correct_converse[OF 0 Hbound] by auto
qed

theorem decode_encode_decode :
  assumes Hdec : "decode (abi_get_type v) bytes = Ok v"
  assumes Hbound : "sint_value_valid (256 :: nat) (abi_dynamic_size_bound v)"
  shows "\<exists> bytes' . encode v = Ok bytes' \<and>
         decode (abi_get_type v) bytes' = Ok v"
proof(-)

  obtain bytes' where 0 : "encode v = Ok bytes'"
    using decode_encode[OF Hdec Hbound] by auto

  have 1 : "decode (abi_get_type v) bytes' = Ok v"
    using encode_decode[OF 0] by auto

  show ?thesis using 0 1 by auto
qed


end