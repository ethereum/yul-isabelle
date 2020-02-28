theory AbiEncodeCorrect imports AbiEncodeSpec AbiEncode

begin

(* if the encoder succeeds, we get a valid encoding according to spec *)
lemma abi_encode_succeed :
  "\<And> v full_code . encode v = Some full_code \<Longrightarrow>
         can_encode_as v full_code 0 (length full_code)"

  sorry
   

(* if the encoder fails, there is no valid encoding according to spec *)
lemma abi_encode_fail :
  "\<And> v full_code . encode v = None \<Longrightarrow>
         \<not> (can_encode_as v full_code 0 (int (length full_code))) \<Longrightarrow>
         False"

  sorry

end