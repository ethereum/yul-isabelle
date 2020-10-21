theory AbiDecodeCorrect imports AbiEncodeSpec AbiDecode AbiEncodeCorrect

begin

(* Correctness theorems for ABI decoder
   and associated lemmas *)

(* Helpers for decoding integers *)

lemma decode_uint_max :
"Word.uint (x :: 256 word) \<le>  max_u256"
  using Word.uint_range'[of "x :: 256 word"]
  by(auto simp add:max_u256_def)

lemma take_split32 :
"(take (32::nat) (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) = 
              (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)"
    by(auto simp add:word_rsplit_def bin_rsplit_len word_rcat_def)

lemma uint_reconstruct_valid :
assumes Hv : "uint_value_valid x1 x2"
assumes Hgt : "(0::nat) < x1" 
assumes Hlt : "x1 \<le> (256::nat)"
shows "uint_value_valid x1 (uint (word_rcat (take (32::nat) 
                      (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"
proof-
  have Hlt' : "(2 :: int)^x1 \<le> (2 :: int)^256" using Hlt 
    by(rule power_increasing; auto)

  have X2_uint : "x2 \<in> uints LENGTH(256)" using Hv Hlt'
    by(auto simp add:uints_num uint_value_valid_def)

  have Conc' : "uint (word_of_int x2 :: 256 word) = x2"
    by(rule word_uint.Abs_inverse[OF X2_uint])

  show ?thesis using Conc' take_split32 Hv
    by(simp add:word_rcat_rsplit uint_value_valid_def)
qed

lemma uint_reconstruct_valid' :
  assumes Hv : "uint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "uint_value_valid x1 (uint (word_rcat
                      (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list) :: 256 word))"
  using uint_reconstruct_valid[OF Hv Hgt Hlt]
  unfolding take_split32
  by auto

lemma uint_reconstruct  :
  assumes Hv : "uint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  assumes Hv_dec : 
    "uint_value_valid x1 (uint (word_rcat (take (32::nat) (word_rsplit
                               (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"
  shows "uint (word_rcat (take (32::nat) (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
proof-
  have Hlt' : "(2 :: int)^x1 \<le> (2 :: int)^256" using Hlt 
    by(rule power_increasing; auto)

  have X2_uint : "x2 \<in> uints LENGTH(256)" using Hv Hlt'
    by(auto simp add:uints_num uint_value_valid_def)

  have Conc' : "uint (word_of_int x2 :: 256 word) = x2"
    by(rule word_uint.Abs_inverse[OF X2_uint])


  show ?thesis using Conc' take_split32 Hv
    by(simp add:word_rcat_rsplit uint_value_valid_def)
qed

lemma uint_reconstruct_full :
  assumes Hv : "uint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "uint (word_rcat (take (32::nat) (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
  using uint_reconstruct[OF Hv Hgt Hlt 
                         uint_reconstruct_valid[OF Hv Hgt Hlt]]
  by auto

lemma uint_reconstruct_full' :
  assumes Hv : "uint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "uint (word_rcat (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list) :: 256 word) = x2"
  using uint_reconstruct_full[OF Hv Hgt Hlt]
  unfolding take_split32
  by auto

lemma sint_reconstruct_valid :
  assumes Hv  : "sint_value_valid x1 x2" 
  assumes Hgt : "(0::nat) < x1"
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "sint_value_valid x1 (sint (word_rcat (take (32::nat) (word_rsplit 
                                   (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"
proof-
  have Hlt' : "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)"
  proof(rule power_increasing; (simp; fail)?)
    show "x1 - 1 \<le> 256 - 1" using Hlt by auto
  qed

  have X2_sint : "x2 \<in> sints LENGTH(256)" using Hv Hlt'
    by(auto simp add:sints_num sint_value_valid_def)

  have Conc' : "sint (word_of_int x2 :: 256 word) = x2"
    by(rule word_sint.Abs_inverse[OF X2_sint])

  show ?thesis using Conc' take_split32 Hv
    by(simp add:word_rcat_rsplit uint_value_valid_def)
qed

lemma sint_reconstruct_valid' :
  assumes Hv  : "sint_value_valid x1 x2" 
  assumes Hgt : "(0::nat) < x1"
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "sint_value_valid x1 (sint (word_rcat (word_rsplit 
                                   (word_of_int x2 :: 256 word) :: 8 word list) :: 256 word))"
  using sint_reconstruct_valid[OF Hv Hgt Hlt]
  unfolding take_split32
  by auto

lemma sint_reconstruct :
  assumes Hv  : "sint_value_valid x1 x2" 
  assumes Hgt : "(0::nat) < x1"
  assumes Hlt : "x1 \<le> (256::nat)"
  assumes Hv_dec : "sint_value_valid x1 (sint (word_rcat (take (32::nat) (word_rsplit 
                        (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word))"
  shows "sint (word_rcat (take (32::nat) (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
proof-
  have Hlt' : "(2 :: int)^(x1 - 1) \<le> (2 :: int)^(256 - 1)"
  proof(rule power_increasing; (auto; fail)?)
    show "x1 - 1 \<le> 256 - 1" using Hlt by auto
  qed

  have X2_sint : "x2 \<in> sints LENGTH(256)" using Hv Hlt'
    by(auto simp add:sints_num sint_value_valid_def)

  have Conc' : "sint (word_of_int x2 :: 256 word) = x2"
    by(rule word_sint.Abs_inverse[OF X2_sint])

  show ?thesis using Conc' take_split32 Hv

    by(simp add:word_rcat_rsplit uint_value_valid_def)
qed

lemma sint_reconstruct_full :
  assumes Hv : "sint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "sint (word_rcat (take (32::nat) (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list)) :: 256 word) = x2"
  using sint_reconstruct[OF Hv Hgt Hlt 
                         sint_reconstruct_valid[OF Hv Hgt Hlt]]
  by auto

lemma sint_reconstruct_full' :
  assumes Hv : "sint_value_valid x1 x2"
  assumes Hgt : "(0::nat) < x1" 
  assumes Hlt : "x1 \<le> (256::nat)"
  shows "sint (word_rcat (word_rsplit 
              (word_of_int x2 :: 256 word) :: 8 word list) :: 256 word) = x2"
  using sint_reconstruct_full[OF Hv Hgt Hlt]
  unfolding take_split32
  by auto

lemma int_length :
  "length (word_rsplit (word_of_int x2 :: 256 word) :: 8 word list) = 32"
  by(auto simp add:word_rsplit_def bin_rsplit_len word_rcat_def)

lemma decode_uint_valid :
  "uint_value_valid 256 (decode_uint l)"
  using decode_uint_max[of "word_rcat (take (32 :: nat) l)"]
  by(simp add:uint_value_valid_def max_u256_def)

(* lemmas for reasoning about byte padding *)
lemma pad_bytes_skip_padding :
"length (pad_bytes l) =
 skip_padding (length l)"
proof-
  obtain dv md where DM : "divmod_nat (length l) 32 = (dv, md)"
    by(cases "divmod_nat (length l) 32"; auto)

  show "length (pad_bytes l) =
        skip_padding (length l)" using DM
    by(cases md; auto simp add: divmod_nat_def)
qed

lemma take_min :
"take (min (length l) n) l = take n l"
proof(induction l arbitrary: n)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    by(cases n; auto)
qed

lemma skip_padding_gt :
  "n \<le> skip_padding n"
  by(cases "n mod 32"; auto simp add:divmod_nat_def)

lemma pad_bytes_len_gt :
  "length bs \<le> length (pad_bytes bs)"
proof(induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  obtain x1 x2 where "divmod_nat (length bs) 32 = (x1, x2)"
    by (cases "divmod_nat (length bs) 32"; auto) 

  then show ?case
    by(cases x2; cases "Suc (length bs) mod 32 "; 
                  auto simp add:divmod_nat_def)
qed

lemma pad_bytes_prefix:
  "take (length bs) (pad_bytes bs) = bs"
proof(induction bs)
  case Nil
  then show ?case by auto
next
  case (Cons a bs)
  obtain x1 x2 where "divmod_nat (length bs) 32 = (x1, x2)"
    by (cases "divmod_nat (length bs) 32"; auto) 

  then show ?case
    by(cases x2; cases "Suc (length bs) mod 32 "; 
                  auto simp add:divmod_nat_def)
qed

lemma check_padding_pad_bytes :
  assumes H : "check_padding n l"
  shows "pad_bytes (take n l) = take (length (pad_bytes (take n l))) l"
proof-

  obtain dv md where DM : "divmod_nat (length l) 32 = (dv, md)"
    by(cases "divmod_nat (length l) 32"; auto)

  obtain dv' md' where DM' :  "divmod_nat n 32 = (dv', md')"
    by(cases "divmod_nat n 32"; auto)

  have Min : "min (length l) n = n" using H DM DM'
  proof(cases md')
    case 0
    then show ?thesis using H DM DM'
      by(auto simp add:Let_def)
  next
    case (Suc nat)
    then show ?thesis using H DM DM'
      by(auto simp add:Let_def divmod_nat_def)
  qed

  show ?thesis
  proof(cases md')
    case 0
    then show ?thesis using H DM DM' Min
      by(auto simp add:Let_def)
  next
    case (Suc nat)
    then show ?thesis using H DM DM' Min
      by(auto simp add:Let_def divmod_nat_def List.drop_take List.take_add)
  qed
qed

lemma check_padding_pad_bytes' :
  assumes H : "check_padding n l"
  shows "pad_bytes (take n l) = take (skip_padding n) l"
proof-

  have "skip_padding n \<le> length l" using H
    by(auto simp add:Let_def)
  hence Lt : "n \<le> length l" using skip_padding_gt[of n] by auto
  hence Min : "min (length l) n = n" by auto
  hence Len : "(length (take n l)) = n" by auto

  show ?thesis
    using check_padding_pad_bytes[OF H]
    unfolding pad_bytes_skip_padding Len by simp
qed

(* lemmas for string <-> bytes conversion *)
lemma bytes_to_string_to_bytes :
  "bytes_to_string (string_to_bytes l) = l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case using modulo_integer.rep_eq[of "of_char a" 256]
    by(simp add:word_of_int char_of_integer_def integer_of_char_def uint_word_of_int)
qed

lemma string_to_bytes_to_string :
  "(string_to_bytes (bytes_to_string l)) = l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case using uint_idem[of a]
    by(auto simp add:word_of_int char_of_integer_def integer_of_char_def uint_idem)
qed

(* static encoder success implies static decoder success
   with the same result *)
lemma abi_encode_decode_static' :
  "(\<And> code prefix post .
     encode_static v = Ok code \<Longrightarrow>
     abi_value_valid v \<Longrightarrow>
     decode_static (abi_get_type v) (length prefix, (prefix @ code @ post)) = Ok v)" and
   "(\<And> v t n code prefix post .
      v = (Vfarray t n vs) \<Longrightarrow>
      encode_static v = Ok code \<Longrightarrow>
      abi_value_valid v \<Longrightarrow>
      decode_static_tup (List.replicate n t) (length prefix, prefix @ code @ post) = Ok vs)" and
    "(\<And> v ts code prefix post .
        v = (Vtuple ts vs) \<Longrightarrow>
        encode_static v = Ok code \<Longrightarrow>
        abi_value_valid v \<Longrightarrow>
        decode_static_tup ts (length prefix, prefix @ code @ post) = Ok vs)"
proof(induction v and vs  rule:my_abi_value_induct)
  (* Vuint *)
  case (1 n i)
  then show ?case using int_length uint_reconstruct_full
    by(auto simp add:Let_def)
next
  (* Vsint *)
  case (2 n i)
  then show ?case using int_length sint_reconstruct_full
    by(auto simp add:Let_def)
next
  (* Vaddr *)
  case (3 i)
  then show ?case using int_length uint_reconstruct_full
    by(auto simp add:Let_def addr_value_valid_def)
next
  (* Vbool *)
  case (4 b)
  then show ?case using int_length uint_reconstruct_full[of 256 1] uint_reconstruct_full[of 256 0]
    by(cases b; auto simp add: Let_def bool_value_valid_def
                      uint_value_valid_def word_rcat_def word_rsplit_def bin_rsplit_len)
next
  (* Vfixed *)
  case (5 m n r)
  then obtain num den' where Quot : "quotient_of (r * 10 ^ n) = (num, Suc den')"
    by(cases "quotient_of (r * 10 ^ n)"; auto simp add:fixed_value_valid_def split:if_split_asm)

  have Num_valid: "sint_value_valid m num" using 5 Quot
    by(cases den'; auto simp add:Let_def fixed_value_valid_def sint_value_valid_def)

  have Exp_nz : "10 ^ n \<noteq> (0 :: rat)" by(auto)

  have Num: "r * 10 ^ n = rat_of_int num"  using 5 Quot sint_reconstruct_full[OF Num_valid]
      int_length[of num]
    quotient_of_div[of "r * 10 ^ n" num "Suc den'"]
    by(cases den'; 
       auto simp add: Let_def fixed_value_valid_def sint_value_valid_def Rat.of_int_def)

  have "rat_of_int num * inverse (10 ^ n) * 10 ^ n = r * 10 ^ n" using Num by(auto)

  hence Num' : "rat_of_int num / 10 ^ n = r" unfolding divide_rat_def Exp_nz
    by(auto)

  show ?case using 5 Quot sint_reconstruct_full[OF Num_valid] int_length[of num]
      quotient_of_div[of "r * 10 ^ n" num "Suc den'"] Num'
    by(auto simp add: Let_def fixed_value_valid_def sint_value_valid_def Rat.of_int_def
            split:prod.split_asm if_split_asm)
next
  (* Vufixed *)
  case (6 m n r)
  then obtain num den' where Quot : "quotient_of (r * 10 ^ n) = (num, Suc den')"
    by(cases "quotient_of (r * 10 ^ n)"; auto simp add:ufixed_value_valid_def split:if_split_asm)

  have Num_valid: "uint_value_valid m num" using 6 Quot
    by(cases den'; auto simp add:Let_def ufixed_value_valid_def uint_value_valid_def)

  have Exp_nz : "10 ^ n \<noteq> (0 :: rat)" by(auto)

  have Num: "r * 10 ^ n = rat_of_int num"  using 6 Quot uint_reconstruct_full[OF Num_valid]
      int_length[of num]
    quotient_of_div[of "r * 10 ^ n" num "Suc den'"]
    by(cases den'; 
       auto simp add: Let_def ufixed_value_valid_def uint_value_valid_def Rat.of_int_def)

  have "rat_of_int num * inverse (10 ^ n) * 10 ^ n = r * 10 ^ n" using Num by(auto)

  hence Num' : "rat_of_int num / 10 ^ n = r" unfolding divide_rat_def Exp_nz
    by(auto)

  show ?case using 6 Quot uint_reconstruct_full[OF Num_valid] int_length[of num]
      quotient_of_div[of "r * 10 ^ n" num "Suc den'"] Num'
    by(auto simp add: Let_def fixed_value_valid_def sint_value_valid_def Rat.of_int_def
            split:prod.split_asm if_split_asm)
next
  (* Vfbytes *)
  case (7 n bs)

  obtain n_div n_mod where Divmod: "divmod_nat n 32 = (n_div, n_mod)"
    by(cases "divmod_nat n 32"; auto)

  obtain n_div' n_mod' where Divmod' : "divmod_nat (min (length bs) n) 32 = (n_div', n_mod')"
    by (cases "divmod_nat (min (length bs) n) 32"; auto)

  have Check1: "check_padding (length bs) (pad_bytes bs @ post)"
  proof(cases "n_mod'")
    case 0
    then show ?thesis using 7 Divmod Divmod' 
      by(auto simp add: Let_def fbytes_value_valid_def)
  next
    case (Suc n_mod'_pre)
    then show ?thesis using 7 Divmod Divmod' 
      by(auto simp add: Let_def fbytes_value_valid_def)
  qed

  have Check2 : "check_padding n (code @ post)" 
  proof(cases "n_mod'")
    case 0
    then show ?thesis using 7 Divmod Divmod' 
      by(auto simp add: Let_def fbytes_value_valid_def)
  next
    case (Suc n_mod'_pre)
    then show ?thesis using 7 Divmod Divmod' 
      by(auto simp add: Let_def fbytes_value_valid_def)
  qed

  show ?case using Check1 Check2  7
      pad_bytes_len_gt[of bs] pad_bytes_prefix[of bs]
    by(auto simp add:Let_def fbytes_value_valid_def simp del:check_padding.simps pad_bytes.simps)
next
  (* Vfunction *)
  case (8 i j)

  have Check : 
    "check_padding 24 (pad_bytes (word_rsplit (word_of_int i :: 160 word) @ 
                                  word_rsplit (word_of_int j :: 32 word)) @ post)"
    using 8 by(auto simp add:Let_def function_value_valid_def 
          uint_value_valid_def word_rsplit_def bin_rsplit_len word_rcat_def
          uint_word_of_int divmod_nat_def)

  have Len1 : "length (pad_bytes (word_rsplit (word_of_int i :: 160 word) @ 
                                  word_rsplit (word_of_int j :: 32 word))) = 32"
    by(auto simp add:divmod_nat_def word_rsplit_def bin_rsplit_len word_rcat_def uint_word_of_int)

  have Len2 : "length( word_rsplit (word_of_int i :: 160 word) @ 
                                    word_rsplit (word_of_int j :: 32 word) :: 8 word list) = 24"
    by(auto simp add:divmod_nat_def word_rsplit_def bin_rsplit_len word_rcat_def uint_word_of_int)

  have Len3 : "length (word_rsplit (word_of_int i :: 160 word) :: 8 word list) = 20"
    by(auto simp add:divmod_nat_def word_rsplit_def bin_rsplit_len word_rcat_def uint_word_of_int)

  have Len4 : "length (word_rsplit (word_of_int j :: 32 word) :: 8 word list) = 4"
    by(auto simp add:divmod_nat_def word_rsplit_def bin_rsplit_len word_rcat_def uint_word_of_int)

  have Take1 :
    "take (24::nat) (pad_bytes (word_rsplit (word_of_int i :: 160 word) @ 
                                word_rsplit (word_of_int j :: 32 word)) :: 8 word list) =
      (word_rsplit (word_of_int i :: 160 word) @ 
       word_rsplit (word_of_int j :: 32 word) :: 8 word list)" 
    using Len1 Len2 Len3 Len4
        pad_bytes_prefix[of
          "(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word)) :: 8 word list"]
        sym[OF take_take[of 20 24 "pad_bytes(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word)) :: 8 word list"]] unfolding min_def
    by( simp del:check_padding.simps pad_bytes.simps)

  have Take2 :
    "take (20::nat) (pad_bytes (word_rsplit (word_of_int i :: 160 word) @ 
                                word_rsplit (word_of_int j :: 32 word)) :: 8 word list) =
      (word_rsplit (word_of_int i :: 160 word) :: 8 word list)" 
    using Len1 Len2 Len3 Len4
        pad_bytes_prefix[of
          "(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word)) :: 8 word list"]
        sym[OF take_take[of 20 24 "pad_bytes(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word)) :: 8 word list"]] unfolding min_def
    by( simp del:check_padding.simps pad_bytes.simps)

  have Take3 :
    "take (4::nat) (drop (20 :: nat) (pad_bytes (word_rsplit (word_of_int i :: 160 word) @ 
                                                 word_rsplit (word_of_int j :: 32 word)))) =
          word_rsplit (word_of_int j :: 32 word)"
    using Take1 Take2 Len1 Len2 Len3 Len4
      unfolding take_drop
    by(auto simp del:check_padding.simps pad_bytes.simps)

  have V1 : "uint_value_valid (160::nat) i" using 8
    by(auto simp add:function_value_valid_def)

  have V2 : "uint_value_valid (32::nat) j" using 8
    by(auto simp add:function_value_valid_def)

  have I' : "uint (word_of_int i :: 160 word) = i"
  proof(rule word_uint.Abs_inverse)
    show "i \<in> uints LENGTH(160)"
      using V1 unfolding uint_value_valid_def word_uint.set_iff_norm
      by auto
  qed

  have J' : "uint (word_of_int j :: 32 word) = j"
  proof(rule word_uint.Abs_inverse)
    show "j \<in> uints LENGTH(32)"
      using V2 unfolding uint_value_valid_def word_uint.set_iff_norm
      by auto
  qed

  show ?case using 
        8 Check Len1 Len2 Len3 Len4 Take1 Take2 Take3
        pad_bytes_len_gt[of 
          "(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word))"]
        pad_bytes_prefix[of
          "(word_rsplit (word_of_int i :: 160 word) @ 
            word_rsplit (word_of_int j :: 32 word))"]
        V1 V2 I' J'
    by(auto simp add:Let_def function_value_valid_def word_rcat_rsplit
          simp del:check_padding.simps pad_bytes.simps)
next
  (* Vfarray *)
  case (9 t n l)
  then show ?case by auto
next
  (* Vtuple *)
  case (10 ts vs)
  then show ?case by auto
next
  (* Vbytes - contradiction *)
  case (11 bs)
  then show ?case by auto
next
  (* Vstring - contradiction *)
  case (12 s)
  then show ?case by auto
next
  (* Varray - contradiction *)
  case (13 t vs)
then show ?case by auto
next
  (* Nil *)
  case 14
  {
    (* Vfarray *)
    case 1
    then show ?case by(auto simp add:farray_value_valid_aux_def)
  next
    case 2
    then show ?case by(auto simp add:tuple_value_valid_aux_def)
  }
next
  (* Cons *)
  case (15 h l)
  {
    (* Vfarray *)
    case 1
    then obtain henc where Henc : "encode_static h = Ok henc"
      by(cases "encode_static h"; auto)

    then obtain lenc where Lenc : "those_err (map encode_static l) = Ok lenc"
      using 1
      by(cases "those_err (map encode_static l)"; auto)

    obtain n' where N' : "n = Suc n'" using 1
      by(cases n; auto simp add:farray_value_valid_aux_def)

    hence Lenc' : "encode_static (Vfarray t n' l) = Ok (concat lenc)"
      using Lenc
      by(auto)

    have Hsize :
      "abi_static_size (abi_get_type h) = length henc"
      using encode_static_size[OF Henc] 1
      by(auto simp add:farray_value_valid_aux_def)

    show ?case using 1 Henc Lenc 15(1)[OF Henc] Hsize
                     15(2)[OF refl Lenc', of "prefix @ henc" "post"] N'
      by(auto simp add:farray_value_valid_aux_def)
  next
    (* Vtuple *)
    case 2
    obtain th tl where Ts : "ts = th # tl" using 2
      by(cases ts; auto simp add:tuple_value_valid_aux_def)

    then obtain henc where Henc : "encode_static h = Ok henc" using 2
      by(cases "encode_static h"; auto)

    then obtain lenc where Lenc : "those_err (map encode_static l) = Ok lenc"
      using 2
      by(cases "those_err (map encode_static l)"; auto)

    hence Lenc' : "encode_static (Vtuple tl l) = Ok (concat lenc)"
      using Lenc
      by(auto)

    have Hsize :
      "abi_static_size (abi_get_type h) = length henc"
      using encode_static_size[OF Henc] 2
      by(auto simp add:tuple_value_valid_aux_def)

    show ?case using 2 Henc Lenc 15(1)[OF Henc] Hsize
                     15(3)[OF refl Lenc', of "prefix @ henc" "post"] Ts
      by(auto simp add:tuple_value_valid_aux_def)
  }
qed

lemma abi_encode_decode_static :
"encode_static v = Ok code \<Longrightarrow>
   abi_value_valid v \<Longrightarrow>
   decode_static (abi_get_type v) (length prefix, (prefix @ code @ post)) = Ok v"
  using abi_encode_decode_static' by auto

lemma is_head_and_tail_static_heads_eq :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   list_all abi_type_isstatic (map abi_get_type vs) \<Longrightarrow>
   heads = vs"
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case by auto
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case by auto
qed

(* combine returned values of decode'_dyn_tuple_heads *)
fun ht_combine :: "abi_value option \<Rightarrow> (int option) \<Rightarrow> abi_value option" where
"ht_combine (Some v) None = Some v"
| "ht_combine None (Some i) = Some (Vsint 256 i)"
| "ht_combine _ _ = None"

(* Underapproximation of is_head_and_tail *)
fun ht_wellbehaved ::
  "(int option) list \<Rightarrow> abi_type list \<Rightarrow> abi_value option list \<Rightarrow> bool" where
"ht_wellbehaved [] [] [] = True"
| "ht_wellbehaved (Some i#ios) (t#ts) (None#vos) =
  (abi_type_isdynamic t \<and> ht_wellbehaved ios ts vos)"
| "ht_wellbehaved (None#ios) (t#ts) (Some vo#vos) =
  (abi_type_isstatic t \<and> ht_wellbehaved ios ts vos)"
| "ht_wellbehaved _ _ _ = False"

lemma abi_decode'_dyn_tuple_heads_succeed:
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
decode'_dyn_tuple_heads (map abi_get_type vs) (int (length pre2)) 
              (length pre1, (pre1 @ pre2 @ l @ post)) = Ok (heads', tails', count', bytes) \<Longrightarrow>
can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ l @ post)
              (int (length pre1) + int (length pre2)) \<Longrightarrow>
(\<And> (offset::int) v::abi_value.
    (offset, v) \<in> set tails \<Longrightarrow> 
    can_encode_as v (pre1 @ pre2 @ l @ post) (int (length pre1) + offset)) \<Longrightarrow>
those (map2 ht_combine heads' 
       (map (\<lambda> to . (case to of None \<Rightarrow> None 
                              | Some t \<Rightarrow> Some (t - int (length pre1)))) tails')) = Some heads \<and>
map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
count' = heads_length vs + int (length pre2) \<and>
ht_wellbehaved tails' (map abi_get_type vs) heads'"
proof(induction arbitrary: heads' tails' count' pre1 pre2 post l bytes rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  show ?case using iht_static.prems(2)
  proof(cases rule:can_encode_as.cases)
    case (Estatic pre' post' code')

    then obtain xenc where Xenc : "encode_static x = Ok xenc"
      by(cases "encode_static x"; auto simp add: tuple_value_valid_aux_def)

    then obtain ysenc where Ysenc : "those_err (map encode_static ys) = Ok ysenc" using Estatic
      by(cases "those_err (map encode_static ys)"; auto simp add: tuple_value_valid_aux_def)

    hence Ysenc' : "encode_static (Vtuple ts ys) = Ok (concat ysenc)" using Estatic
      by(auto)

    have Xvalid : "abi_value_valid x" using Estatic
      by(auto simp add: tuple_value_valid_aux_def)

    have Xstatic : "abi_type_isstatic (abi_get_type x)"
      using Estatic
      by(auto simp add: tuple_value_valid_aux_def)

    have Code : "code' = xenc @ concat ysenc"
      using Xenc Ysenc Estatic by(auto)

    have Pre_eq_len : "length (pre1 @ pre2) = length pre'"
      using Estatic(2) by(auto)

    hence Pre_eq : "pre1 @ pre2 = pre'" and
          Code_post_eq : "l @ post = code' @ post'"
      using Estatic(1) 
            append_eq_append_conv[of "(pre1 @ pre2)" "pre'" "l @ post" "code' @ post'"]
      by(auto)

    have Sz : "abi_static_size (abi_get_type x) \<le> int (length xenc) + 
                        int (length (concat ysenc)) + int (length post') "
      using Estatic Xenc Ysenc encode_static_size[OF Xenc Xvalid]
      by(auto)

    have Sz' : "int (length xenc) \<le> int (length l) + int (length post)"
      using iht_static.prems iht_static.hyps encode_static_size[OF Xenc Xvalid]
      by(cases "int (length xenc) \<le> int (length l) + int (length post)"; auto)

    obtain xdec where Xdec :
      "decode_static (abi_get_type x)
                (int (length pre1) + int (length pre2), pre1 @ pre2 @ l @ post) = Ok (xdec)"
      using iht_static Xenc Ysenc Sz Sz' encode_static_size[OF Xenc Xvalid]
      by(cases "decode_static (abi_get_type x)
                (int (length pre1) + int (length pre2), pre1 @ pre2 @ l @ post)"; auto)

    obtain ysdec where Ysdec :
      "decode'_dyn_tuple_heads (map abi_get_type xs) (int (length pre2) + int (length xenc))
                  (int (length pre1), pre1 @ pre2 @ l @ post) = Ok ysdec"
      using iht_static Xenc Ysenc Sz Sz' encode_static_size[OF Xenc Xvalid] Xdec
      by(cases "decode'_dyn_tuple_heads (map abi_get_type xs)
                  (int (length pre2) + int (length xenc))
                  (int (length pre1), pre1 @ pre2 @ l @ post)"; auto)

    hence Ysdec' : "decode'_dyn_tuple_heads (map abi_get_type xs) (int (length (pre2 @ xenc)))
                  (int (length pre1), pre1 @ pre2 @ l @ post) = Ok ysdec"
      by auto

    obtain ysd1 ysd2 ysd3 ysd4 where
         Ysdec_tup : "ysdec = (ysd1, ysd2, ysd3, ysd4)"
      by(cases ysdec; auto)

    have Ysdec'' : "decode'_dyn_tuple_heads (map abi_get_type xs) (int (length (pre2 @ xenc)))
                       (int (length pre1), pre1 @ (pre2 @ xenc) @ concat ysenc @ post') = 
                      Ok (ysd1, ysd2, ysd3, ysd4)"
      using Pre_eq Code Code_post_eq Ysdec' 
      unfolding append_assoc Ysdec_tup
      by(auto)

    have X_enc_dec :
      "xdec = x"
      using abi_encode_decode_static[OF Xenc Xvalid, of "pre1 @ pre2" "concat ysenc @ post'"] Xdec
            Code_post_eq Code
      by(auto)

    have Ysd1 : "heads' = Some x # ysd1" and Ysd2 : "tails' = None # ysd2" and Ysd3 : "count' = ysd3"
       using iht_static(5)
        Xdec Ysdec' Ysdec_tup Estatic Xstatic Xenc Ysenc Sz
        abi_static_size_nonneg[of "abi_get_type x"]
        encode_static_size[OF Xenc Xvalid] X_enc_dec
      by(auto simp add:Let_def)

    have Ts_static : "abi_type_isstatic (abi_get_type (Vtuple ts ys))"
      using Estatic by auto

    have Ts_valid : "abi_value_valid (Vtuple ts ys)"
      using Estatic by (auto simp add:tuple_value_valid_aux_def)

    have Canenc : "(can_encode_as (Vtuple ts ys) 
          (pre1 @ (pre2 @ xenc) @ concat ysenc @ post') 
          (int (length pre1) + (int (length (pre2 @ xenc)))))"
      using can_encode_as.Estatic[OF Ts_static Ts_valid Ysenc', of "pre1 @ pre2 @ xenc" post']
            abi_encode_decode_static
      by(auto)

    show ?thesis using 
       iht_static.IH[of "pre2 @ xenc" "pre1" "concat ysenc" "post'"
                        ysd1 ysd2 ysd3 ysd4, OF _ Canenc] 
                      iht_static.prems(3) Estatic Code Ysdec''  Ysd1 Ysd2 Ysd3
                     Pre_eq Code_post_eq Xstatic encode_static_size[OF Xenc Xvalid]
      by(auto simp add: Let_def)
  next
    case (Etuple_dyn t'' heads'' head_types'' tails'')

    hence T''_in : "t'' \<in> set ts"  using iht_static
      by(cases "t'' = v"; auto)

    then have False using is_head_and_tail_head_types_elem[OF iht_static(1) T''_in] Etuple_dyn
      by auto

    thus ?thesis by auto
  qed
next
  case (iht_dynamic xs ys ts tails x ptr)

  have X_dyn : "abi_type_isdynamic(abi_get_type x)"
    using iht_dynamic by auto

  show ?case using iht_dynamic.prems(2)
  proof(cases rule:can_encode_as.cases)
    case (Estatic pre' post' code')

    then obtain ysenc where Ysenc : "those_err (map encode_static ys) = Ok ysenc" using Estatic
      by(cases "those_err (map encode_static ys)"; auto simp add: tuple_value_valid_aux_def)

    hence Ysenc' : "encode_static (Vtuple ts ys) = Ok (concat ysenc)" using Estatic
      by(auto)

    have Code : "code' = encode_int ptr @ concat ysenc"
      using Ysenc Estatic by(auto)

    have Ptr_len : "length (encode_int ptr) = 32"
      by(auto simp add:word_rsplit_def bin_rsplit_len)

    have Pre_eq_len : "length (pre1 @ pre2) = length pre'"
      using Estatic(2) by(auto)

    hence Pre_eq : "pre1 @ pre2 = pre'" and
          Code_post_eq : "l @ post = code' @ post'"
      using Estatic(1) 
            append_eq_append_conv[of "(pre1 @ pre2)" "pre'" "l @ post" "code' @ post'"]
      by(auto)

    have Len_ok : "32 \<le> length l + length post"
      using iht_dynamic(4) X_dyn
      by(cases "32 \<le> length l + length post"; auto simp add:Let_def)

    hence Len_ok' : "(min (32 - min (length l) 32) (32 - length l)) = 32 - length l"
      by(auto)

    obtain ysdec where Ysdec :
      "decode'_dyn_tuple_heads (map abi_get_type xs) (int (length pre2) + 32)
                  (int (length pre1), pre1 @ pre2 @ l @ post) = Ok ysdec"
      using iht_dynamic Len_ok
      by(cases "decode'_dyn_tuple_heads (map abi_get_type xs)
                  (int (length pre2) + 32)
                  (int (length pre1), pre1 @ pre2 @ l @ post)"; auto simp add:Let_def)

    hence Ysdec' : "decode'_dyn_tuple_heads (map abi_get_type xs) 
                      (int (length (pre2 @ encode_int ptr)))
                      (int (length pre1), pre1 @ pre2 @ l @ post)
         = Ok ysdec"
      using Len_ok Len_ok' Ptr_len
      by(auto)

    obtain ysd1 ysd2 ysd3 ysd4 where
         Ysdec_tup : "ysdec = (ysd1, ysd2, ysd3, ysd4)"
      by(cases ysdec; auto)

    have Ysdec'' : "decode'_dyn_tuple_heads (map abi_get_type xs) 
                        (int (length (pre2 @ encode_int ptr)))
                        (int (length pre1), pre1 @ (pre2 @ encode_int ptr)  @ 
                                                      concat ysenc @ post') = 
                      Ok (ysd1, ysd2, ysd3, ysd4)"
      using Pre_eq Code Code_post_eq Ysdec'
      unfolding append_assoc Ysdec_tup
      by(auto)

    have Ptr_valid : "sint_value_valid 256 ptr" using Estatic(4) by auto

    have X_enc_dec :
      "decode_sint (encode_int ptr) = ptr"
      using sint_reconstruct_full[OF  Ptr_valid]
      by auto

    have Ysd1 : "heads' = None # ysd1" and Ysd2 : "tails' = Some (length pre1 + ptr) # ysd2" 
                                       and Ysd3 : "count' = ysd3"
       using iht_dynamic(4)
        Ysdec' Ysdec_tup Estatic X_dyn Ysenc Len_ok Ptr_len
        abi_static_size_nonneg[of "abi_get_type x"]
        X_enc_dec
       by(auto simp add:Let_def)

    have Ts_static : "abi_type_isstatic (abi_get_type (Vtuple ts ys))"
      using Estatic by auto

    have Ts_valid : "abi_value_valid (Vtuple ts ys)"
      using Estatic by (auto simp add:tuple_value_valid_aux_def)

    have Canenc : "(can_encode_as (Vtuple ts ys) 
          (pre1 @ (pre2 @ encode_int ptr) @ concat ysenc @ post') 
          (int (length pre1) + (int (length (pre2 @ encode_int ptr)))))"
      using can_encode_as.Estatic[OF Ts_static Ts_valid Ysenc', 
                                  of "pre1 @ pre2 @ encode_int ptr" post']
            abi_encode_decode_static
      by(auto)

    show ?thesis using 
       iht_dynamic.IH[of "pre2 @ encode_int ptr" "pre1" "concat ysenc" "post'"
                        ysd1 ysd2 ysd3 ysd4, OF _ Canenc] 
                      iht_dynamic.prems(3) Estatic Code Ysdec''  Ysd1 Ysd2 Ysd3
                     Pre_eq Code_post_eq X_dyn Ptr_len
      by(auto simp add: Let_def)
  next
    case (Etuple_dyn t'' heads'' head_types'' tails'')

    hence T''_in : "t'' \<in> set ts" 
      by(auto)

    then have False using is_head_and_tail_head_types_elem[OF iht_dynamic(1) T''_in] Etuple_dyn
      by auto

    thus ?thesis by auto
  qed
qed

(* if decoding tails fails, this can only be because some
   particular tail failed to decode *)
lemma abi_decode'_dyn_tuple_tails_fail :
"decode'_dyn_tuple_tails tails ts heads offset (ix, code) = Err err \<Longrightarrow>
 ht_wellbehaved tails ts heads \<Longrightarrow>
 (\<exists> offset' t err' .
    (Some offset', t) \<in> set (zip tails ts) \<and>
    decode' t (offset', code) = Err err')
 "
proof(induction tails arbitrary: ts heads offset ix code err)
  case Nil
  then show ?case 
    by(case_tac ts; case_tac heads; auto)
next
  case (Cons tailsh tailst)
  then show ?case
  proof(cases ts)
    assume Nil' : "ts = []"
    then show ?thesis using Cons by auto
  next
    fix tsh tst
    assume Cons' : "ts = tsh#tst"
    then show ?thesis 
    proof(cases heads)
      assume Nil'' : "heads = []"
      then show ?thesis  using Cons Cons' by auto
    next
      fix headsh headst
      assume Cons'' : "heads = headsh#headst"
      then show ?thesis
      proof(cases tailsh)
        case None
        then show ?thesis
        proof(cases headsh)
          assume None' : "headsh = None"
          then show ?thesis using Cons Cons' Cons'' None by auto
        next
          fix headsh'
          assume Some' : "headsh = Some headsh'"

          hence C': "decode'_dyn_tuple_tails tailst tst headst offset (ix, code) = Err err"
            using Cons Cons' Cons'' None 
            by(auto simp del:decode'.simps split:sum.splits prod.splits)

          then show ?thesis using Cons.prems Cons.IH[OF C'] Cons' None Some' Cons''
            by(simp del: decode'.simps)
        qed
      next
        case (Some tailsh')
        then show ?thesis
        proof(cases headsh)
          assume None' : "headsh = None"
          then show ?thesis
          proof(cases "decode' tsh (tailsh', code)")
            case (Inl ch)
            then obtain ch1 ch2 where Ch : "ch = (ch1, ch2)" by(cases ch; auto)
            then have C' : 
               "decode'_dyn_tuple_tails tailst tst headst (offset + ch2) (ix, code) = Err err"
                using Cons Cons' Cons'' Some None' Inl
                by(auto simp del: decode'.simps split:prod.splits sum.splits) 
            show ?thesis using Cons.prems Cons.IH[OF C'] Cons' Cons'' Some None' Inl
              by(auto simp del: decode'.simps split:prod.splits sum.splits) 
          next
            case (Inr err')
            then show ?thesis using Cons.prems Cons' Cons'' Some None'
              by(auto simp del: decode'.simps split:prod.splits sum.splits) 
          qed
        next
          fix headsh'
          assume Some' : "headsh = Some headsh'"
          then show ?thesis using Cons Cons' Cons'' Some by auto
        qed
      qed
    qed
  qed
qed

lemma can_encode_as_start_nonneg :
  "can_encode_as v full_code offset \<Longrightarrow> 0 \<le> offset"
proof(induction rule:can_encode_as.induct; auto)
qed

(* helper for computing heads size of a list of types *)
fun ty_heads_length :: "(abi_type) list \<Rightarrow> int" where
"ty_heads_length [] = 0"
| "ty_heads_length (tyh#t) = 
    (if abi_type_isstatic tyh
        then abi_static_size tyh + ty_heads_length t
        else 32 + ty_heads_length t)"

lemma ty_heads_length_nonneg :
"0 \<le> ty_heads_length ts"
proof(induction ts)
  case Nil
  then show ?case by auto
next
  case (Cons a ts)
  then show ?case by (auto simp add:abi_static_size_nonneg)
qed

(* When considering failure cases for heads decoder, there are two ways we can fail.
  1. Too few bytes in input to decode header (ruled out by "\<le> length code" premise)
  2. Failure to decode some element *)
lemma abi_decode'_dyn_tuple_heads_fail :
"decode'_dyn_tuple_heads (ts) heads_len (ix, code) = Err err \<Longrightarrow>
 0 \<le> ix \<Longrightarrow>
 0 \<le> heads_len \<Longrightarrow>
 nat ix + nat heads_len + ty_heads_length ts \<le> int (length code) \<Longrightarrow>
 (\<exists> tpre tbad tpost err .
    ts = tpre @ [tbad] @ tpost \<and>
    (abi_type_isstatic tbad) \<and>
    (decode' tbad (nat ix + nat heads_len + ty_heads_length tpre, code) = Err err))
 "
proof(induction ts arbitrary: heads_len ix code err)
  case Nil
  then show ?case by auto
next
  case (Cons tailsh tailst)
  then show ?case
  proof(cases "abi_type_isdynamic tailsh")
    case True
    then show ?thesis
    proof(cases "length code - nat (ix + heads_len) < (32::nat)")
      assume True' : "length code - nat (ix + heads_len) < (32::nat)"
      then show ?thesis
        using Cons True ty_heads_length_nonneg[of tailst]
        by(auto simp del:decode'.simps decode_err.simps simp add:Let_def)
    next
      assume False' : "\<not> length code - nat (ix + heads_len) < (32::nat)"
      then show ?thesis
      proof(cases "decode'_dyn_tuple_heads tailst (heads_len + (32::int)) (ix, code)")
        case (Inl dec)
        then obtain vos idxs n' bytes_parsed' where Dec : "dec = (vos, idxs, n', bytes_parsed')"
          by(cases dec; auto)
        then show ?thesis 
          using Cons True False' Inl
          by(auto simp del:decode'.simps decode_err.simps simp add:Let_def)
      next
        case (Inr err')

        obtain tpre tbad tpost err'' where Bad :
          "tailst = tpre @ [tbad] @ tpost \<and>
                 abi_type_isstatic tbad \<and>
                 decode' tbad (int (nat ix + nat (heads_len + (32::int))) + 
                                                  ty_heads_length tpre, code) = 
            Err err''"
          using Cons.prems Cons.IH[OF Inr] True False' Inr
          by(auto simp del:decode'.simps decode_err.simps simp add:Let_def)

        have Asc : "ix + (heads_len + (32::int)) + ty_heads_length tpre =
                    ix + heads_len + ((32::int) + ty_heads_length tpre)" by auto

        have Bad' :
          "\<exists> err''' . tailsh # tailst = (tailsh#tpre) @ [tbad] @ tpost \<and>
          abi_type_isstatic tbad \<and> decode' tbad (int (nat ix + nat heads_len) +
            ty_heads_length (tailsh#tpre), code) = Err err'''"
          using Cons.prems  True False' Inr ty_heads_length_nonneg[of tpre] Bad
          by(auto simp del:decode'.simps decode_err.simps simp add:Let_def Asc)

        show ?thesis
        proof(rule exI[of _ "tailsh#tpre"])
          show "\<exists>(tbad::abi_type) (tpost::abi_type list) err::char list.
                  tailsh # tailst = (tailsh # tpre) @ [tbad] @ tpost \<and>
                  abi_type_isstatic tbad \<and> decode' tbad (int (nat ix + nat heads_len) + 
                  ty_heads_length (tailsh # tpre), code) = Err err" using Bad'
            by(auto simp del:decode'.simps decode_err.simps simp add:Let_def)
        qed
      qed
    qed
  next
    case False
    then show ?thesis
    proof(cases "decode' tailsh (ix + heads_len, code)")
      case (Inl dec1)
      obtain v1 bytes_parsed where Dec1 : "dec1 = (v1, bytes_parsed)" by(cases dec1; auto)
      then show ?thesis 
      proof(cases "decode'_dyn_tuple_heads tailst (heads_len + 
                   (if (0::int) \<le> abi_static_size tailsh then abi_static_size tailsh 
                                                         else (0::int))) (ix, code)")
        fix dec2
        assume Inl' : "decode'_dyn_tuple_heads tailst (heads_len + 
                       (if (0::int) \<le> abi_static_size tailsh then abi_static_size tailsh 
                                                             else (0::int))) (ix, code) = Inl dec2"
        then obtain vos idxs n' bytes_parsed' where Dec2 : "dec2 = (vos, idxs, n', bytes_parsed')"
          by(cases dec2; auto)

        show ?thesis using Cons False Inl Inl' Dec1 Dec2
          by(auto simp del:decode'.simps decode_err.simps)
      next
        fix err'       
        assume Inr' : "decode'_dyn_tuple_heads tailst (heads_len + 
                       (if (0::int) \<le> abi_static_size tailsh then abi_static_size tailsh 
                                                             else (0::int))) (ix, code) = Inr err'"

        obtain tpre tbad tpost err'' where Bad :
          "tailst = tpre @ [tbad] @ tpost \<and>
           abi_type_isstatic tbad \<and>
           decode' tbad (int (nat ix + nat (heads_len + 
              (if (0::int) \<le> abi_static_size tailsh 
               then abi_static_size tailsh else (0::int)))) + 
              ty_heads_length tpre, code) = Err err''"

          using Cons.prems Cons.IH[OF Inr'] False Inl Inr' Dec1 abi_static_size_nonneg
          by(auto simp del:decode'.simps decode_err.simps)

        have Asc : "ix + (heads_len + abi_static_size tailsh) + ty_heads_length tpre =
                    (ix + heads_len + (abi_static_size tailsh + ty_heads_length tpre))" by auto

        have Bad' :
          "\<exists> err''' . tailsh # tailst = (tailsh#tpre) @ [tbad] @ tpost \<and>
          abi_type_isstatic tbad \<and> decode' tbad (int (nat ix + nat heads_len) +
            ty_heads_length (tailsh#tpre), code) = Err err'''"
          using Cons.prems False Inl Inr' ty_heads_length_nonneg[of tpre] Bad Dec1
            abi_static_size_nonneg
          by(auto simp del:decode'.simps decode_err.simps simp add:Let_def Asc)

        show ?thesis
        proof(rule exI[of _ "tailsh#tpre"])
          show "\<exists>(tbad::abi_type) (tpost::abi_type list) err::char list.
                  tailsh # tailst = (tailsh # tpre) @ [tbad] @ tpost \<and>
                  abi_type_isstatic tbad \<and> decode' tbad (int (nat ix + nat heads_len) + 
                  ty_heads_length (tailsh # tpre), code) = Err err" using Bad'
            by(auto simp del:decode'.simps decode_err.simps simp add:Let_def)        
        qed
      qed
    next
      case (Inr b)
      show ?thesis  
      proof(rule exI[of _ "[]"])
        show " \<exists>(tbad::abi_type) (tpost::abi_type list) err::char list.
                 tailsh # tailst = [] @ [tbad] @ tpost \<and> abi_type_isstatic tbad \<and> 
                  decode' tbad (int (nat ix + nat heads_len) + ty_heads_length [], code) = Err err"
          using Inr False Cons.prems
          by(auto simp del:decode'.simps decode_err.simps simp add: Let_def)
      qed
    qed
  qed
qed


lemma list_prefix_eq_length :
  "int (length l1) + int (length l2) = int (length ltot) \<Longrightarrow>
   l1 @ l2 @ lsuf = ltot @ lsuf' \<Longrightarrow>
   l1 @ l2 = ltot"
proof(induction l1 arbitrary: l2 ltot lsuf lsuf')
  case Nil
  then show ?case by auto
next
  case (Cons a l1)
  then show ?case  by(cases ltot; auto)
qed

(* helper lemma characterizing success cases for tail decoder *)
lemma abi_decode'_dyn_tuple_tails_succeed :
  "decode'_dyn_tuple_tails tails' (map abi_get_type vs) heads' offset 
    (int (length(pre1)), pre1@pre2@code@post) = Ok (vs_out, bytes') \<Longrightarrow>

  is_head_and_tail vs heads head_types tails \<Longrightarrow>

  ht_wellbehaved tails' (map abi_get_type vs) heads' \<Longrightarrow>

  can_encode_as (Vtuple head_types heads) (pre1 @ pre2 @ code @ post)
                (int (length pre1) + int (length pre2)) \<Longrightarrow>

  (\<And> (offset::int) v::abi_value.
      (offset, v) \<in> set tails \<Longrightarrow> 
       can_encode_as v (pre1 @ pre2 @ code @ post) (int (length pre1) + offset)) \<Longrightarrow>

  those (map2 ht_combine heads' 
        (map (case_option None (\<lambda>t::int. Some (t - int (length pre1)))) tails')) = Some heads \<Longrightarrow>

  map (\<lambda>x::int \<times> abi_value. fst x + int (length pre1)) tails = somes (tails') \<Longrightarrow>

  (\<And> vd full_code start .
   vd \<in> set vs \<Longrightarrow>
   can_encode_as vd full_code start \<Longrightarrow>
   (\<exists>len::int. decode' (abi_get_type vd) (start, full_code) = Ok (vd, len))) \<Longrightarrow>

  vs_out = vs
"

proof(induction vs arbitrary:
      heads head_types tails code pre1 pre2 post heads' tails' 
      offset  vs_out bytes')
  case Nil
  then show ?case
  proof(cases tails'; auto simp del:decode'.simps)
    assume Nil' : "tails' = []"
    then show ?thesis using Nil by(cases heads'; auto simp del:decode'.simps)
  qed
next
  case (Cons v vs)
  then show ?case
  proof(cases tails')
    assume Nil' : "tails' = []"
    then show ?thesis using Cons by(auto simp del:decode'.simps)
  next
    fix tails'h tails't
    assume Cons' : "tails' = tails'h#tails't"  
    then show ?thesis
    proof(cases heads')
      assume Nil'' : "heads' = []"
      then show ?thesis using Cons by(auto simp del:decode'.simps)
    next
      fix heads'h heads't
      assume Cons'' : "heads' = heads'h#heads't"
      then show ?thesis
      proof(cases tails'h)
        case None
        (* in this case, the first element is static *)
        then obtain hds_v where Hds_v : "heads'h = Some hds_v"
          using Cons Cons' Cons''
          by(cases heads'h; simp del: decode'.simps)

        show ?thesis using Cons.prems(2)
        proof(cases rule: is_head_and_tail.cases)
          case (iht_static ys1 ts1 v1)

          obtain dec_vs dec_count where Dec_tl : 
                "decode'_dyn_tuple_tails tails't (map abi_get_type vs) 
                   heads't offset (int (length pre1), pre1 @ pre2 @ code @ post) = 
                    Ok (dec_vs, dec_count)"
            using Cons Cons' Cons'' None Hds_v
            by(simp del: decode'.simps split:sum.splits prod.splits)

          show ?thesis using Cons.prems(4)
          proof(cases rule:can_encode_as.cases)
            case (Estatic preX postX codeX)

            have Pre : "pre1 @ pre2 = preX"
              using list_prefix_eq_length[OF Estatic(2) Estatic(1)]
              by(auto simp del: decode'.simps )

            obtain vcode where Vcode : "encode_static v = Ok vcode"
              using Cons.prems Cons' Cons'' None Hds_v Estatic iht_static Dec_tl Pre
              by(cases "(encode_static v)"; auto simp del:decode'.simps)

            then obtain ys1code where Ys1code : "those_err (map encode_static ys1) = Ok ys1code"
                                 and CodeX_code : "codeX = vcode @ concat ys1code"
              using Cons.prems Cons' Cons'' None Hds_v Estatic iht_static Dec_tl Pre
              by(cases "those_err (map encode_static ys1)"; auto simp del:decode'.simps)

            have Enc'' : "can_encode_as (Vtuple ts1 ys1) ((preX @ vcode) @ concat ys1code @ postX) 
                (int (length (preX @ vcode)))" 
            proof(rule can_encode_as.Estatic)
              have "\<And> tx . tx \<in> set ts1 \<Longrightarrow> abi_type_isstatic tx"
                using is_head_and_tail_head_types_elem[OF iht_static(3)] by auto
              then show "abi_type_isstatic (abi_get_type (Vtuple ts1 ys1))"
                using Cons.prems Cons' Cons'' None Hds_v iht_static Dec_tl
                by(auto simp del: decode'.simps simp add:list_ex_iff)
            next
              show "abi_value_valid (Vtuple ts1 ys1)" using Cons.prems(4) 
              proof(cases rule:can_encode_as.cases)
                case (Estatic preX postX codeX)
                then show ?thesis using Cons.prems Cons' Cons'' None 
                                        Hds_v iht_static Dec_tl
                  by(auto simp del: decode'.simps simp add:tuple_value_valid_aux_def)
              next
                case (Etuple_dyn t heads head_types tails)
                then show ?thesis using Cons.prems Cons' Cons'' None 
                                        Hds_v iht_static Dec_tl
                  by(auto simp del: decode'.simps simp add:tuple_value_valid_aux_def)
              qed
            next
              have Pre : "pre1 @ pre2 = preX"
                using list_prefix_eq_length[OF Estatic(2) Estatic(1)]
                by(auto simp del: decode'.simps )

              show "encode_static (Vtuple ts1 ys1) = Ok (concat ys1code)" 
                using Cons.prems Cons' Cons'' None Hds_v Estatic iht_static Dec_tl Pre
                    Vcode Ys1code CodeX_code
                by(simp del: decode'.simps )
            qed

            hence Enc :
              "can_encode_as (Vtuple ts1 ys1) (preX @ vcode @ concat ys1code @ postX) 
                (int (length pre1) + int (length pre2) + int (length vcode))" 
              unfolding append_assoc Pre
              using Pre Estatic Ys1code CodeX_code
              by(simp del:encode'.simps)

            hence Enc' : "can_encode_as (Vtuple ts1 ys1) 
                          ((pre1 @ pre2) @ vcode @ concat ys1code @ postX) 
                          (int (length pre1) + int (length pre2) + int (length vcode))" 
              unfolding Pre
              by(simp del:encode'.simps)

            hence Enc'' : "can_encode_as (Vtuple ts1 ys1) 
                          (pre1 @ (pre2 @ vcode) @ concat ys1code @ postX) 
                          (int (length pre1) + int (length pre2) + int (length vcode))"
              by(simp del:encode'.simps)

            have Asc : "(int (length pre1) + int (length pre2) + int (length vcode)) = 
                   int (length pre1) + int (length (pre2 @ vcode))" by auto

            hence Enc''' : "can_encode_as (Vtuple ts1 ys1) 
                          (pre1 @ (pre2 @ vcode) @ concat ys1code @ postX) 
                          (int (length pre1) + int (length (pre2 @ vcode)))"
              using Enc'' unfolding Asc by auto

            have Dec_tl' : "decode'_dyn_tuple_tails tails't (map abi_get_type vs) 
                   heads't offset (int (length pre1), 
                                   pre1 @ (pre2 @ vcode) @ concat ys1code @ postX) = 
                    Ok (dec_vs, dec_count)" using Dec_tl Pre Estatic Ys1code CodeX_code
              by(auto)

            have TsElem' : "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> 
                              can_encode_as v (pre1 @ pre2 @ vcode @ concat ys1code @ postX) 
                                              (int (length pre1) + offset))"
            proof-
              fix offset v
              assume ElH : "(offset, v) \<in> set tails"
              then show "can_encode_as v (pre1 @ pre2 @ vcode @ concat ys1code @ postX) 
                                              (int (length pre1) + offset)"
                using Cons.prems(5)[OF ElH]  Cons' Cons'' None Hds_v
                                 Dec_tl iht_static Ys1code Vcode CodeX_code Estatic Pre
                by(auto simp del: decode'.simps)
            qed

            show ?thesis using Cons.IH[OF Dec_tl' iht_static(3) _ Enc'''] 
                               Cons.prems  Cons' Cons'' None Hds_v
                               Dec_tl iht_static Ys1code Vcode CodeX_code Estatic
                               TsElem'
              by(auto simp del: decode'.simps ) 
          next
            case (Etuple_dyn tX headsX head_typesX tailsX)
            hence False using is_head_and_tail_head_types_elem[OF iht_static(3)] iht_static
              by(auto)
            then show ?thesis by auto
          qed
        next
          case (iht_dynamic ys1 ts1 tails1 ptr1)
          then have False using Cons.prems Cons' Cons'' None Hds_v by(auto simp del:decode'.simps)
          thus ?thesis by auto
        qed
      next
        case (Some tls_v)
        (* first element is dynamic *)
        hence Hds_v : "heads'h = None"
          using Cons Cons' Cons''
          by(cases heads'h; simp del: decode'.simps)

        show ?thesis using Cons.prems(2)
        proof(cases rule: is_head_and_tail.cases)
          case (iht_static ys1 ts1 v1)
          hence False using Cons.prems Cons Cons' Cons'' Some Hds_v
            by(auto simp del:decode'.simps)
          thus ?thesis by auto
        next
          case(iht_dynamic ys1 ts1 tails1 ptr1)

          obtain dec_v dec_v_count where Dec_v : 
            "decode' (abi_get_type v) (tls_v, pre1 @ pre2 @ code @ post) = Ok (dec_v, dec_v_count)"
            using Cons.prems Cons' Cons'' Some Hds_v iht_dynamic
            by(cases "decode' (abi_get_type v) (tls_v, pre1 @ pre2 @ code @ post)"; 
               auto simp del: decode'.simps)

          then obtain dec_vs dec_count where Dec_tl : 
                "decode'_dyn_tuple_tails tails't (map abi_get_type vs) heads't 
                   (offset + dec_v_count)
                   (int (length pre1), pre1 @ pre2 @ code @ post) = 
                      Ok (dec_vs, dec_count)"
            using Cons Cons' Cons'' Some Hds_v iht_dynamic
            by(simp del: decode'.simps split:prod.split_asm sum.split_asm)

          show ?thesis using Cons.prems(4)
          proof(cases rule:can_encode_as.cases)
            case (Estatic preX postX codeX)
            have Pre : "pre1 @ pre2 = preX"
              using list_prefix_eq_length[OF Estatic(2) Estatic(1)]
              by(auto simp del: decode'.simps )

            obtain vhdcode where Vhdcode :
              "encode_static (Vsint 256 ptr1) = Ok vhdcode"
                using Cons.prems Cons' Cons'' Some Hds_v Estatic iht_static Dec_tl Pre
                by(auto simp del:decode'.simps)

            then obtain ys1code where Ys1code : "those_err (map encode_static ys1) = Ok ys1code"
                                 and CodeX_code : "codeX = vhdcode @ concat ys1code"
              using Cons.prems Cons' Cons'' Some Hds_v Estatic iht_dynamic Dec_v Dec_tl Pre
              by(cases "those_err (map encode_static ys1)"; auto simp del:decode'.simps)

            have Enc'' : "can_encode_as (Vtuple ts1 ys1) ((preX @ vhdcode) @ concat ys1code @ postX) 
                (int (length (preX @ vhdcode)))" 
            proof(rule can_encode_as.Estatic)
              have "\<And> tx . tx \<in> set ts1 \<Longrightarrow> abi_type_isstatic tx"
                using is_head_and_tail_head_types_elem[OF iht_dynamic(4)] by auto
              then show "abi_type_isstatic (abi_get_type (Vtuple ts1 ys1))"
                using Cons.prems Cons' Cons'' Some Hds_v iht_static Dec_tl iht_static
                by(auto simp del: decode'.simps simp add:list_ex_iff)
            next
              show "abi_value_valid (Vtuple ts1 ys1)" using Cons.prems(4) 
              proof(cases rule:can_encode_as.cases)
                case (Estatic preX postX codeX)
                then show ?thesis using Cons.prems Cons' Cons'' Some
                                        Hds_v iht_dynamic Dec_tl 
                  by(auto simp del: decode'.simps simp add:tuple_value_valid_aux_def)
              next
                case (Etuple_dyn t heads head_types tails)
                then show ?thesis using Cons.prems Cons' Cons'' Some 
                                        Hds_v iht_dynamic Dec_tl
                  by(auto simp del: decode'.simps simp add:tuple_value_valid_aux_def)
              qed
            next
              have Pre : "pre1 @ pre2 = preX"
                using list_prefix_eq_length[OF Estatic(2) Estatic(1)]
                by(auto simp del: decode'.simps )

              show "encode_static (Vtuple ts1 ys1) = Ok (concat ys1code)" 
                using Cons.prems Cons' Cons'' Some Hds_v Estatic iht_static Dec_tl Pre
                    Vhdcode Ys1code CodeX_code
                by(simp del: decode'.simps )
            qed

            hence Enc :
              "can_encode_as (Vtuple ts1 ys1) (preX @ vhdcode @ concat ys1code @ postX) 
                (int (length pre1) + int (length pre2) + int (length vhdcode))" 
              unfolding append_assoc Pre
              using Pre Estatic Ys1code CodeX_code
              by(simp del:encode'.simps)

            hence Enc' : "can_encode_as (Vtuple ts1 ys1) 
                          ((pre1 @ pre2) @ vhdcode @ concat ys1code @ postX) 
                          (int (length pre1) + int (length pre2) + int (length vhdcode))" 
              unfolding Pre
              by(simp del:encode'.simps)

            hence Enc'' : "can_encode_as (Vtuple ts1 ys1) 
                          (pre1 @ (pre2 @ vhdcode) @ concat ys1code @ postX) 
                          (int (length pre1) + int (length pre2) + int (length vhdcode))"
              by(simp del:encode'.simps)

            have Asc : "(int (length pre1) + int (length pre2) + int (length vhdcode)) = 
                   int (length pre1) + int (length (pre2 @ vhdcode))" by auto

            hence Enc''' : "can_encode_as (Vtuple ts1 ys1) 
                          (pre1 @ (pre2 @ vhdcode) @ concat ys1code @ postX) 
                          (int (length pre1) + int (length (pre2 @ vhdcode)))"
              using Enc'' unfolding Asc by auto

            have Dec_tl' : "decode'_dyn_tuple_tails tails't (map abi_get_type vs) 
                   heads't (offset + dec_v_count) (int (length pre1), 
                                   pre1 @ (pre2 @ vhdcode) @ concat ys1code @ postX) = 
                    Ok (dec_vs, dec_count)" using Dec_tl Pre Estatic Ys1code CodeX_code
              by(auto)

            have TsElem' : "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> 
                              can_encode_as v (pre1 @ pre2 @ vhdcode @ concat ys1code @ postX) 
                                              (int (length pre1) + offset))"
            proof-
              fix offset v
              assume ElH : "(offset, v) \<in> set tails"
              then show "can_encode_as v (pre1 @ pre2 @ vhdcode @ concat ys1code @ postX) 
                                              (int (length pre1) + offset)"
                using Cons.prems(5)[OF ElH]  Cons' Cons'' Some Hds_v
                                 Dec_tl iht_dynamic Ys1code Vhdcode CodeX_code Estatic Pre
                by(auto simp del: decode'.simps)
            qed

            have Dec_v' : "dec_v = v"
              using Cons.prems(3)
                    Cons.prems(5)[of ptr1 v] 
                    Cons.prems(6)
                    Cons.prems(8)[of v "(pre1 @ pre2 @ code @ post)" "(int (length pre1) + ptr1)"] 
                    Cons' Cons''
                    Dec_v iht_dynamic Some Hds_v Dec_tl
              by(auto simp del:decode'.simps)

            show ?thesis using Cons.IH[OF Dec_tl' iht_dynamic(4) _ Enc'''] 
                               Cons.prems  Cons' Cons'' Some Hds_v
                               Dec_tl Dec_v iht_dynamic Ys1code Vhdcode CodeX_code Estatic
                               TsElem' Dec_v'
              by(auto simp del: decode'.simps )
          next
            case (Etuple_dyn tX headsX head_typesX tailsX)
            hence False using is_head_and_tail_head_types_elem[OF iht_dynamic(4)] iht_dynamic
              by(auto)
            then show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
qed

(* lemma about our executable is_head_and_tail approximation *)
lemma is_head_and_tail_wellbehaved :
"is_head_and_tail vs heads head_types tails  \<Longrightarrow>
       ht_wellbehaved a_tail (map abi_get_type vs) a_head \<Longrightarrow>
       those (map2 ht_combine a_head (map (case_option None (\<lambda>t::int. Some (t - starta))) a_tail)) 
          = Some heads \<Longrightarrow>
       map (\<lambda>x::int \<times> abi_value. fst x + starta) tails = somes a_tail \<Longrightarrow>
       (Some offset', t) \<in> set (zip a_tail (map abi_get_type vs)) \<Longrightarrow>
       (\<exists> v . abi_get_type v = t \<and> (offset' - starta, v) \<in> set tails)"
proof(induction arbitrary: a_head a_tail starta offset' t rule: is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  obtain a_tailh a_tailt where A_tail : "a_tail = a_tailh#a_tailt" using iht_static
    by(cases a_tail; auto)
  obtain a_headh a_headt where A_head : "a_head = a_headh#a_headt" using iht_static
    by(cases a_head; auto)

  show ?case
  proof(cases a_tailh)
    case None
    then obtain a_headh_v where A_headh_v : "a_headh = Some a_headh_v" 
      using A_tail A_head iht_static
      by(cases a_headh; auto)
    then show ?thesis using None A_tail A_head iht_static by(auto)
  next
    case (Some tailh_v)
    then have A_headh_v : "a_headh = None" using A_tail A_head iht_static
      by(cases a_headh; auto)
    then show ?thesis using Some  A_tail A_head iht_static by(auto)
  qed
next
  case (iht_dynamic xs ys ts tails x ptr)
  obtain a_tailh a_tailt where A_tail : "a_tail = a_tailh#a_tailt" using iht_dynamic
    by(cases a_tail; auto)
  obtain a_headh a_headt where A_head : "a_head = a_headh#a_headt" using iht_dynamic
    by(cases a_head; auto)

  show ?case
  proof(cases a_tailh)
    case None
    then obtain a_headh_v where A_headh_v : "a_headh = Some a_headh_v" 
      using A_tail A_head iht_dynamic
      by(cases a_headh; auto)
    then show ?thesis using None A_tail A_head iht_dynamic by(auto)
  next
    case (Some tailh_v)
    then have A_headh_v : "a_headh = None" using A_tail A_head iht_dynamic
      by(cases a_headh; auto)
    then show ?thesis using Some  A_tail A_head 
        iht_dynamic.IH[of a_tailt a_headt starta] iht_dynamic.prems
      by(auto)
  qed
qed

lemma ty_heads_length_heads_length :
"ty_heads_length (map abi_get_type vs) =
  heads_length vs"
  by(induction vs; auto)

(* heads length calculation never exceeds total code size *)
(*
lemma heads_length_heads [rule_format]:
  "\<forall> heads head_types tails .
  is_head_and_tail vs heads head_types tails \<longrightarrow>
   (\<forall> start code . can_encode_as (Vtuple head_types heads) code start \<longrightarrow>
      0 \<le> start \<longrightarrow>
      heads_length vs + start \<le> length code)"
*)
lemma heads_length_heads :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   can_encode_as (Vtuple head_types heads) code start \<Longrightarrow>
   0 \<le> start \<Longrightarrow>
   heads_length vs + start \<le> length code"
proof(induction vs arbitrary: heads head_types tails start code)
  case Nil
  show ?case using Nil(1)
  proof(cases rule: is_head_and_tail.cases)
    case iht_nil
    then show ?thesis using can_encode_as_start[OF Nil(2)] by auto
  qed
next
  case (Cons vh vt)
  show ?case using Cons.prems(1)
  proof(cases rule: is_head_and_tail.cases)
    case (iht_static ys ts v)
    show ?thesis using Cons.prems(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre1 post1 code1)

      obtain vh_code where Vh_code : "encode_static vh = Ok vh_code"
        using Cons.prems iht_static Estatic
        by(cases "encode_static vh"; auto)

      then obtain ys_code where
        Ys_code : "those_err (map encode_static ys) = Ok ys_code" and
        Code : "code1 = vh_code @ concat ys_code"
        using Cons.prems iht_static Estatic
        by(cases "those_err (map encode_static ys)"; auto)

      have Enc' : "can_encode_as (Vtuple ts ys) (vh_code @ concat ys_code @ []) (length vh_code)"
      proof(rule can_encode_as.Estatic)
        show "abi_type_isstatic (abi_get_type (Vtuple ts ys))"
          using Estatic iht_static by auto
      next
        show "abi_value_valid (Vtuple ts ys)"
          using Estatic iht_static by(auto simp add: tuple_value_valid_aux_def)
      next
        show "encode_static (Vtuple ts ys) = Ok (concat ys_code)"
          using Ys_code by auto
      qed

      hence Enc : "can_encode_as (Vtuple ts ys) (vh_code @ concat ys_code) (length vh_code)"
        by auto

      show ?thesis using Cons.IH[OF iht_static(3) Enc] 
          Cons.prems iht_static Estatic Vh_code Ys_code Code encode_static_size
        by(auto)
    next
      case (Etuple_dyn t1 heads1 head_types1 tails1)
      have False using is_head_and_tail_head_types_elem[OF Cons.prems(1) Etuple_dyn(2)]
                       Etuple_dyn by auto
      then show ?thesis by auto
    qed
  next
    case (iht_dynamic ys ts tails' ptr)
    show ?thesis using Cons.prems(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre1 post1 code1)

      obtain ys_code where
        Ys_code : "those_err (map encode_static ys) = Ok ys_code" and
        Code : "code1 = encode_int ptr @ concat ys_code"
        using Cons.prems iht_dynamic Estatic
        by(cases "those_err (map encode_static ys)"; auto)

      have Enc' : "can_encode_as (Vtuple ts ys) (encode_int ptr @ concat ys_code @ []) 
        (length (encode_int ptr))"
      proof(rule can_encode_as.Estatic)
        show "abi_type_isstatic (abi_get_type (Vtuple ts ys))"
          using Estatic iht_dynamic by auto
      next
        show "abi_value_valid (Vtuple ts ys)"
          using Estatic iht_dynamic by(auto simp add: tuple_value_valid_aux_def)
      next
        show "encode_static (Vtuple ts ys) = Ok (concat ys_code)"
          using Ys_code by auto
      qed

      hence Enc : "can_encode_as (Vtuple ts ys) (encode_int ptr @ concat ys_code) 
                   (length (encode_int ptr))"
        by auto

      have Ptlen : "length (encode_int ptr) = 32"
        by(auto simp add:word_rsplit_def bin_rsplit_len)

      show ?thesis using Cons.IH[OF iht_dynamic(4) Enc] Ptlen
          Cons.prems iht_dynamic Estatic Ys_code Code encode_static_size
        by(auto)
    next
      case (Etuple_dyn t heads head_types tails)
      have False using is_head_and_tail_head_types_elem[OF Cons.prems(1) Etuple_dyn(2)]
                       Etuple_dyn by auto
      then show ?thesis by auto
    qed
  qed
qed

lemma some_somes:
"Some x \<in> set optl \<Longrightarrow>
 x \<in> set (somes optl)"
proof(induction optl arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a optl)
  then show ?case by(cases a; auto)
qed

lemma map_elem' :
  "x \<in> set (map f l) \<Longrightarrow>
     (\<exists> x' . x' \<in> set l \<and> f x' = x)"
  by(induction l arbitrary: f x; auto)

(* helper lemma for "picking a value out of the middle" of the
   heads list (instead of pulling from the beginning)
*)
lemma is_head_and_tail_heads_static_split_precise [rule_format] :
"is_head_and_tail (vs) heads head_types tails \<Longrightarrow> 
    vs = vpre @ v # vpost \<Longrightarrow>
    list_all abi_value_valid vs \<Longrightarrow>
    abi_type_isstatic (abi_get_type v) \<Longrightarrow>
    (\<exists> hpre hpost .
       heads = hpre @ v # hpost \<and>
       length hpre = length vpre \<and>
       (\<forall> codes . those_err (map encode_static hpre) = Ok codes \<longrightarrow>
                  list_all abi_value_valid_aux heads \<longrightarrow>
                  length (concat codes) = heads_length vpre))"
proof(induction arbitrary: vpre v vpost rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs1 ys1 ts1 tails1 x1 v1)
  then show ?case
  proof(cases vpre)
    case Nil
    then show ?thesis using iht_static by(auto)
  next
    case (Cons vpre_h vpre_t)
    then obtain hpre hpost where
      Vpre_post : "ys1 = hpre @ v # hpost" and
      Vpre_len : "length hpre = length vpre_t" and
      Vpre_codes : "\<And> codes .
           those_err (map encode_static hpre) = Ok codes \<Longrightarrow>
           list_all abi_value_valid_aux ys1 \<Longrightarrow> 
           int (length (concat codes)) = heads_length vpre_t"
      using iht_static.prems iht_static.hyps iht_static.IH[of vpre_t v vpost]
      by(auto)

    show ?thesis
    proof(rule exI[of _ "x1#hpre"]; rule exI[of _ hpost])
      have C3 : "(\<forall>codes.
                  those_err (map encode_static (x1 # hpre)) = Ok codes \<longrightarrow>
                  list_all abi_value_valid_aux (x1 # ys1) \<longrightarrow> 
                  int (length (concat codes)) = heads_length vpre)"
      proof(rule allI; rule impI; rule impI)
        fix codes
        assume Henc : "those_err (map encode_static (x1 # hpre)) = Ok codes"
        assume Hvalid : "list_all abi_value_valid_aux (x1 # ys1)"

        obtain vpre_h_code where Vpre_h_code : "encode_static vpre_h = Ok vpre_h_code"
          using Vpre_post Henc Cons iht_static.prems iht_static.hyps
          by(cases "encode_static vpre_h"; auto)

        obtain hpre_codes where Hpre_codes : 
          "those_err (map encode_static hpre) = Ok hpre_codes" and
          Hcode : "vpre_h_code # hpre_codes = codes"
          using Vpre_post Vpre_h_code Henc Cons iht_static.prems iht_static.hyps
          by(cases "those_err (map encode_static hpre)"; auto)

        show "int (length (concat codes)) = heads_length vpre"
          using Henc Hvalid Vpre_post Vpre_len Vpre_codes Vpre_h_code Hpre_codes
                Cons iht_static.prems iht_static.hyps encode_static_size
          by(auto)
      qed
      show "x1 # ys1 = (x1 # hpre) @ v # hpost \<and>
            length (x1 # hpre) = length vpre \<and>
            (\<forall>codes.
                those_err (map encode_static (x1 # hpre)) = Ok codes \<longrightarrow>
                list_all abi_value_valid_aux (x1 # ys1) \<longrightarrow> 
                int (length (concat codes)) = heads_length vpre)"
        using Vpre_post Vpre_len Vpre_codes Cons iht_static C3 by(auto)
    qed
  qed
next
  case (iht_dynamic xs1 ys1 ts1 tails1 x1 ptr1)
  show ?case
  proof(cases vpre)
    case Nil
    then show ?thesis using iht_dynamic by(auto)
  next
    case (Cons vpre_h vpre_t)
    then obtain hpre hpost where
      Vpre_post : "ys1 = hpre @ v # hpost" and
      Vpre_len : "length hpre = length vpre_t" and
      Vpre_codes : "\<And> codes .
           those_err (map encode_static hpre) = Ok codes \<Longrightarrow>
           list_all abi_value_valid_aux ys1 \<Longrightarrow> 
           int (length (concat codes)) = heads_length vpre_t"
      using iht_dynamic.prems iht_dynamic.hyps iht_dynamic.IH[of vpre_t v vpost]
      by(auto)

    show ?thesis
    proof(rule exI[of _ "Vsint (256::nat) ptr1#hpre"]; rule exI[of _ hpost])
      have C3 : "(\<forall>codes.
                  those_err (map encode_static (Vsint (256::nat) ptr1 # hpre)) = Ok codes \<longrightarrow>
                  list_all abi_value_valid_aux (Vsint (256::nat) ptr1 # ys1) \<longrightarrow> 
                  int (length (concat codes)) = heads_length vpre)"
      proof(rule allI; rule impI; rule impI)
        fix codes
        assume Henc : "those_err (map encode_static (Vsint (256::nat) ptr1 # hpre)) = Ok codes"
        assume Hvalid : "list_all abi_value_valid_aux (Vsint (256::nat) ptr1 # ys1)"

        obtain vpre_h_code where Vpre_h_code :
          "encode_static (Vsint (256::nat) ptr1) = Ok vpre_h_code"
          using Vpre_post Henc Cons
          by(cases "encode_static vpre_h"; auto)

        obtain hpre_codes where Hpre_codes : 
          "those_err (map encode_static hpre) = Ok hpre_codes" and
          Hcode : "vpre_h_code # hpre_codes = codes"
          using Vpre_post Vpre_h_code Henc Cons iht_dynamic.prems iht_dynamic.hyps
          by(cases "those_err (map encode_static hpre)"; auto)

        show "int (length (concat codes)) = heads_length vpre"
          using Henc Hvalid Vpre_post Vpre_len Vpre_codes Vpre_h_code Hpre_codes
                Cons iht_dynamic.prems iht_dynamic.hyps int_length
          by(auto)
      qed
      show "Vsint 256 ptr1 # ys1 = (Vsint 256 ptr1 # hpre) @ v # hpost \<and>
            length (Vsint 256 ptr1 # hpre) = length vpre \<and>
            (\<forall>codes.
                those_err (map encode_static (Vsint 256 ptr1 # hpre)) = Ok codes \<longrightarrow>
                list_all abi_value_valid_aux (Vsint 256 ptr1 # ys1) \<longrightarrow> 
                int (length (concat codes)) = heads_length vpre)"
        using Vpre_post Vpre_len Vpre_codes Cons iht_static C3 by(auto)
    qed
  qed
qed

lemma those_err_split :
  "those_err (vs @ vs') = Ok out \<Longrightarrow>
    (\<exists> tvs tvs' . those_err vs = Ok tvs \<and> those_err vs' = Ok tvs' \<and>
       tvs @ tvs' = out)"
proof(induction vs arbitrary: vs' out)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)

  then obtain a' where A' : "a = Ok a'"
    by(cases a; auto)

  then obtain vs_vs'_out where Vs'_out : "those_err (vs @ vs') = Ok vs_vs'_out"
    using Cons 
    by(cases "those_err (vs @ vs')"; auto)

  then show ?case using Cons.prems Cons.IH[OF Vs'_out] A' Vs'_out
    by auto
qed

(* helper lemma for "picking a value out of the middle" of
   result of mapping on a list
*)

lemma map_split_precise :
"map f xs = xpre @ x # xpost \<Longrightarrow>
(\<exists> x'pre x' x'post .
    xs = x'pre @ x' # x'post \<and>
    length x'pre = length xpre \<and>
    length x'post = length xpost)"
proof(induction xs arbitrary: f xpre x xpost)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  show ?case
  proof(cases xpre)
    assume Nil' : "xpre = []"
    then show ?thesis using Cons.prems Cons.IH[of f]
      by(auto)
  next
    fix xpre_h xpre_t
    assume Cons' : "xpre = xpre_h#xpre_t"

    then have Map' : "map f xs = xpre_t @ x # xpost"
      using Cons.prems by(auto)

    obtain x'pre x' x'post where
      X' : "xs = x'pre @ x' # x'post \<and> length x'pre = length xpre_t \<and> length x'post = length xpost"
      using Cons.IH[of f, OF Map']
      by(fastforce)

    show ?thesis
    proof(rule exI[of _ "a#x'pre"])
      show "\<exists>x' x'post. a # xs = (a # x'pre) @ x' # x'post \<and> length (a # x'pre) = length xpre \<and> 
            length x'post = length xpost"
        using Cons.prems Cons' X'
        by(auto)
    qed
  qed
qed

lemma my_replicate_map :
  "list_all (\<lambda> x . f x = y) l \<Longrightarrow>
   map f l = replicate (length l) y"
  by(induction l; auto)

lemma is_head_and_tail_heads_tuple_static :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
 abi_type_isstatic (abi_get_type (Vtuple head_types heads))"
proof(induction rule:is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case by(auto)
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case by auto
qed

(* relate behavior of dynamic-data size lower bound to heads-length
   for easier reasoning *)
lemma abi_size_lower_bound_ty_heads_length :
  "ty_heads_length (replicate n t) = n * (abi_size_lower_bound t)"
proof(induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  then show ?case by (simp add: comm_semiring_class.distrib) 
qed

(* finally, some lemmas used for showing our lower bound for encoded value size
   (used to terminate the decoder early if the array size decoded is too large w/r/t
   the data being decoded) is sound *)
lemma is_head_and_tail_static_head_types_eq :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
 list_all abi_type_isstatic (map abi_get_type vs) \<Longrightarrow>
 head_types = map abi_get_type vs"
proof(induction rule: is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case by(auto)
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case by(auto)
qed

lemma is_head_and_tail_dynamic_head_types_eq :
"is_head_and_tail vs heads head_types tails \<Longrightarrow>
 list_all abi_type_isdynamic (map abi_get_type vs) \<Longrightarrow>
 head_types = replicate (length vs) (Tsint 256)"
proof(induction rule: is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  then show ?case by(auto)
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case by(auto)
qed

lemma heads_length_dyn :
"list_all abi_type_isdynamic (map abi_get_type vs) \<Longrightarrow>
 heads_length vs = int (length vs) * 32"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case by(auto)
qed

declare decode'.simps [simp del]

(* can_encode_as holds implies decoder implementation will agree *)
lemma abi_decode_succeed2 :
  "can_encode_as v full_code start \<Longrightarrow>
   (\<exists> len . decode' (abi_get_type v) (start, full_code) = Ok (v, len))"
proof(induction v arbitrary: full_code start)
  case (Vuint x1 x2)
  then show ?case 
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vuint abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
  qed
next
  case (Vsint x1 x2)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vsint abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
  qed
next
  case (Vaddr x)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vaddr abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
  qed

next
  case (Vbool x)
  then show ?case 
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vbool abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
  qed

next
  case (Vfixed x1 x2 x3a)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vfixed abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
  qed

next
case (Vufixed x1 x2 x3a)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vufixed abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
qed
next
  case (Vfbytes x1 x2)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vfbytes abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
qed
next
  case (Vfunction x1 x2)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Vfunction abi_encode_decode_static[OF Estatic(5), of pre post] 
                            encode_static_size[OF Estatic(5)]
    by(auto simp del: decode_static.simps simp add: decode'.simps)
qed
next
  case (Vfarray t n vs)
  then show ?case
  proof(cases "abi_type_isstatic t")
    case True
    show ?thesis using Vfarray(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre post code)
      then show ?thesis using Vfarray abi_encode_decode_static[OF Estatic(5), of pre post] 
                              encode_static_size[OF Estatic(5)]
        by(auto simp del: decode_static.simps simp add: decode'.simps)
    next
      case (Efarray_dyn heads head_types tails)
      then show ?thesis using True by auto
    qed
  next
    case False
    show ?thesis using Vfarray(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre post code)
      then show ?thesis using Vfarray abi_encode_decode_static[OF Estatic(5), of pre post] 
                              encode_static_size[OF Estatic(5)]
        by(auto simp del: decode_static.simps simp add: decode'.simps)
    next
      case (Efarray_dyn heads head_types tails)
      show ?thesis using Efarray_dyn(4)
      proof(cases rule: can_encode_as.cases)
        case (Estatic preX postX codeX)

        then obtain heads_code
          where Heads_ok : "those_err (map encode_static heads) = Ok heads_code"
          and Heads_code : "concat heads_code = codeX"
          using Efarray_dyn False Vfarray
          by(cases "those_err (map encode_static heads)"; auto)

        have Vs_rep : "replicate (length vs) t = map abi_get_type vs"
          using  sym[OF my_replicate_map[of abi_get_type t vs]] Efarray_dyn
          by(auto simp add:farray_value_valid_aux_def)

        have N : "n = length vs"
          using  Efarray_dyn
          by(auto simp add:farray_value_valid_aux_def)

        show ?thesis
        proof(cases "decode'_dyn_tuple_heads (replicate n t) 0 (start, full_code)")
          case (Inr err)

          obtain tpre tbad tpost err'
            where Tbad: "decode' tbad (start + ty_heads_length tpre, full_code) = Err err'"
            and Tbad_t : "replicate n t = tpre @ [tbad] @ tpost"
            and Tbad_static : "abi_type_isstatic tbad"
            using abi_decode'_dyn_tuple_heads_fail[OF Inr]
                  can_encode_as_start[OF Vfarray(2)]
                  can_encode_as_start_nonneg[OF Vfarray(2)]
                  Efarray_dyn
                  ty_heads_length_heads_length[of vs]
                  sym[OF my_replicate_map[of abi_get_type t vs]]
                  heads_length_heads[OF Efarray_dyn(3) Efarray_dyn(4)]
            by(auto simp add:farray_value_valid_aux_def)
 
          have "tbad \<in> set (map abi_get_type vs)"
            using Efarray_dyn(1) Tbad_t
                  my_replicate_map[of abi_get_type t vs]
                  map_split_precise[of abi_get_type vs tpre tbad tpost]
            by(auto simp add:farray_value_valid_aux_def)

          hence Tbad_t' : "tbad = t" using Efarray_dyn
            by(auto simp add:farray_value_valid_aux_def list_all_iff)

          hence False using Efarray_dyn Tbad_static by auto

          thus ?thesis by auto
        next
          case (Inl dec_hd_res)
          obtain vos idxs byteoffset bytes_parsed where Res :
            "dec_hd_res = (vos, idxs, byteoffset, bytes_parsed)"
            by(cases dec_hd_res; auto)

          have Inl' :
            "decode'_dyn_tuple_heads (map abi_get_type vs) 
                (int 0) (start, full_code) = Ok dec_hd_res"
            using Inl unfolding N Vs_rep by auto

          have Start_fullcode : "(min (length full_code) (nat start)) = nat start"
            using can_encode_as_start[OF Vfarray(2)]
                  can_encode_as_start_nonneg[OF Vfarray(2)]
            by auto

          have Offs' : 
            "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (start + offset))"
          proof-
            fix offset v
            have C' : "start + offset = offset + start" by auto
            then show "(offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (start + offset)"
              using Efarray_dyn(5)[of offset v] unfolding C' by auto
          qed

          have Wb : "ht_wellbehaved idxs (map abi_get_type vs) vos"
          and Head_succeed :
            "those (map2 ht_combine vos 
               (map (\<lambda>to. case to of None \<Rightarrow> None 
                  | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) idxs)) = 
                                                                            Some heads \<and>
             map (\<lambda>x. fst x + int (length (take (nat start) full_code))) tails = somes idxs \<and>
             byteoffset = heads_length vs + int (length []) \<and> 
             ht_wellbehaved idxs (map abi_get_type vs) vos"
            using 
                  can_encode_as_start[OF Vfarray(2)]
                  can_encode_as_start_nonneg[OF Vfarray(2)]
                  abi_decode'_dyn_tuple_heads_succeed
                    [OF Efarray_dyn(3), 
                     of "[]" "take (nat start) full_code" "drop (nat start) full_code" "[]"
                        vos idxs byteoffset bytes_parsed] Inl'
                 Start_fullcode Res Efarray_dyn Vs_rep Offs' N
            by(auto)

          have Start_fullcode' : "int (length (take (nat start) full_code)) = start" 
            using Start_fullcode can_encode_as_start_nonneg[OF Vfarray(2)]
            by(auto)

          have Combine :
            "those (map2 ht_combine vos (map (\<lambda>to. case to of None \<Rightarrow> None 
                    | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) idxs)) =
             those (map2 ht_combine vos (map (case_option None (\<lambda>t. Some (t - start))) idxs))"
            unfolding Start_fullcode' by auto

          have Ht2_combine' :
            "those (map2 ht_combine vos (map (case_option None (\<lambda>t. Some (t - start))) idxs)) =
              Some heads"
            using 
                Head_succeed
                Start_fullcode'
                can_encode_as_start[OF Vfarray(2)]
                can_encode_as_start_nonneg[OF Vfarray(2)]
            unfolding Combine
            by(auto)

          show ?thesis
          proof(cases "decode'_dyn_tuple_tails idxs (replicate n t) 
                          vos byteoffset (start, full_code)")
            case (Inr err)

            have Wb' : "ht_wellbehaved idxs (replicate n t) vos"
              using Wb Vs_rep N by auto

            obtain offset' tbad err'
              where Tbad_in : "(Some offset', tbad) \<in> set (zip idxs (replicate n t))" and
                    Tbad_bad : "decode' tbad (offset', full_code) = Err err'"
              using abi_decode'_dyn_tuple_tails_fail[OF Inr Wb']
              by auto

            obtain vbad where Vbad1 : "abi_get_type vbad = tbad" 
                        and Vbad2: "(offset' - start, vbad) \<in> set tails"
              using is_head_and_tail_wellbehaved[OF Efarray_dyn(3) Wb, of start offset' tbad] 
                  Head_succeed
                  Start_fullcode'
                  can_encode_as_start[OF Vfarray(2)]
                  can_encode_as_start_nonneg[OF Vfarray(2)]
                  Tbad_in
                  Ht2_combine' unfolding sym[OF Vs_rep] N
              by(auto)

            have Vbad3 : "vbad \<in> set vs"
              using is_head_and_tail_tails_elem[OF Efarray_dyn(3) Vbad2] by auto

            have False using Vfarray(1)[OF Vbad3 Efarray_dyn(5)[OF Vbad2]]  Tbad_bad Vbad1
              by(auto)
  
            then show ?thesis by auto
          next
            fix dec_tl_res
            assume Inl'' : 
              "decode'_dyn_tuple_tails idxs (replicate n t) vos byteoffset (start, full_code) = 
                Ok dec_tl_res"
            hence Inl''' : 
              "decode'_dyn_tuple_tails idxs (map abi_get_type vs) vos byteoffset 
                  (start, full_code) = Ok dec_tl_res" using Vs_rep N by auto

            obtain vs_out bytes' where Res_tl : "dec_tl_res = (vs_out, bytes')"
              by(cases dec_tl_res; auto)

            obtain bytes'' where C' :
              "decode' (abi_get_type (Vfarray t n vs)) (start, full_code) = 
              Ok (Vfarray t n vs, bytes'')"
 
              using abi_decode'_dyn_tuple_tails_succeed[of idxs vs vos byteoffset
                    "take (nat start) full_code" "[]" "drop (nat start) full_code" "[]"
                    vs_out bytes', OF _ Efarray_dyn(3) Wb _]
                  Inl' Res Start_fullcode
                  can_encode_as_start[OF Vfarray(2)]
                  can_encode_as_start_nonneg[OF Vfarray(2)] Res_tl
                  Efarray_dyn Offs' Combine Head_succeed Vfarray Inl'''
                  sym[OF Vs_rep] N
              by(auto simp add:decode'.simps Let_def )
            thus ?thesis by auto
          qed
        qed
      next
        case (Etuple_dyn tX headsX head_typesX tailsX)
        then show ?thesis 
          using Efarray_dyn is_head_and_tail_heads_tuple_static[OF Efarray_dyn(3)]
          by(auto simp add:farray_value_valid_aux_def list_ex_iff)
      qed
    qed
  qed
next
case (Vtuple ts vs)
  then show ?case
  proof(cases "abi_type_isstatic (Ttuple ts)")
    case True
    show ?thesis using Vtuple(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre post code)
      then show ?thesis using Vtuple abi_encode_decode_static[OF Estatic(5), of pre post] 
                              encode_static_size[OF Estatic(5)]
        by(auto simp del: decode_static.simps simp add: decode'.simps)
    next
      case (Etuple_dyn t heads head_types tails)
      then show ?thesis using True Vtuple
        by(auto simp add: tuple_value_valid_aux_def list_ex_iff)
    qed
  next
    case False
    show ?thesis using Vtuple(2)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre post code)
      then show ?thesis using Vtuple abi_encode_decode_static[OF Estatic(5), of pre post] 
                              encode_static_size[OF Estatic(5)]
        by(auto simp del: decode_static.simps simp add: decode'.simps)
    next
      case (Etuple_dyn t heads head_types tails)
      show ?thesis using Etuple_dyn(5)
      proof(cases rule: can_encode_as.cases)
        case (Estatic preX postX codeX)

        then obtain heads_code
          where Heads_ok : "those_err (map encode_static heads) = Ok heads_code"
          and Heads_code : "concat heads_code = codeX"
          using Efarray_dyn False Vtuple
          by(cases "those_err (map encode_static heads)"; auto)

        have Vs_ts : "ts = map abi_get_type vs"
          using Etuple_dyn by(auto simp add:tuple_value_valid_aux_def)

        show ?thesis
        proof(cases "decode'_dyn_tuple_heads (ts) 0 (start, full_code)")
          case (Inr err)

          obtain tpre tbad tpost err'
            where Tbad: "decode' tbad (start + ty_heads_length tpre, full_code) = Err err'"
            and Tbad_t : "ts = tpre @ [tbad] @ tpost"
            and Tbad_static : "abi_type_isstatic tbad"
            using abi_decode'_dyn_tuple_heads_fail[OF Inr]
                  can_encode_as_start[OF Vtuple(2)]
                  can_encode_as_start_nonneg[OF Vtuple(2)]
                  Efarray_dyn
                  ty_heads_length_heads_length[of vs]
                  heads_length_heads[OF Etuple_dyn(4) Etuple_dyn(5)] 
                  Vs_ts
            by(auto simp add:tuple_value_valid_aux_def)
 
          have Tbad_tvs : "tbad \<in> set (map abi_get_type vs)"
            using  Tbad_t
                  map_split_precise[of abi_get_type vs tpre tbad tpost] Vs_ts
            by(auto simp add:tuple_value_valid_aux_def)

          hence Tbad_tvs' : "tbad \<in> set ts" using Vs_ts by auto

          obtain vbad_pre vbad vbad_post where
            Vbad_full : "vs = vbad_pre @ vbad # vbad_post" and
            Vbad_full_pre : "length (vbad_pre) = length tpre"
            using Tbad_t sym[OF Vs_ts] map_split_precise[of abi_get_type vs tpre tbad tpost]
            by(auto)

          have Vbad : "vbad \<in> set vs" 
            using Tbad_tvs Vbad_full Vbad_full_pre Vs_ts by(auto)

          have Vbad_t : "abi_get_type vbad = tbad" using Vbad_full Vbad_full_pre Vs_ts Tbad_t
            by(auto)

          have Vbad_heads : "vbad \<in> set heads"
            using is_head_and_tail_vs_elem_static[OF Etuple_dyn(4) Vbad] Tbad_static Vbad_t
            by auto

          have Bad_valid : "list_all abi_value_valid vs"
            using encode_correct_converse_valid[OF Vtuple(2)] Vs_ts
            by(simp add:tuple_value_valid_aux_def list_all_iff)

          hence Bad_valid' : "abi_value_valid vbad" using Vbad
            by(auto simp add: list_all_iff)

          obtain hpre hpost where Heads_bad: "
                   heads = hpre @ vbad # hpost \<and>
                   length hpre = length vbad_pre \<and> 
                    (\<forall>codes. those_err (map encode_static hpre) = Ok codes \<longrightarrow> 
                             list_all abi_value_valid_aux heads \<longrightarrow> 
                              int (length (concat codes)) = heads_length vbad_pre)"
            using Vtuple.IH[OF Vbad, of full_code "start + ty_heads_length tpre"] Tbad
            is_head_and_tail_heads_static_split_precise[OF Etuple_dyn(4) Vbad_full Bad_valid]
            Tbad_static Vbad_t Vtuple Etuple_dyn Vbad_full
            encode_correct_converse_valid[OF Vtuple(2)]
            by(auto)


          hence Heads_bad3' : "\<And> codes . those_err (map encode_static hpre) = Ok codes \<Longrightarrow>
                                         list_all abi_value_valid_aux heads \<Longrightarrow>
                                         int (length (concat codes)) = heads_length vbad_pre"
            by auto

          obtain hpre_codes  where
            Hpre_codes : "those_err (map encode_static hpre) = Ok hpre_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad
              those_err_split[of "map encode_static hpre" "map encode_static (vbad#hpost)"]
            by(cases "those_err (map encode_static hpre)"; auto)

          obtain vbad_hpost_codes where
            Vbad_hpost_codes : "those_err (map encode_static (vbad#hpost)) = Ok vbad_hpost_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad
              those_err_split[of "map encode_static hpre" "map encode_static (vbad#hpost)"]
            by(cases "those_err (map encode_static hpre)"; auto)

          then obtain vbad_code where Vbad_code : "encode_static vbad = Ok vbad_code"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad Vbad_hpost_codes
            by(cases "encode_static vbad"; auto)

          then obtain hpost_codes where Hpost_codes : 
            "those_err (map encode_static hpost) = Ok hpost_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad Hpre_codes
              those_err_split[of "map encode_static (hpre@[vbad])"]
              Estatic(4) Vbad_full
            by(auto)

          have BadEnc : "can_encode_as vbad ((preX @ concat hpre_codes) @ vbad_code @ 
                                             (concat hpost_codes @ postX))
                (int (length (preX @ concat hpre_codes) ))"
          proof(rule can_encode_as.Estatic)
            show "abi_type_isstatic (abi_get_type vbad)" using Tbad_static Vbad_t by auto
          next
            show "abi_value_valid vbad" using Bad_valid' by auto
          next
            show "encode_static vbad = Ok vbad_code" using Vbad_code by auto
          qed

          have Heads_code' : "concat heads_code = concat hpre_codes @ 
                                                  (vbad_code @ concat hpost_codes)"
            using Heads_ok Heads_code Heads_bad Hpre_codes Bad_valid' Tbad_static 
                  Vbad_t Vbad_full Vbad_code Hpost_codes
                  those_err_split[of "map encode_static hpre"
                                     "map encode_static (vbad#hpost)" heads_code]
            by(auto)


          have Tpre_types : "tpre = map abi_get_type vbad_pre"
            using Vbad_full Heads_bad Tbad_t Vs_ts
                  Heads_ok Heads_code Heads_bad Hpre_codes Bad_valid' Tbad_static 
                  Vbad_t  Vbad_code Hpost_codes Vbad_full_pre
                  map_split_precise[of abi_get_type vs tpre tbad tpost]
            by(auto) 

          have BadEnc' : "can_encode_as vbad full_code (start + ty_heads_length tpre)"
            using BadEnc Estatic Heads_ok Heads_code' Heads_bad Tbad_t
            Heads_bad3' Hpre_codes Bad_valid' Tbad_static 
            Vbad_t Vbad_full Vbad_code Hpost_codes Tpre_types
            ty_heads_length_heads_length[of vbad_pre]
            by(auto)

          have False using Vtuple.IH[OF Vbad, of full_code "start + ty_heads_length tpre"]
            Tbad
            Tbad_static Vbad_t Vtuple Etuple_dyn Vbad_full BadEnc'
            by(simp add:tuple_value_valid_aux_def)


          thus ?thesis by auto
        next
          case (Inl dec_hd_res)
          obtain vos idxs byteoffset bytes_parsed where Res :
            "dec_hd_res = (vos, idxs, byteoffset, bytes_parsed)"
            by(cases dec_hd_res; auto)

          have Inl' :
            "decode'_dyn_tuple_heads (map abi_get_type vs) 
                (int 0) (start, full_code) = Ok dec_hd_res"
            using Inl Vs_ts  by auto

          have Start_fullcode : "(min (length full_code) (nat start)) = nat start"
            using can_encode_as_start[OF Vtuple(2)]
                  can_encode_as_start_nonneg[OF Vtuple(2)]
            by auto

          have Offs' : 
            "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (start + offset))"
          proof-
            fix offset v
            have C' : "start + offset = offset + start" by auto
            then show "(offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (start + offset)"
              using Etuple_dyn(6)[of offset v] unfolding C' by auto
          qed

          have Wb : "ht_wellbehaved idxs (map abi_get_type vs) vos"
          and Head_succeed :
            "those (map2 ht_combine vos 
               (map (\<lambda>to. case to of None \<Rightarrow> None 
                  | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) idxs)) = 
                                                                            Some heads \<and>
             map (\<lambda>x. fst x + int (length (take (nat start) full_code))) tails = somes idxs \<and>
             byteoffset = heads_length vs + int (length []) \<and> 
             ht_wellbehaved idxs (map abi_get_type vs) vos"
            using 
                  can_encode_as_start[OF Vtuple(2)]
                  can_encode_as_start_nonneg[OF Vtuple(2)]
                  abi_decode'_dyn_tuple_heads_succeed
                    [OF Etuple_dyn(4), 
                     of "[]" "take (nat start) full_code" "drop (nat start) full_code" "[]"
                        vos idxs byteoffset bytes_parsed] Inl'
                 Start_fullcode Res Etuple_dyn Vs_ts Offs' 
            by(auto)

          have Start_fullcode' : "int (length (take (nat start) full_code)) = start" 
            using Start_fullcode can_encode_as_start_nonneg[OF Vtuple(2)]
            by(auto)

          have Combine :
            "those (map2 ht_combine vos (map (\<lambda>to. case to of None \<Rightarrow> None 
                    | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) idxs)) =
             those (map2 ht_combine vos (map (case_option None (\<lambda>t. Some (t - start))) idxs))"
            unfolding Start_fullcode' by auto

          have Ht2_combine' :
            "those (map2 ht_combine vos (map (case_option None (\<lambda>t. Some (t - start))) idxs)) =
              Some heads"
            using 
                Head_succeed
                Start_fullcode'
                can_encode_as_start[OF Vtuple(2)]
                can_encode_as_start_nonneg[OF Vtuple(2)]
            unfolding Combine
            by(auto)

          show ?thesis
          proof(cases "decode'_dyn_tuple_tails idxs (map abi_get_type vs) 
                          vos byteoffset (start, full_code)")
            case (Inr err)
            obtain offset' tbad err'
              where Tbad_in : "(Some offset', tbad) \<in> set (zip idxs (map abi_get_type vs))" and
                    Tbad_bad : "decode' tbad (offset', full_code) = Err err'"
              using abi_decode'_dyn_tuple_tails_fail[OF Inr Wb] 
              by auto

            obtain vbad where Vbad1 : "abi_get_type vbad = tbad" 
                        and Vbad2: "(offset' - start, vbad) \<in> set tails"
              using is_head_and_tail_wellbehaved[OF Etuple_dyn(4) Wb, of start offset' tbad] 
                  Head_succeed
                  Start_fullcode'
                  can_encode_as_start[OF Vtuple(2)]
                  can_encode_as_start_nonneg[OF Vtuple(2)]
                  Tbad_in
                  Ht2_combine' unfolding Vs_ts
              by(auto)

            have Vbad3 : "vbad \<in> set vs"
              using is_head_and_tail_tails_elem[OF Etuple_dyn(4) Vbad2] by auto

            have False using Vtuple(1)[OF Vbad3 Etuple_dyn(6)[OF Vbad2]] Tbad_bad Vbad1
              by(auto)
  
            then show ?thesis by auto
          next
            fix dec_tl_res
            assume Inl'' : 
              "decode'_dyn_tuple_tails idxs (map abi_get_type vs) 
                    vos byteoffset (start, full_code) = 
                Ok dec_tl_res"
            hence Inl''' : 
              "decode'_dyn_tuple_tails idxs (map abi_get_type vs) vos byteoffset 
                  (start, full_code) = Ok dec_tl_res" using Vs_ts by auto

            obtain vs_out bytes' where Res_tl : "dec_tl_res = (vs_out, bytes')"
              by(cases dec_tl_res; auto)

            have Dyn' : "list_ex abi_type_isdynamic (map abi_get_type vs)"
              using Etuple_dyn
              by(auto simp add: list_all_iff list_ex_iff tuple_value_valid_aux_def)

            obtain bytes'' where C' :
              "decode' (abi_get_type (Vtuple ts vs)) (start, full_code) = 
              Ok (Vtuple ts vs, bytes'')"
 
              using abi_decode'_dyn_tuple_tails_succeed[of idxs vs vos byteoffset
                    "take (nat start) full_code" "[]" "drop (nat start) full_code" "[]"
                    vs_out bytes', OF _ Etuple_dyn(4) Wb _]
                  Inl' Res Start_fullcode
                  can_encode_as_start[OF Vtuple(2)]
                  can_encode_as_start_nonneg[OF Vtuple(2)] Res_tl
                  Etuple_dyn Offs' Combine Head_succeed Vtuple Inl'''
                  Vs_ts Dyn'
              by(auto simp add:decode'.simps Let_def )
            thus ?thesis by auto
          qed
        qed
      next
        case Etuple_dyn' : (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis
          using Etuple_dyn is_head_and_tail_heads_tuple_static[OF Etuple_dyn(4)]
          by(auto simp add:tuple_value_valid_aux_def list_ex_iff list_all_iff)
      qed
    qed
  qed
next        
  case (Vbytes bs)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis by auto
  next
    case (Ebytes pre post count code)

    show ?thesis using Ebytes(6)
    proof(cases rule: can_encode_as.cases)
      case (Estatic preX postX codeX)
    
      obtain n_div n_mod where Divmod: "divmod_nat (length bs) 32 = (n_div, n_mod)"
        by(cases "divmod_nat (length bs) 32"; auto)

      have Check1 : "check_padding (length bs) (pad_bytes bs @ post)" using Divmod
      proof(cases n_mod)
        case 0
        then show ?thesis using Divmod by(auto)
      next
        case (Suc nat)
        then show ?thesis using Divmod by(auto simp add:Let_def)
      qed

      show ?thesis using Check1 Vbytes Ebytes Estatic
          uint_reconstruct_full[of 256 "int (length bs)"]
          uint_reconstruct_full'[of 256 "int (length bs)"]
          pad_bytes_len_gt[of bs] pad_bytes_prefix[of bs] int_length
        by(auto simp add: decode'.simps Let_def 
              simp del: check_padding.simps pad_bytes.simps)
    qed
  qed
next
  case (Vstring s)
  then show ?case
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis by auto
  next
    case (Estring l)
    show ?thesis using Estring(3)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre post code)
      then show ?thesis by auto
    next
      case (Ebytes pre post count code)
  
      show ?thesis using Ebytes(6)
      proof(cases rule: can_encode_as.cases)
        case (Estatic preX postX codeX)
      
        obtain n_div n_mod where Divmod: "divmod_nat (length l) 32 = (n_div, n_mod)"
          by(cases "divmod_nat (length l) 32"; auto)
  
        have Check1 : "check_padding (length l) (pad_bytes l @ post)" using Divmod
        proof(cases n_mod)
          case 0
          then show ?thesis using Divmod by(auto)
        next
          case (Suc nat)
          then show ?thesis using Divmod by(auto simp add:Let_def)
        qed
  
        show ?thesis using Check1 Vstring Estring Ebytes Estatic
            uint_reconstruct_full[of 256 "int (length l)"]
            uint_reconstruct_full'[of 256 "int (length l)"]
            pad_bytes_len_gt[of l] pad_bytes_prefix[of l] int_length
            bytes_to_string_to_bytes[of s]
          by(auto simp add: decode'.simps Let_def 
                simp del: check_padding.simps pad_bytes.simps
                bytes_to_string.simps string_to_bytes.simps)
      qed
    qed
  qed
next
  case (Varray t vs)
  show ?case using Varray(2)
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis using Varray
      by(auto simp del: decode_static.simps simp add: decode'.simps)
  next
    case (Earray heads head_types tails)
      (* idea: need to get count first *)
    show ?thesis using Earray(3)
    proof(cases rule: can_encode_as.cases)
      case (Estatic pre1 post1 code1)
      show ?thesis using Earray(4)
      proof(cases rule: can_encode_as.cases)
        case Estatic' : (Estatic pre2 post2 code2)
        then obtain heads_code
          where Heads_ok : "those_err (map encode_static heads) = Ok heads_code"
          and Heads_code : "concat heads_code = code2"
          using Efarray_dyn Varray
          by(cases "those_err (map encode_static heads)"; auto)

        have Vs_rep : "replicate (length vs) t = map abi_get_type vs"
          using  sym[OF my_replicate_map[of abi_get_type t vs]] Earray
          by(auto simp add:array_value_valid_aux_def)

        show ?thesis
        proof(cases "decode'_dyn_tuple_heads (replicate (length vs) t) 0
               (int (length pre2), pre1 @ encode_int (int (length vs)) @ post1)")
        case (Inr err)
          obtain tpre tbad tpost err'
            where Tbad: "decode' tbad (start + 32 + ty_heads_length tpre, full_code) = Err err'"
            and Tbad_t : "replicate (length vs) t = tpre @ [tbad] @ tpost"
            and Tbad_static : "abi_type_isstatic tbad"
            using abi_decode'_dyn_tuple_heads_fail[OF Inr]
                  can_encode_as_start[OF Varray(2)]
                  can_encode_as_start_nonneg[OF Varray(2)]
                  Earray Estatic Estatic' Heads_ok
                  int_length[of "int (length vs)"]
                  uint_reconstruct_full[of 256 "int (length vs)"]
                  ty_heads_length_heads_length[of vs]
                  sym[OF my_replicate_map[of abi_get_type t vs]]
                  heads_length_heads[OF Earray(2) Earray(4)]
            by(auto simp add:array_value_valid_aux_def)
 
          have Tbad_tvs : "tbad \<in> set (map abi_get_type vs)"
            using  Tbad_t
                  map_split_precise[of abi_get_type vs tpre tbad tpost] Vs_rep
            by(auto simp add:tuple_value_valid_aux_def)

          hence Tbad_tvs' : "tbad \<in> set (replicate (length vs) t)" using Vs_rep by auto

          hence Tbad_is_t : "tbad = t" by auto

          obtain vbad_pre vbad vbad_post where
            Vbad_full : "vs = vbad_pre @ vbad # vbad_post" and
            Vbad_full_pre : "length (vbad_pre) = length tpre"
            using Tbad_t Vs_rep map_split_precise[of abi_get_type vs tpre tbad tpost]
            by(auto)

          have Vbad : "vbad \<in> set vs" 
            using Tbad_tvs Vbad_full Vbad_full_pre Vs_rep by(auto)

          have Vbad_t : "abi_get_type vbad = tbad" using Vbad_full Vbad_full_pre Vs_rep Tbad_t
            by(auto)

          have Vbad_heads : "vbad \<in> set heads"
            using is_head_and_tail_vs_elem_static[OF Earray(2) Vbad] Tbad_static Vbad_t
            by auto

          have Bad_valid : "list_all abi_value_valid vs"
            using encode_correct_converse_valid[OF Varray(2)] Vs_rep
            by(simp add:array_value_valid_aux_def list_all_iff)

          hence Bad_valid' : "abi_value_valid vbad" using Vbad
            by(auto simp add: list_all_iff)

          obtain hpre hpost where Heads_bad: "
                   heads = hpre @ vbad # hpost \<and>
                   length hpre = length vbad_pre \<and> 
                    (\<forall>codes. those_err (map encode_static hpre) = Ok codes \<longrightarrow> 
                             list_all abi_value_valid_aux heads \<longrightarrow> 
                              int (length (concat codes)) = heads_length vbad_pre)"
            using Varray.IH[OF Vbad, of full_code "start + 32 + ty_heads_length tpre"] Tbad
            is_head_and_tail_heads_static_split_precise[OF Earray(2) Vbad_full Bad_valid]
            Tbad_static Vbad_t Varray Etuple_dyn Vbad_full
            encode_correct_converse_valid[OF Varray(2)]
            by(auto)

          hence Heads_bad3' : "\<And> codes . those_err (map encode_static hpre) = Ok codes \<Longrightarrow>
                                         list_all abi_value_valid_aux heads \<Longrightarrow>
                                         int (length (concat codes)) = heads_length vbad_pre"
            by auto

          obtain hpre_codes  where
            Hpre_codes : "those_err (map encode_static hpre) = Ok hpre_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad
              those_err_split[of "map encode_static hpre" "map encode_static (vbad#hpost)"]
            by(cases "those_err (map encode_static hpre)"; auto)

          obtain vbad_hpost_codes where
            Vbad_hpost_codes : "those_err (map encode_static (vbad#hpost)) = Ok vbad_hpost_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad
              those_err_split[of "map encode_static hpre" "map encode_static (vbad#hpost)"]
            by(cases "those_err (map encode_static hpre)"; auto)

          then obtain vbad_code where Vbad_code : "encode_static vbad = Ok vbad_code"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad Vbad_hpost_codes
            by(cases "encode_static vbad"; auto)

          then obtain hpost_codes where Hpost_codes : 
            "those_err (map encode_static hpost) = Ok hpost_codes"
            using Tbad_static Vbad_t Vbad_full Heads_ok Heads_bad Hpre_codes
              those_err_split[of "map encode_static (hpre@[vbad])"]
              Estatic(4) Vbad_full
            by(auto)

          have BadEnc : "can_encode_as vbad ((pre2 @ concat hpre_codes) @ vbad_code @ 
                                             (concat hpost_codes @ post2))
                (int (length (pre2 @ concat hpre_codes) ))"
          proof(rule can_encode_as.Estatic)
            show "abi_type_isstatic (abi_get_type vbad)" using Tbad_static Vbad_t by auto
          next
            show "abi_value_valid vbad" using Bad_valid' by auto
          next
            show "encode_static vbad = Ok vbad_code" using Vbad_code by auto
          qed

          have Heads_code' : "concat heads_code = concat hpre_codes @ 
                                          (vbad_code @ concat hpost_codes)"
            using Heads_ok Heads_code Heads_bad Hpre_codes Bad_valid' Tbad_static 
                  Vbad_t Vbad_full Vbad_code Hpost_codes
                  those_err_split[of "map encode_static hpre"
                                     "map encode_static (vbad#hpost)" heads_code]
            by(auto)

          have Tpre_types : "tpre = map abi_get_type vbad_pre"
            using Vbad_full Tbad_t Vs_rep
                  Heads_ok Heads_code Hpre_codes Bad_valid' Tbad_static 
                  Vbad_t Vbad_code Hpost_codes Vbad_full_pre
                  map_split_precise[of abi_get_type vs tpre tbad tpost]
            by(auto)

          have BadEnc' : "can_encode_as vbad full_code (start + 32 + ty_heads_length tpre)"
            using BadEnc Estatic Estatic' Heads_ok Heads_code' Heads_bad Tbad_t
            Heads_bad3' Hpre_codes Bad_valid' Tbad_static 
            Vbad_t Vbad_full Vbad_code Hpost_codes Tpre_types 
            ty_heads_length_heads_length[of vbad_pre] 
            by(auto)

          have False using Varray.IH[OF Vbad, of full_code "start + 32 + ty_heads_length tpre"]
            Tbad BadEnc'
            Tbad_static Vbad_t Varray Etuple_dyn Vbad_full
            by(simp add:array_value_valid_aux_def)

          thus ?thesis by auto
        next
          case (Inl dec_hd_res)
          obtain vos idxs byteoffset bytes_parsed where Res :
            "dec_hd_res = (vos, idxs, byteoffset, bytes_parsed)"
            by(cases dec_hd_res; auto)

          have Inl' :
            "decode'_dyn_tuple_heads (replicate (length vs) t) 
                (int 0) (start + 32, full_code) = Ok dec_hd_res"
            using Inl Vs_rep Estatic Estatic' by(auto)

          have Start_fullcode : "int (min (length full_code) (nat (start + 32))) = start + 32"
            using can_encode_as_start[OF Earray(4)]
                  can_encode_as_start_nonneg[OF Earray(4)]
            by(auto)

          have Offs' : 
            "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> 
                  can_encode_as v full_code (start + 32 + offset))"
          proof-
            fix offset v
            have C' : "start + 32 + offset = offset + start + 32" by auto
            then show "(offset, v) \<in> set tails \<Longrightarrow>
              can_encode_as v full_code (start + 32 + offset)"
              using Earray(5)[of offset v] unfolding C' by(auto)
          qed

          have Start32' : "nat start + 32 = nat (start + 32)" using
                  can_encode_as_start_nonneg[OF Varray(2)] by auto

          have Wb : "ht_wellbehaved idxs (map abi_get_type vs) vos"
          and Head_succeed :
            "those (map2 ht_combine vos 
               (map (\<lambda>to. case to of None \<Rightarrow> None 
                  | Some t \<Rightarrow> Some (t - int (length (take (nat start + 32) full_code)))) idxs)) = 
                                                                            Some heads \<and>
             map (\<lambda>x. fst x + int (length (take (nat start + 32) full_code))) tails = somes idxs \<and>
             byteoffset = heads_length vs + int (length []) \<and> 
             ht_wellbehaved idxs (map abi_get_type vs) vos"
            using 
                  can_encode_as_start[OF Varray(2)]
                  can_encode_as_start_nonneg[OF Varray(2)]
                  abi_decode'_dyn_tuple_heads_succeed
                    [OF Earray(2), 
                     of "[]" "take (nat (start + 32)) full_code" 
                        "drop (nat (start + 32)) full_code" "[]"
                        vos idxs byteoffset bytes_parsed] Inl'
                 Start_fullcode Res Earray Vs_rep Offs' 
             by(auto simp add: Start32')

          have Start_fullcode' : "int (length (take (nat start + 32) full_code)) = start + 32" 
            using Start_fullcode can_encode_as_start_nonneg[OF Varray(2)]
            by(auto)

          have Combine :
            "those (map2 ht_combine vos (map (\<lambda>to. case to of None \<Rightarrow> None 
                    | Some t \<Rightarrow> Some (t - int (length (take (nat start + 32) full_code)))) idxs)) =
             those (map2 ht_combine vos 
                                    (map (case_option None (\<lambda>t. Some (t - (start + 32)))) idxs))"
            unfolding Start_fullcode' by(auto)

          have Ht2_combine' :
            "those (map2 ht_combine vos 
                                    (map (case_option None (\<lambda>t. Some (t - (start + 32)))) idxs)) =
              Some heads"
            using 
                Head_succeed
                Start_fullcode'
                can_encode_as_start[OF Varray(2)]
                can_encode_as_start_nonneg[OF Varray(2)]
            unfolding Combine
            by(auto)

          have LenCheck : "32 + ((int (length vs)) * abi_size_lower_bound t) + start \<le> 
                            int (length full_code)"
            using abi_size_lower_bound_ty_heads_length Varray Earray Estatic Estatic'
          proof(cases "abi_type_isstatic t")
            case True

            then have Ht_rep : "head_types = replicate (length vs) t"
              using Earray
                is_head_and_tail_static_head_types_eq[OF Earray(2)]
                my_replicate_map[of abi_get_type t vs]
              by(auto simp add: array_value_valid_aux_def list_all_iff)

            hence Ht_ty_hl : "ty_heads_length (replicate (length vs) t) =
                               (length vs) * abi_size_lower_bound t"
              using abi_size_lower_bound_ty_heads_length by auto

            hence Ht_hl : "heads_length vs = (length vs) * abi_size_lower_bound t"
              using True ty_heads_length_heads_length
                my_replicate_map[of abi_get_type t vs]
                Earray
                is_head_and_tail_static_head_types_eq[OF Earray(2)]
                sym[OF Ht_rep]
              by(auto simp add: array_value_valid_aux_def list_all_iff)

            thus ?thesis
              using True heads_length_heads[OF Earray(2), of full_code "start + 32"] 
                    Ht_rep
                    Earray(4)
                    can_encode_as_start_nonneg[OF Earray(4)]
              by(auto)
          next
            case False

            hence Vs_dyn : "list_all abi_type_isdynamic (map abi_get_type vs)"
              using Earray my_replicate_map[of abi_get_type t vs]
              by(auto simp add: array_value_valid_aux_def list_all_iff)

            have Ht_rep : "head_types = replicate (length vs) (Tsint 256)"
              using Earray
                is_head_and_tail_dynamic_head_types_eq[OF Earray(2) Vs_dyn]
              by(auto simp add: array_value_valid_aux_def)

            hence Ht_ty_hl : "ty_heads_length (replicate (length vs) t) =
                               (length vs) * abi_size_lower_bound t"
              using abi_size_lower_bound_ty_heads_length by auto

            hence Ht_hl : "heads_length vs = (length vs) * abi_size_lower_bound t"
              using False ty_heads_length_heads_length[of vs]
                Earray
                sym[OF Ht_rep]
                heads_length_dyn[OF Vs_dyn]
              by(auto simp add: array_value_valid_aux_def)

            thus ?thesis
              using False heads_length_heads[OF Earray(2), of full_code "start + 32"] 
                    Ht_rep
                    Earray(4)
                    can_encode_as_start_nonneg[OF Earray(4)]
              by(auto)
          qed

          show ?thesis
          proof(cases "decode'_dyn_tuple_tails idxs (map abi_get_type vs) 
                          vos byteoffset (start + 32, full_code)")
            case (Inr err)
            obtain offset' tbad err'
              where Tbad_in : "(Some offset', tbad) \<in> set (zip idxs (map abi_get_type vs))" and
                    Tbad_bad : "decode' tbad (offset', full_code) = Err err'"
              using abi_decode'_dyn_tuple_tails_fail[OF Inr Wb] 
              by auto

            obtain vbad where Vbad1 : "abi_get_type vbad = tbad" 
                        and Vbad2: "(offset' - (start + 32), vbad) \<in> set tails"
              using is_head_and_tail_wellbehaved[OF Earray(2) Wb, of "start + 32" offset' tbad] 
                  Head_succeed
                  Start_fullcode'
                  can_encode_as_start[OF Varray(2)]
                  can_encode_as_start_nonneg[OF Varray(2)]
                  Tbad_in
                  Ht2_combine' unfolding Vs_rep
              by(auto)

            have Vbad3 : "vbad \<in> set vs"
              using is_head_and_tail_tails_elem[OF Earray(2) Vbad2] by auto

            have False using Varray(1)[OF Vbad3 Earray(5)[OF Vbad2]] Tbad_bad Vbad1
              by(auto)
  
            then show ?thesis by auto
          next
            fix dec_tl_res
            assume Inl'' : 
              "decode'_dyn_tuple_tails idxs (map abi_get_type vs) 
                    vos byteoffset (start + 32, full_code) = 
                Ok dec_tl_res"
            hence Inl''' : 
              "decode'_dyn_tuple_tails idxs (map abi_get_type vs) vos byteoffset 
                  (start + 32, full_code) = Ok dec_tl_res" using Vs_rep by auto

            obtain vs_out bytes' where Res_tl : "dec_tl_res = (vs_out, bytes')"
              by(cases dec_tl_res; auto)

            have Count : "decode_uint (take 32 (drop (nat start) full_code)) = int(length vs)"
              using Estatic int_length[of "length vs"]
              uint_reconstruct_full'[of 256 "length vs"]
              by(auto)

            obtain bytes'' where C' :
              "decode' (abi_get_type (Varray t vs)) (start, full_code) = 
              Ok (Varray t vs, bytes'')"
 
              using abi_decode'_dyn_tuple_tails_succeed[of idxs vs vos byteoffset
                    "take (nat start + 32) full_code" "[]" "drop (nat start + 32) full_code" "[]"
                    vs_out bytes', OF _ Earray(2) Wb _]
                  Inl' Res Start_fullcode Start32'
                  can_encode_as_start[OF Varray(2)]
                  can_encode_as_start_nonneg[OF Varray(2)]
                  can_encode_as_start[OF Earray(4)]
                  can_encode_as_start_nonneg[OF Earray(4)]
                  Res_tl
                  Etuple_dyn Offs' Combine Head_succeed Varray Inl'''
                  Vs_rep Count Earray(4)
                  LenCheck
              by(auto simp add:decode'.simps Let_def simp del:decode_uint.simps)
            thus ?thesis by auto
          qed
        qed

      next
        case (Etuple_dyn tX headsX head_typesX tailsX)
        then show ?thesis 
          using is_head_and_tail_heads_tuple_static[OF Earray(2)]
          by(auto simp add:array_value_valid_aux_def list_ex_iff list_all_iff)
      qed
    qed
  qed
qed

(* Main theorem 3:
   Specification implies successful decoding *)
theorem abi_decode_correct :
  assumes H : "can_encode_as v full_code 0"
  shows "decode (abi_get_type v) full_code = Ok v"
  using encode_correct_converse_valid[OF H] abi_decode_succeed2[OF H]
  by(auto)

lemma abi_decode_static_type_ok :
  "decode_static t (index, full_code) = Ok v \<Longrightarrow>
   abi_get_type v = t"
  by(induction t arbitrary: index full_code v;
        auto simp add:Let_def split:if_splits;
        auto simp add:Let_def split:if_splits sum.splits)

lemma abi_decode'_type_ok :
  "decode' t (index, full_code) = Ok (v, sz) \<Longrightarrow>
   abi_get_type v = t"
proof(induction t arbitrary: index full_code  v sz)
case (Tuint x)
  then show ?case 
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case (Tsint x)
  then show ?case
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case Taddr
  then show ?case 
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case Tbool
  then show ?case
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case (Tfixed x1a x2a)
  then show ?case
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case (Tufixed x1a x2a)
  then show ?case 
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case (Tfbytes x)
  then show ?case
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case Tfunction
  then show ?case
    by(auto simp add:Let_def decode'.simps split:if_splits)
next
  case (Tfarray t x2a)
  show ?case using Tfarray(2) unfolding decode'.simps Tfarray(1)
    by(auto simp add:Let_def split:if_splits sum.splits)
next
  case (Ttuple x)
  then show ?case using Ttuple(2) unfolding decode'.simps Ttuple(1)
    by(auto simp add:Let_def split:if_splits sum.splits)
next
  case Tbytes
  then show ?case unfolding decode'.simps Let_def
    (* TODO: this is a bit slower than it should be. *)
    by(auto split:if_split_asm)
next
  case Tstring
  then show ?case unfolding decode'.simps Let_def
    (* TODO: this is a bit slower than it should be. *)
    by(auto split:if_split_asm)
next
  case (Tarray t)
  show ?case using Tarray(2) unfolding decode'.simps Tarray(1)
    unfolding Let_def
    by(auto split:if_splits sum.splits)
qed

(* helper lemmas for static value decode \<rightarrow> encode lemmas *)
lemma uint_reencode :
 assumes Hcode : "32 \<le> length code"
 shows "encode_int (decode_uint (code)) = take 32 code"
  unfolding encode_int.simps decode_uint.simps word_of_int word_of_int_uint
proof(rule word_rsplit_rcat_size)
  have Hcode' : "min (length code) 32 = 32" using Hcode by auto
  show "size (word_rcat (take 32 code) :: 256 word) = length (take 32 code) * LENGTH(8)"
    using Hcode'
    by(auto simp add: word_size)
qed

lemma sint_reencode :
 assumes Hcode : "32 \<le> length code"
 shows "encode_int (decode_sint (code)) = take 32 code"
  unfolding encode_int.simps decode_sint.simps word_of_int word_sint.Rep_inverse
proof(rule word_rsplit_rcat_size)
  have Hcode' : "min (length code) 32 = 32" using Hcode by auto
  show "size (word_rcat (take 32 code) :: 256 word) = length (take 32 code) * LENGTH(8)"
    using Hcode'
    by(auto simp add: word_size)
qed

lemma abi_decode_encode_static':
  "(\<And> t index (full_code :: 8 word list) . 
    abi_type_valid t \<Longrightarrow>
    0 \<le> index \<Longrightarrow>
    nat index + nat (abi_static_size t) \<le> length full_code \<Longrightarrow>
    decode_static t (index, full_code) = Ok v \<Longrightarrow>
    abi_get_type v = t \<Longrightarrow>
     (abi_value_valid v \<and>
     (\<exists> (code :: 8 word list) . encode_static v = Ok code \<and>
         take (nat (abi_static_size t)) (drop (nat index) full_code) = code)))" and

    "(\<And> v t n index full_code  .
          v = (Vfarray t n vs) \<Longrightarrow>
                  abi_type_valid t \<Longrightarrow>
                  0 \<le>  index \<Longrightarrow>
                  nat index + nat (n * abi_static_size t) \<le> length full_code \<Longrightarrow>
                  decode_static_tup (replicate n t) (index, full_code) = Ok vs \<Longrightarrow>
                  map abi_get_type vs = replicate n t \<Longrightarrow>
                  (list_all abi_value_valid vs \<and>
                  (\<exists> (codes :: 8 word list list) . those_err (map encode_static vs) = Ok codes \<and>
                           take (nat (n * (abi_static_size t))) (drop (nat index) full_code) = 
                           concat codes)))" and

     "(\<And> v ts index full_code  .
          v = (Vtuple ts vs) \<Longrightarrow>
                  list_all abi_type_valid ts \<Longrightarrow>
                  0 \<le> index \<Longrightarrow>
                  nat index + nat (list_sum (map abi_static_size ts)) \<le> length full_code \<Longrightarrow>
                  decode_static_tup (ts) (index, full_code) = Ok vs \<Longrightarrow>
                  map abi_get_type vs = ts \<Longrightarrow>
                  (list_all abi_value_valid vs \<and>
                  (\<exists> (codes :: 8 word list list) . those_err (map encode_static vs) = Ok codes \<and>
                           take (nat (list_sum (map abi_static_size ts))) 
                                (drop (nat index) full_code) = concat codes)))"
proof(induction rule:my_abi_value_induct)
(* Vuint *)
  case (1 n i)
  then show ?case using uint_reencode[of "drop (nat index) full_code"]
    by(auto simp add: Let_def split:if_split_asm simp del:encode_int.simps decode_uint.simps)
next
(* Vsint *)
  case (2 n i)
  then show ?case using sint_reencode[of "drop (nat index) full_code"]
    by(auto simp add: Let_def split:if_split_asm simp del:encode_int.simps decode_sint.simps)
next
(* Vaddr *)
  case (3 x)
  then show ?case using uint_reencode[of "drop (nat index) full_code"]
    by(auto simp add: Let_def split: if_split_asm)
next
(* Vbool *)
  case (4 x)
  have Sz : "32 \<le> length full_code - nat index" using 4 by auto
  then show ?case
  proof(cases x)
    case True
    then show ?thesis using 4 uint_reencode[of "drop (nat index) full_code"] Sz
      by(auto simp add: bool_value_valid_def Let_def split: if_split_asm 
              simp del:encode_int.simps decode_sint.simps)
  next
    case False
    then show ?thesis using 4 uint_reencode[of "drop (nat index) full_code"] Sz
      by(auto simp add: bool_value_valid_def Let_def split: if_split_asm 
              simp del:encode_int.simps decode_sint.simps)
  qed
next
(* Vfixed *)
  case (5 m n r)
  have Sz : "32 \<le> length full_code - nat index" using 5 by auto
  then show ?case using 5 sint_reencode[of "drop (nat index) full_code"]
    by(auto simp add: Let_def Rat.quotient_of_int
               split:if_split_asm simp del:encode_int.simps decode_sint.simps)
next
(* Vufixed *)
  case (6 m n r)
  have Sz : "32 \<le> length full_code - nat index" using 6 by auto
  then show ?case using 6 uint_reencode[of "drop (nat index) full_code"]
    by(auto simp add: Let_def Rat.quotient_of_int
               split:if_split_asm simp del:encode_int.simps decode_sint.simps)
next
(* Fbytes *)
  case (7 n bs)

  obtain dv md where Divmod : "divmod_nat n 32 = (dv, md)"
    by (cases "divmod_nat n 32"; auto)

  have Len32 : "32 \<le> length full_code - nat index" using 7 Divmod
    by(auto)

  hence Len32' : "min (length full_code - nat index) 32 = 32"
    by auto

  show ?case
  proof(cases md)
    case 0
    then have N  : "n = 32" using 7 Divmod
      by(auto simp add:divmod_nat_def)

    show ?thesis using 7 0 Divmod N Len32 Len32'
      by(auto simp add:fbytes_value_valid_def)
  next
    case (Suc md')

    hence Suc' : "n \<noteq> 32" using Divmod by(auto simp add: divmod_nat_def)

    have Check : "check_padding n (drop (nat index) full_code)" using 7 Suc Divmod
      by(cases "check_padding n (drop (nat index) full_code)";
         auto simp add: Let_def fbytes_value_valid_def 
              simp del:pad_bytes.simps check_padding.simps)

    have Min_n : "min (length full_code - nat index) n = n" using Suc 7 by(auto)

    have N_bound : "n < 32" using Suc Divmod 7 Min_n Suc'
      by(auto simp add: fbytes_value_valid_def Let_def)

    have N_bound' : "n - md' = 1" using Suc N_bound Divmod
      by(auto simp add: divmod_nat_def)

    have Len32'' :"length (pad_bytes (take n (drop (nat index) full_code))) = 32"
      using 7 Suc Check Min_n Divmod N_bound' N_bound
      by(auto simp add:Let_def fbytes_value_valid_def)

    then show ?thesis using 7 Divmod Suc Check Min_n N_bound
        check_padding_pad_bytes[OF Check]
      by(auto simp add: Let_def fbytes_value_valid_def
              simp del:pad_bytes.simps check_padding.simps)
  qed
next
  (* function *)
  case (8 i j)
  have Check : "check_padding 24 (drop (nat index) full_code)" using 8
    by(cases "check_padding 24 (drop (nat index) full_code)";
                 auto simp add:Let_def function_value_valid_def divmod_nat_def
                      simp del: check_padding.simps)

  have Valid1 : "uint_value_valid 160 (uint (word_rcat 
                                      (take 20 (drop (nat index) full_code)) :: 160 word))"
    using 8 Check 
    by(auto simp add:Let_def function_value_valid_def divmod_nat_def split:if_split_asm
            simp del: check_padding.simps)

  have Valid2 : "uint_value_valid 32 (uint (word_rcat
                                           (take 4 (drop (20 + nat index) full_code)) :: 32 word))"
    using 8 Check Valid1
    by(auto simp add:Let_def function_value_valid_def divmod_nat_def split:if_split_asm
            simp del: check_padding.simps)


  have Len1 : "length (word_rsplit
                        (word_rcat 
                          (take 20 (drop (nat index) full_code)) :: 160 word) :: 8 word list) = 20"
  proof(rule length_word_rsplit_even_size[of 8])
    show "8 = LENGTH(8)" by auto
  next
    show "size (word_rcat (take 20 (drop (nat index) full_code)) :: 160 word) = 20 * 8"
      by (auto simp add: word_size)
  qed

  have Len2 : "length (word_rsplit (word_rcat
                  (take 4 (drop (20 + nat index) full_code)) :: 32 word) :: 8 word list) = 4"
  proof(rule length_word_rsplit_even_size[of 8])
    show "8 = LENGTH(8)" by auto
  next
    show "size (word_rcat (take 4 (drop (20 + nat index) full_code))  :: 32 word) = 4 * 8"
      by (auto simp add: word_size)
  qed

  have Min1 : "min (length full_code - nat index) 20 = 20"
  using 8 by(auto)

  then have Size1: "size (word_rcat (take 20 (drop (nat index) full_code)) :: 160 word) =
                      length (take 20 (drop (nat index) full_code)) * LENGTH(8)"
    by(auto simp add:word_size) 

  have Min2 : "min (length full_code - (20 + nat index)) 4 = 4"
  using 8 by(auto)

  then have Size2: "size (word_rcat (take 4 (drop (20 + nat index) full_code)) :: 32 word) = 
                      length (take 4 (drop (20 + nat index) full_code)) * LENGTH(8)"
    by(auto simp add:word_size) 


  have Conc'1 : "drop 24 (take 32 (drop (nat index) full_code)) = [0, 0, 0, 0, 0, 0, 0, 0]"
    using 8 Check Valid1 Valid2 Len1 Len2 Min2
      check_padding_pad_bytes[of "24" "(drop (nat index) full_code)"]
    by(auto simp add:Let_def function_value_valid_def divmod_nat_def
        simp del: encode_int.simps decode_uint.simps)

  hence Conc'2 : "take 32 (drop (nat index) full_code) =
    word_rsplit (word_rcat (take 20 (drop (nat index) full_code)) :: 160 word) @ 
    word_rsplit (word_rcat (take 4 (drop (20 + nat index) full_code)) :: 32 word) @ 
    [0, 0, 0, 0, 0, 0, 0, 0]" using 8 Check Valid1 Valid2 Len1 Len2 Min2
    take_add[of 20 12 "(drop (nat index) full_code)"]
    take_add[of 4 8 "take 12 (drop (20 + nat index) full_code)"]
    unfolding word_rsplit_rcat_size[OF Size1]
    unfolding word_rsplit_rcat_size[OF Size2]
    by(simp del: encode_int.simps decode_uint.simps)

  show ?case using 8 Conc'1 Conc'2 Check Valid1 Valid2 Len1 Len2 Min2
    by(auto simp add:Let_def function_value_valid_def divmod_nat_def word_size
        simp del: encode_int.simps decode_uint.simps)
next
  (* Farray *)
  case (9 t' n l)
  obtain dec where Dec: "decode_static_tup (replicate n t') (index, full_code) = Ok dec"
    using "9.prems"
    by(cases "decode_static_tup (replicate n t') (index, full_code)"; auto)

  then have V : "farray_value_valid_aux t' n dec" using "9.prems"
    by(cases "farray_value_valid_aux t' n dec"; auto)

  then show ?case using "9.prems" "9.IH"(1)[of "Vfarray t' n l" t' n index full_code] Dec
                        my_replicate_map[of "abi_get_type" t' l]
    by(auto simp add:farray_value_valid_aux_def list_all_iff)
next
(* Tuple *)
  case (10 ts vs)

  obtain dec where Dec: "decode_static_tup ts (index, full_code) = Ok dec"
    using "10.prems"
    by(cases "decode_static_tup ts (index, full_code) "; auto)

  then have V : "tuple_value_valid_aux ts dec" using "10.prems"
    by(cases "tuple_value_valid_aux ts dec"; auto)

  then show ?case using "10.prems" "10.IH"(2)[of "Vtuple ts vs" ts index full_code] Dec
    by(auto simp add:tuple_value_valid_aux_def list_all_iff list_sum_def)
next
(* Bytes *)
  case (11)
  then show ?case by auto
next
(* String *)
  case (12)
  then show ?case by auto
next
(* Array *)
  case (13 t vs)
  then show ?case by auto
next
(* Nil *)
  case 14
  {
    (* Farray *)
    case 1
    then show ?case by auto
  next
    (* Tuple *)
    case 2
    then show ?case by(auto simp add:list_sum_def)
  }
next
(* Cons *)
  case (15 v' vs)
  {
    (* Farray *)
    case 1
    then obtain n' where N' : "n = Suc n'" by(cases n; auto)

    then obtain dec where Dec : "decode_static (abi_get_type v') (index, full_code) = Ok dec"
      using "1" by (cases "decode_static (abi_get_type v') (index, full_code)"; auto)

    then obtain dec2 where Dec2 : "decode_static_tup (replicate n' (abi_get_type v'))
                             (index + abi_static_size (abi_get_type v'), full_code) = Ok dec2"
      using "1" N'
      by(cases "decode_static_tup (replicate n' (abi_get_type v'))
                             (index + abi_static_size (abi_get_type v'), full_code)";
          auto)

    have Dec' : "decode_static (abi_get_type v') (index, full_code) = Ok v'"
      using 1 Dec Dec2 N' by(auto)

    have Dec2' : "decode_static_tup (replicate n' (abi_get_type v'))
                             (index + abi_static_size (abi_get_type v'), full_code) = Ok vs"
      using 1 Dec Dec2 Dec' N' by(auto)

    have Bound2 : "nat (index + abi_static_size (abi_get_type v')) +
                   nat (int n' * abi_static_size (abi_get_type v'))
                   \<le> length full_code"
      using 1 N' nat_mult_distrib[of "1 + int n'"] nat_mult_distrib[of "int n'"]
                 nat_add_distrib[of "1" "int n'"]
      by(auto)

    hence Bound1 : "nat index + nat (abi_static_size (abi_get_type v')) \<le> length full_code"
      using nat_add_distrib[of "index" "abi_static_size (abi_get_type v')"] 1
      by(auto)

    have TakeDrop :
    "\<And> codes .
       take (nat (int n' * abi_static_size (abi_get_type v'))) 
            (drop (nat (index + abi_static_size (abi_get_type v'))) full_code) = concat codes \<Longrightarrow>
       take (nat ((1 + int n') * abi_static_size (abi_get_type v'))) (drop (nat index) full_code) =
       take (nat (abi_static_size (abi_get_type v'))) (drop (nat index) full_code) @ concat codes"
    proof-
      fix codes :: "8 word list list"
      assume H : "take (nat (int n' * abi_static_size (abi_get_type v'))) 
            (drop (nat (index + abi_static_size (abi_get_type v'))) full_code) = concat codes"

      have Com : "(nat (abi_static_size (abi_get_type v')) + nat index) = 
                  (nat (index + abi_static_size (abi_get_type v')))"
        using abi_static_size_nonneg[of "abi_get_type v'"]  1
        by(auto)

      show "take (nat ((1 + int n') * abi_static_size (abi_get_type v'))) 
                 (drop (nat index) full_code) =
       take (nat (abi_static_size (abi_get_type v'))) (drop (nat index) full_code) @ concat codes"

        using H nat_mult_distrib[of "1 + int n'"] nat_mult_distrib[of "int n'"]
              nat_add_distrib[of "1" "int n'"] 
        by(auto simp add:take_add Com)
    qed

    show ?case using "15.IH"(2)[of "Vfarray t n' vs" t n' 
                                   "index + abi_static_size (abi_get_type v')" full_code]
                          "15.IH"(1)[of t "index" full_code]
                          1 N' Dec' Dec2' abi_static_size_nonneg[of "abi_get_type v'"] Bound2 Bound1 
                          TakeDrop
      by(auto)
  next

    (* Tuple *)
    case 2

    then obtain dec where Dec : "decode_static (abi_get_type v') (index, full_code) = Ok dec"
      using "2" by (cases "decode_static (abi_get_type v') (index, full_code)"; auto)


    then obtain dec2 where Dec2 : "decode_static_tup (map abi_get_type vs)
                             (index + abi_static_size (abi_get_type v'), full_code) = Ok dec2"
      using "2" 
      by(cases "decode_static_tup (map abi_get_type vs)
                             (index + abi_static_size (abi_get_type v'), full_code)";
          auto)

    have Dec' : "decode_static (abi_get_type v') (index, full_code) = Ok v'"
      using 2 Dec Dec2  by(auto)

    have Dec2' : "decode_static_tup (map abi_get_type vs)
                             (index + abi_static_size (abi_get_type v'), full_code) = Ok vs"
      using 2 Dec Dec2 Dec'  by(auto)

    have Tl_nonneg : "0 \<le> foldl (+) 0 (map (abi_static_size \<circ> abi_get_type) vs)" 
      using list_nonneg_sum[of "map (abi_static_size \<circ> abi_get_type) vs"] abi_static_size_nonneg 
      unfolding list_sum_def list_nonneg_def 
      by(auto simp add:list_all_iff)

    have Bound2 : "nat index + nat (foldl (+) (abi_static_size (abi_get_type v')) 
                                   (map (abi_static_size \<circ> abi_get_type) vs)) \<le> length full_code"
      using nat_add_distrib[of "index" "abi_static_size (abi_get_type v')"] 2
            abi_static_size_nonneg[of "abi_get_type v'"]
            sym[OF foldl_plus[of "abi_static_size (abi_get_type v')"  0
                                 "(map (abi_static_size \<circ> abi_get_type) vs)"]]
      by(auto simp add:list_sum_def)

    hence Bound2' : "nat (index + abi_static_size (abi_get_type v')) + 
                     nat (list_sum (map abi_static_size (map abi_get_type vs))) \<le> length full_code"
      unfolding list_sum_def
      using sym[OF foldl_plus[of "abi_static_size (abi_get_type v')"  0
                                 "(map (abi_static_size \<circ> abi_get_type) vs)"]] 2
      abi_static_size_nonneg[of "abi_get_type v'"]
      nat_add_distrib Tl_nonneg
      by(auto)

    have Bound1 : "nat index + nat (abi_static_size (abi_get_type v')) \<le> length full_code"
      using nat_add_distrib[of "index" "abi_static_size (abi_get_type v')"] 2
            abi_static_size_nonneg[of "abi_get_type v'"]
            sym[OF foldl_plus[of "abi_static_size (abi_get_type v')"  0
                                 "(map (abi_static_size \<circ> abi_get_type) vs)"]]
            Tl_nonneg
      by(auto simp add:list_sum_def)


    have TakeDrop :
    "\<And> codes .
       take (nat (list_sum (map (abi_static_size \<circ> abi_get_type) vs)))
            (drop (nat (index + abi_static_size (abi_get_type v'))) full_code) = concat codes \<Longrightarrow>
       take (nat (list_sum (abi_static_size (abi_get_type v') # 
                            map (abi_static_size \<circ> abi_get_type) vs)))
            (drop (nat index) full_code) =
       take (nat (abi_static_size (abi_get_type v'))) (drop (nat index) full_code) @ concat codes"
    proof-
      fix codes :: "8 word list list"
      assume H : "take (nat (list_sum (map (abi_static_size \<circ> abi_get_type) vs)))
            (drop (nat (index + abi_static_size (abi_get_type v'))) full_code) = concat codes"

      have Com : "(nat (abi_static_size (abi_get_type v')) + nat index) = 
                  (nat (index + abi_static_size (abi_get_type v')))"
        using abi_static_size_nonneg[of "abi_get_type v'"]  2
        by(auto)

      show "take (nat (list_sum (abi_static_size (abi_get_type v') # 
                            map (abi_static_size \<circ> abi_get_type) vs)))
            (drop (nat index) full_code) =
       take (nat (abi_static_size (abi_get_type v'))) (drop (nat index) full_code) @ concat codes"

        using H nat_add_distrib[of "index" "abi_static_size (abi_get_type v')"]  2
                sym[OF foldl_plus[of "abi_static_size (abi_get_type v')"  0
                                 "(map (abi_static_size \<circ> abi_get_type) vs)"]]
                nat_add_distrib[of "(abi_static_size (abi_get_type v'))"
                                   "foldl (+) 0 (map (abi_static_size \<circ> abi_get_type) vs)"]
                abi_static_size_nonneg[of "abi_get_type v'"] Tl_nonneg
        by(auto simp add:take_add Com list_sum_def)
    qed

    show ?case using "15.IH"(3)[of "Vtuple (map abi_get_type vs) vs" "map abi_get_type vs"
                                   "index + abi_static_size (abi_get_type v')" full_code
                               ,OF refl _ _ Bound2' Dec2' refl]
                          "15.IH"(1)[of "abi_get_type v'" "index" full_code
                               ,OF _ _ Bound1 Dec' refl]
                          2  abi_static_size_nonneg[of "abi_get_type v'"] 
                          TakeDrop
      by(auto simp del:  decode_static_tup.simps)
  }
qed

(* a more convenient static decoder correctness lemma *)
lemma abi_decode_encode_static :
"decode_static t (index, full_code) = Ok v \<Longrightarrow>
 abi_type_valid t \<Longrightarrow>
 0 \<le> index \<Longrightarrow>
 nat index + nat (abi_static_size t) \<le> length full_code \<Longrightarrow>
 (abi_value_valid v \<and>
 (\<exists> (code :: 8 word list) . encode_static v = Ok code \<and>
     take (nat (abi_static_size t)) (drop (nat index) full_code) = code))"
  using abi_decode_static_type_ok[of t] abi_decode_encode_static'
  by auto

(* a more convenient version of the Estatic rule for proving static encodings *)
lemma Estatic_easier :
  assumes Hstatic : "abi_type_isstatic (abi_get_type v)"
  assumes Hvalid : "abi_value_valid v"
  assumes Henc : "encode_static v = Ok code"
  assumes Hstart : "0 \<le> start"
  assumes Hbound : "nat start + nat (abi_static_size (abi_get_type v))  \<le> length full_code"
  assumes Hcode : 
    "code = take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code)"
  shows "can_encode_as v full_code start"
proof-
  have Min : "(int (min (length full_code) (nat start))) = nat start" using Hbound by(auto)

  have TakeDrop1 :
       "take (nat start) full_code @
        take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) @ 
        drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code)
          = full_code"
    by(simp only:append_take_drop_id)

  have TakeDrop2:
        "take (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) @ 
         drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code) = 
  drop (nat start) full_code"
    by(simp only:append_take_drop_id)

  show "can_encode_as v full_code start"
    using Estatic[OF Hstatic Hvalid
                 ,of "take (nat (abi_static_size (abi_get_type v)) ) (drop (nat start) full_code)"
                     "take (nat start) full_code"
                     "drop (nat (abi_static_size (abi_get_type v))) (drop (nat start) full_code)"]
    using Min Henc Hcode Hstart
    unfolding TakeDrop1 
    by(auto)
qed

(* decode' never returns a negative index *)
lemma decode'_index_positive :
"decode' t (start, full_code) = Ok (v, len) \<Longrightarrow>
 0 \<le> start"
  by(cases "start < 0"; auto simp add: decode'.simps)

(* helpful identity of list_sum and concat *)
lemma list_sum_concat :
  "list_sum (map length xss) = length (concat xss)"
proof(induction xss)
  case Nil
  then show ?case by (auto simp add:list_sum_def)
next
  case (Cons a xss)
  then show ?case using sym[OF foldl_plus[of "length a" 0 "map int (map length xss)"]]
    by(simp add:list_sum_def)
qed

(* "trisecting" lists - this ends up being useful for some low-level byte-string
   reasoning in the final theorem. *)
lemma list_partition3 :
  assumes Htri : "l1 @ l2 @ post = l @ post'"
  assumes Hlen : "length l1 + length l2 + n = length l"
  shows "l = l1 @ l2 @ drop (length l1 + length l2) l"
proof-

  have Min: "min (length l1) (length l1 + length l2) = length l1" by(auto)

  have App1 : "l1 @ l2 = take (length l1 + length l2) l" 
    using Hlen Htri
    unfolding append_eq_conv_conj
    by(auto simp add:drop_take Min)

  have App2: "l1 @ l2 @ drop (length l1 + length l2) l = (l1 @ l2) @ drop (length l1 + length l2) l"
    by simp

  show "l = l1 @ l2 @ drop (length l1 + length l2) l"
    unfolding App2 App1
    by(simp only:append_take_drop_id)
qed

lemma decode'_tuple_tails_length :
  "decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) = Ok (vs, bytes) \<Longrightarrow>
    length vs = length ts"
proof(induction ts arbitrary: idxs vs vos byteoffset ix l bytes)
  case Nil

  have Idx_nil : "idxs = []" using Nil by(cases idxs; auto)
  have Vos_nil : "vos = []" using Nil Idx_nil by(cases vos; auto)

  show ?case using Nil Idx_nil Vos_nil by auto
next
  case (Cons a ts)

  obtain idxh idxt where Idx_cons : "idxs = idxh#idxt"
    using Cons by(cases idxs; auto)

  obtain vosh vost where Vos_cons : "vos = vosh#vost"
    using Cons Idx_cons by (cases vos; auto)

  then show ?case
  proof(cases idxh)
    case None

    obtain vosh' where Vosh_some : "vosh = Some vosh'"
      using Idx_cons Vos_cons Cons None
      by(cases vosh; auto)

    then show ?thesis using Idx_cons Vos_cons Cons None
      by(auto split:sum.split_asm)
  next
    case (Some idxh')

    have Vosh_none : "vosh = None"
      using Idx_cons Vos_cons Cons Some
      by(cases vosh; auto)

    then show ?thesis using Idx_cons Vos_cons Cons Some
      by(auto split:sum.split_asm)
  qed
qed

lemma check_padding_skip_padding :
"check_padding n l \<Longrightarrow>
 skip_padding n \<le> length l"
  by(auto simp only:Let_def check_padding.simps)

lemma decode_sint_valid256 : "sint_value_valid 256 (decode_sint bs)"
  using sint_range_size[of "word_rcat (take 32 (bs :: 8 word list)) :: 256 word"]
  by(auto simp add: sint_value_valid_def word_size)

lemma decode_uint_valid256 : "uint_value_valid 256 (decode_uint bs)"
  using uint_range_size[of "word_rcat (take 32 (bs :: 8 word list)) :: 256 word"]
  by(auto simp add: uint_value_valid_def word_size)

(* Decoder implies specification (can_encode_as) *)
(* The nesting of quantifiers here in the second clause appears to be necessary
   in order to prevent Isabelle's automation from reassociating the clauses
   in an unwanted way *)
lemma abi_decode_succeed_converse_gen :
  shows "\<And> t len start full_code .
            decode' t (start, full_code) = Ok (v, len) \<Longrightarrow>
            abi_type_valid t \<Longrightarrow>
            abi_get_type v = t \<Longrightarrow>
            can_encode_as v full_code (start)" and

         "\<And> v t n n' ts pre1 pre2 count code heads'  tails' count' count'' bytes bytes'.
             (v = (Vfarray t n vs) \<Longrightarrow> 
              abi_type_isdynamic t \<Longrightarrow>
              abi_type_valid t \<Longrightarrow>
              decode'_dyn_tuple_heads (replicate n t) 
                (int (length pre2)) 
                (int (length pre1), pre1@pre2@code) = Ok (heads', tails', count', bytes) \<Longrightarrow>
              decode'_dyn_tuple_tails tails' (replicate n t) heads' count'' 
                (int (length pre1), pre1@pre2@code) = Ok (vs, bytes') \<Longrightarrow>
              (abi_value_valid v \<and>
              (\<exists> heads head_types tails . 
                is_head_and_tail vs heads head_types tails \<and>
                can_encode_as (Vtuple head_types heads) (pre1@pre2@code)
                  (int (length pre1) + int (length pre2)) \<and>
                (\<forall> (offset::int) v::abi_value. (offset, v) \<in> set tails \<longrightarrow> 
                  can_encode_as v ( pre1@pre2@code) (int (length pre1) + offset)) \<and>
                those (map2 ht_combine heads' 
                  (map (\<lambda> to . 
                    (case to of 
                      None \<Rightarrow> None 
                      | Some t \<Rightarrow> Some (t - int (length pre1))))
                   tails')) = Some heads \<and>
                map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
                ht_wellbehaved tails' (map abi_get_type vs) heads'))) &&&

             (v = (Vtuple ts vs) \<Longrightarrow>
              list_all abi_type_valid ts \<Longrightarrow>
              decode'_dyn_tuple_heads (ts)
                (int (length pre2)) 
                (int (length pre1), pre1@pre2@code) = Ok (heads', tails', count', bytes) \<Longrightarrow>
              decode'_dyn_tuple_tails tails' (ts) heads' count'' 
                (int (length pre1), pre1@pre2@code) = Ok (vs, bytes') \<Longrightarrow>
              (abi_value_valid v \<and>
              (\<exists> heads head_types tails . 
                is_head_and_tail vs heads head_types tails \<and>
                can_encode_as (Vtuple head_types heads) (pre1@pre2@code) 
                  (int (length pre1) + int (length pre2)) \<and>
                (\<forall> (offset::int) v::abi_value. (offset, v) \<in> set tails \<longrightarrow>
                  can_encode_as v (pre1@pre2@code) (int (length pre1) + offset)) \<and>
                those (map2 ht_combine heads' 
                  (map (\<lambda> to .   
                    (case to of
                      None \<Rightarrow> None 
                      | Some t \<Rightarrow> Some (t - int (length pre1))))
                   tails')) = Some heads \<and>
                map (\<lambda> x . fst x + int (length pre1)) tails = (somes tails') \<and>
                ht_wellbehaved tails' (map abi_get_type vs) heads'))) &&&

             (v = (Varray t vs) \<Longrightarrow>
              abi_type_valid t \<Longrightarrow>
              length count = 32 \<Longrightarrow>
              uint_value_valid 256 n \<Longrightarrow>
              uint_value_valid 256 n' \<Longrightarrow>
              n = length vs \<Longrightarrow>
              n \<le> n' \<Longrightarrow>
              count = encode_int (int n') \<Longrightarrow>
              decode'_dyn_tuple_heads (replicate n t) 
                (int (length pre2)) (int (length (pre1 @ count)), pre1@count@pre2@code) 
                = Ok (heads', tails', count', bytes) \<Longrightarrow>
              decode'_dyn_tuple_tails tails' (replicate n t) heads' count''
                (int (length (pre1 @ count)), pre1@count@pre2@code) = Ok (vs, bytes') \<Longrightarrow>
              (abi_value_valid v \<and>
              (\<exists> heads head_types tails . 
                is_head_and_tail vs heads head_types tails \<and>
                can_encode_as (Vtuple head_types heads) (pre1@count@pre2@code)
                  (int (length pre1) + 32 + int (length pre2)) \<and>
                (\<forall> (offset::int) v::abi_value. (offset, v) \<in> set tails \<longrightarrow>
                  can_encode_as v ( pre1@count@pre2@code) (int (length pre1) + 32 + offset)) \<and>
                those (map2 ht_combine heads' 
                  (map (\<lambda> to . 
                    (case to of 
                      None \<Rightarrow> None
                      | Some t \<Rightarrow> Some (t - int (length pre1) - 32)))
                   tails')) = Some heads \<and>
                  map (\<lambda> x . fst x + int (length pre1) + 32) tails = (somes tails') \<and>
                  ht_wellbehaved tails' (map abi_get_type vs) heads')))"

proof(induction rule:my_abi_value_induct)
(* Vuint *)
  case (1 x1 x2)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vuint x1 x2)"]
      Estatic_easier[of "(Vuint x1 x2)"]
    (* this could be made faster *)
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vsint *)
  case (2 x1 x2)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vsint x1 x2)"]
      Estatic_easier[of "(Vsint x1 x2)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Addr *)
  case (3 x)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vaddr x)"]
      Estatic_easier[of "(Vaddr x)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Bool *)
  case (4 x)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vbool x)"]
      Estatic_easier[of "(Vbool x)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vfixed *)
  case (5 x1 x2 x3a)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vfixed x1 x2 x3a)"]
      Estatic_easier[of "(Vfixed x1 x2 x3a)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vufixed *)
  case (6 x1 x2 x3a)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vufixed x1 x2 x3a)"]
      Estatic_easier[of "(Vufixed x1 x2 x3a)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vfbytes *)
  case (7 x1 x2)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vfbytes x1 x2)"]
      Estatic_easier[of "(Vfbytes x1 x2)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vfunction *)
  case (8 x1 x2)
  then show ?case using
      abi_decode_encode_static[of t start full_code "(Vfunction x1 x2)"]
      Estatic_easier[of "(Vfunction x1 x2)"]
    by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
next
(* Vfarray *)
  case (9 t' n' l')
  show ?case
  proof(cases "abi_type_isstatic t'")
    case True
    then show ?thesis using "9.prems"
      abi_decode_encode_static[of t start full_code "(Vfarray t' n' l')"]
      Estatic_easier[of "(Vfarray t' n' l')"]
      by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
  next
    case False

    obtain heads' tails' count' bytes where
      Heads : "decode'_dyn_tuple_heads (replicate n' t') 0 (start, full_code) = 
                Ok (heads', tails', count', bytes)" using "9.prems" False
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    then obtain bytes' where
      Tails : "decode'_dyn_tuple_tails tails' (replicate n' t') heads' count' (start, full_code) =
                Ok (l', bytes')" using "9.prems" False
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    have Min : "(int (min (length full_code) (nat start))) = start"
      using "9.prems"
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    obtain heads head_types tails where
      IH_spec :
      " abi_value_valid (Vfarray t' n' l') \<and>
        is_head_and_tail l' heads head_types tails \<and>
        can_encode_as (Vtuple head_types heads) 
          (take (nat start) full_code @ [] @ drop (nat start) full_code)
          (int (length (take (nat start) full_code)) + int (length [])) \<and>
        (\<forall>offset v.
            (offset, v) \<in> set tails \<longrightarrow>
            can_encode_as v (take (nat start) full_code @ [] @ 
              drop (nat start) full_code) (int (length (take (nat start) full_code)) + offset)) \<and>
        those (map2 ht_combine heads' 
          (map (\<lambda>a. case a of 
            None \<Rightarrow> None 
            | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) tails')) =
        Some heads \<and>
        map (\<lambda>x. fst x + int (length (take (nat start) full_code))) tails = somes tails' \<and> 
        ht_wellbehaved tails' (map abi_get_type l') heads'"
      using  False "9.prems" Heads Tails
             "9.IH"(1)[of "Vfarray t' n' l'" t' n' "[]" "take (nat start) full_code"
                          "drop (nat start) full_code" heads' 
                          tails' count' bytes count' bytes'] Min
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    have Offs' : 
      "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (offset + start))"
    proof-
      fix offset v
      assume Hin : "(offset, v) \<in> set tails"
      then show "can_encode_as v full_code (offset + start)"
      using IH_spec Min unfolding add.commute[of "offset" "start"]
       by(auto)
    qed

    show ?thesis using False "9.prems" Heads Tails IH_spec Min Offs'
                             Efarray_dyn[of t' n' l' heads head_types tails full_code start]
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)
  qed
next
(* Vtuple *)
  case (10 ts vs)
  show ?case
  proof(cases "abi_type_isstatic (Ttuple ts)")
    case True
    then show ?thesis using "10.prems"
      abi_decode_encode_static[of t start full_code "(Vtuple ts vs)"]
      Estatic_easier[of "(Vtuple ts vs)"]
      by(auto simp add:decode'.simps simp del: decode_static.simps
            split:if_split_asm sum.split_asm)
  next
    case False

    obtain heads' tails' count' bytes where
      Heads : "decode'_dyn_tuple_heads (ts) 0 (start, full_code) = 
                Ok (heads', tails', count', bytes)" using "10.prems" False
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    then obtain bytes' where
      Tails : "decode'_dyn_tuple_tails tails' (ts) heads' count' (start, full_code) =
                Ok (vs, bytes')" using "10.prems" False
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    have Min : "(int (min (length full_code) (nat start))) = start"
      using "10.prems"
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    obtain heads head_types tails where
      IH_spec :
      " abi_value_valid (Vtuple ts vs) \<and>
        is_head_and_tail vs heads head_types tails \<and>
        can_encode_as (Vtuple head_types heads) 
          (take (nat start) full_code @ [] @ drop (nat start) full_code)
          (int (length (take (nat start) full_code)) + int (length [])) \<and>
        (\<forall>offset v.
            (offset, v) \<in> set tails \<longrightarrow>
            can_encode_as v (take (nat start) full_code @ [] @ 
              drop (nat start) full_code) (int (length (take (nat start) full_code)) + offset)) \<and>
        those (map2 ht_combine heads' 
          (map (\<lambda>a. case a of 
            None \<Rightarrow> None 
            | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)))) tails')) =
        Some heads \<and>
        map (\<lambda>x. fst x + int (length (take (nat start) full_code))) tails = somes tails' \<and> 
        ht_wellbehaved tails' (map abi_get_type vs) heads'"

      using False "10.prems" Heads Tails
                  "10.IH"(2)[of "Vtuple ts vs" ts "[]" "take (nat start) full_code"
                                "drop (nat start) full_code" heads'
                                tails' count' bytes count' bytes'] Min
      by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)

    have Offs' : 
      "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (offset + start))"
    proof-
      fix offset v
      assume Hin : "(offset, v) \<in> set tails"
      then show "can_encode_as v full_code (offset + start)"
      using IH_spec Min unfolding add.commute[of "offset" "start"]
       by(auto)
    qed
      
    show ?thesis using False "10.prems" Heads Tails IH_spec Min Offs'
                             Etuple_dyn[of ts vs _ heads head_types tails full_code start]
      by(auto simp add:decode'.simps Let_def list_ex_iff split: if_split_asm sum.split_asm)
  qed
next
(* Vbytes *)
  case (11 x)

  have Hyps : "0 \<le> start" 
              "32 + start \<le> int (length full_code)" 
              "decode_uint (take 32 (drop (nat start) full_code)) + 32 + start \<le> 
               int (length full_code)" 
              "check_padding (nat (decode_uint (take 32 (drop (nat start) full_code))))
                             (drop (32 + nat start) full_code)"
              "take (nat (decode_uint (take 32 (drop (nat start) full_code))))
                    (drop (32 + nat start) full_code) = x"
              "int (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code))))) + 
                    32 = len"
    using 11 
    by(auto simp add:decode'.simps Let_def bytes_value_valid_def split:if_split_asm 
              simp del: decode_uint.simps check_padding.simps skip_padding.simps)

  have Gt0 : "0 \<le> (decode_uint (take 32 (drop (nat start) full_code)))" 
    by auto

  have Min1 : "nat (decode_uint (take 32 (drop (nat start) full_code))) \<le> 
                    length full_code - (32 + nat start)"
    using Hyps(1) Hyps(3)
    by(auto)

  have Min1A :
  "(int (min (length full_code - (32 + nat start))
    (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
    (decode_uint (take 32 (drop (nat start) full_code)))"
    using Hyps(3)
          min_absorb2[OF Min1] Gt0
    by(auto simp del:decode_uint.simps)  

  have Min2 : " (int (min (length full_code) (nat start))) = start"
    using Hyps(1) Hyps(2) by(auto)

  have Min2 :
  "(min (length full_code - (32 + nat start))
        (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
   (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))"
    using min_absorb2[OF check_padding_skip_padding[OF Hyps(4)]]
    by(auto simp add: Let_def simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)

  have Comm:
    "32 + nat start + skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))) =
    (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))) + (32 + nat start))"
    by(auto)

  have Min3 : "(min (length full_code) (nat start)) = (nat start)"
    using Hyps(2) by auto

  have Min4 : "min (length full_code - nat start) 32 = 32"
    using Hyps(1) Hyps(2) Hyps(3) by auto

  have Min5 : "(min (length full_code - (32 + nat start)) 
                    (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
               (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))"
    using min_absorb2[OF check_padding_skip_padding[OF Hyps(4)]]
    by(auto simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)


  have Conc' :
    "can_encode_as 
      (Vbytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                    (drop (32 + nat start) full_code)))
      ((take (nat start) full_code) @ (take 32 (drop (nat start) full_code)) @
       pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                   (drop (32 + nat start) full_code)) @
       (drop (32 + nat start + (skip_padding 
            (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))))
              full_code)) 
      (int (length (take (nat start) full_code)))"
  proof(rule Ebytes[OF _ refl])
    show "abi_value_valid (Vbytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                                        (drop (32 + nat start) full_code)))"
      using Hyps 
      by(auto simp add:decode'.simps Let_def bytes_value_valid_def Min1A decode_uint_valid 
              split:if_split_asm 
              simp del: decode_uint.simps check_padding.simps skip_padding.simps)
  next
    show "length (take 32 (drop (nat start) full_code)) = 32"
      using Hyps(1) Hyps(2) by(auto)
  next
    show "can_encode_as
          (Vuint 256 
            (int (length (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                                   (drop (32 + nat start) full_code)))))
         (take (nat start) full_code @
          take 32 (drop (nat start) full_code) @
          pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code))))
                    (drop (32 + nat start) full_code)) @
          drop (32 + nat start + (skip_padding 
                (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))))) full_code)
         (int (length (take (nat start) full_code)))"
    proof(rule Estatic; (simp; fail)?)
      show "abi_value_valid (Vuint 256 (int (length (take (nat (decode_uint 
              (take 32 (drop (nat start) full_code)))) (drop (32 + nat start) full_code)))))"
        using min_absorb2[OF Min1] Gt0 decode_uint_valid
        by(auto simp del: decode_uint.simps pad_bytes.simps)
    next
      have "32 \<le> length full_code - nat start" using Hyps(1) Hyps(2) by(auto)

      thus "encode_static (Vuint 256 (int (length (take (nat (decode_uint 
              (take 32 (drop (nat start) full_code)))) (drop (32 + nat start) full_code))))) = 
            Ok (take 32 (drop (nat start) full_code))"
        using min_absorb2[OF Min1] Gt0 uint_reencode[of "(drop (nat start) full_code)"]
        by(auto simp del: pad_bytes.simps)
    qed
  qed

  have ListPart : "(take (nat start) full_code @
      take 32 (drop (nat start) full_code) @
      pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code))))
                      (drop (32 + nat start) full_code)) @
      drop (32 + nat start + (skip_padding 
            (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))))) full_code)
  = full_code"
    unfolding check_padding_pad_bytes'[OF Hyps(4)] 
    unfolding append_eq_conv_conj 
    using Min3 Min4 Min5
    by(auto simp add: Comm simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)

  show ?case using Conc' unfolding ListPart
    unfolding Hyps using Min3 Hyps(1) by(simp)
next
(* Vstring *)
  case (12 s)

  obtain x where X : "x = string_to_bytes s" by auto

  have Hyps : "0 \<le> start" 
              "32 + start \<le> int (length full_code)" 
              "decode_uint (take 32 (drop (nat start) full_code)) + 32 + start \<le> 
               int (length full_code)" 
              "check_padding (nat (decode_uint (take 32 (drop (nat start) full_code))))
                             (drop (32 + nat start) full_code)"
              "x = take (nat (decode_uint (take 32 (drop (nat start) full_code))))
                    (drop (32 + nat start) full_code)"
              "int (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code))))) + 
                    32 = len"
    using 12  X
         by(auto simp add:decode'.simps Let_def bytes_value_valid_def string_to_bytes_to_string
                 split:if_split_asm 
                 simp del: decode_uint.simps check_padding.simps skip_padding.simps
                           string_to_bytes.simps bytes_to_string.simps)

  show ?case
  proof(rule Estring[OF _ refl _])
    have "length (string_to_bytes s) \<le>
          (nat (decode_uint (take 32 (drop (nat start) full_code))))"
      using Hyps List.length_take[of "(nat (decode_uint (take 32 (drop (nat start) full_code))))" 
                                     "(string_to_bytes s)"] unfolding X
      by(auto simp add: string_value_valid_def
               simp del: decode_uint.simps check_padding.simps skip_padding.simps
                         string_to_bytes.simps bytes_to_string.simps)

    hence "uint_value_valid 256 (length (string_to_bytes s))"
      using decode_uint_valid[of "(take 32 (drop (nat start) full_code))"]
      by(auto simp add: uint_value_valid_def)

    hence "uint_value_valid 256 (length s)"
      unfolding string_to_bytes.simps by auto

    then show "abi_value_valid (Vstring s)" using Hyps unfolding X
      by(auto simp add: string_value_valid_def
              simp del: decode_uint.simps check_padding.simps skip_padding.simps
                        string_to_bytes.simps bytes_to_string.simps)
  next
    (* the following is copied from the bytes case. it would be convenient
       to have a lemma capturing this. *)
    have Gt0 : "0 \<le> (decode_uint (take 32 (drop (nat start) full_code)))" 
      by auto
  
    have Min1 : "nat (decode_uint (take 32 (drop (nat start) full_code))) \<le> 
                      length full_code - (32 + nat start)"
      using Hyps(1) Hyps(3)
      by(auto)
  
    have Min1A :
    "(int (min (length full_code - (32 + nat start))
      (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
      (decode_uint (take 32 (drop (nat start) full_code)))"
      using Hyps(3)
            min_absorb2[OF Min1] Gt0
      by(auto simp del:decode_uint.simps)  
  
    have Min2 : " (int (min (length full_code) (nat start))) = start"
      using Hyps(1) Hyps(2) by(auto)
  
    have Min2 :
    "(min (length full_code - (32 + nat start))
          (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
     (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))"
      using min_absorb2[OF check_padding_skip_padding[OF Hyps(4)]]
      by(auto simp add: Let_def simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)
  
    have Comm:
      "32 + nat start + skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))) =
      (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))) + (32 + nat start))"
      by(auto)
  
    have Min3 : "(min (length full_code) (nat start)) = (nat start)"
      using Hyps(2) by auto
  
    have Min4 : "min (length full_code - nat start) 32 = 32"
      using Hyps(1) Hyps(2) Hyps(3) by auto
  
    have Min5 : "(min (length full_code - (32 + nat start)) 
                      (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))) =
                 (skip_padding (nat (decode_uint (take 32 (drop (nat start) full_code)))))"
      using min_absorb2[OF check_padding_skip_padding[OF Hyps(4)]]
      by(auto simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)
  
    have Conc' :
      "can_encode_as 
        (Vbytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                      (drop (32 + nat start) full_code)))
        ((take (nat start) full_code) @ (take 32 (drop (nat start) full_code)) @
         pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                     (drop (32 + nat start) full_code)) @
         (drop (32 + nat start + (skip_padding 
              (nat (decode_uint (take (32::nat) (drop (nat start) full_code))))))
                full_code)) 
        (int (length (take (nat start) full_code)))"
    proof(rule Ebytes[OF _ refl])
      show "abi_value_valid (Vbytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                                          (drop (32 + nat start) full_code)))"
        using Hyps 
        by(auto simp add:decode'.simps Let_def bytes_value_valid_def Min1A decode_uint_valid 
                split:if_split_asm 
                simp del: decode_uint.simps check_padding.simps skip_padding.simps)
    next
      show "length (take 32 (drop (nat start) full_code)) = 32"
        using Hyps(1) Hyps(2) by(auto)
    next
      show "can_encode_as
            (Vuint 256 
              (int (length (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                                     (drop (32 + nat start) full_code)))))
           (take (nat start) full_code @
            take 32 (drop (nat start) full_code) @
            pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code))))
                      (drop (32 + nat start) full_code)) @
            drop (32 + nat start + (skip_padding 
                  (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))))) full_code)
           (int (length (take (nat start) full_code)))"
      proof(rule Estatic; (simp; fail)?)
        show "abi_value_valid (Vuint 256 (int (length (take (nat (decode_uint 
                (take 32 (drop (nat start) full_code)))) (drop (32 + nat start) full_code)))))"
          using min_absorb2[OF Min1] Gt0 decode_uint_valid
          by(auto simp del: decode_uint.simps pad_bytes.simps)
      next
        have "32 \<le> length full_code - nat start" using Hyps(1) Hyps(2) by(auto)
  
        thus "encode_static (Vuint 256 (int (length (take (nat (decode_uint 
                (take 32 (drop (nat start) full_code)))) (drop (32 + nat start) full_code))))) = 
              Ok (take 32 (drop (nat start) full_code))"
          using min_absorb2[OF Min1] Gt0 uint_reencode[of "(drop (nat start) full_code)"]
          by(auto simp del: pad_bytes.simps)
      qed
    qed

    have ListPart : "(take (nat start) full_code @
        take 32 (drop (nat start) full_code) @
        pad_bytes (take (nat (decode_uint (take 32 (drop (nat start) full_code)))) 
                        (drop (32 + nat start) full_code)) @
        drop (32 + nat start + (skip_padding 
              (nat (decode_uint (take (32::nat) (drop (nat start) full_code)))))) full_code)
    = full_code"
      unfolding check_padding_pad_bytes'[OF Hyps(4)] 
      unfolding append_eq_conv_conj 
      using Min3 Min4 Min5
      by(auto simp add: Comm simp del: pad_bytes.simps decode_uint.simps skip_padding.simps)

    show "can_encode_as (Vbytes (string_to_bytes s)) full_code start"
      using Conc' unfolding ListPart
      unfolding sym[OF X] Hyps using Min3 Hyps(1) 
      by(simp del: pad_bytes.simps decode_uint.simps skip_padding.simps string_to_bytes.simps)
  qed
next
(* Varray *)
  case (13 t' vs')

  have Start_nonneg : "0 \<le> start"
    using "13.prems"
    by(cases "0 \<le> start"; auto simp add: decode'.simps)

  hence Start_bound :
    "start \<le> int (length full_code)"
    using "13.prems"
    by(cases "start \<le> int (length full_code)"; auto simp add: decode'.simps)

  hence Start_idx_size : "32 + start \<le> length full_code"
    using "13.prems" Start_nonneg
    by(cases "32 + start \<le> length full_code";
        auto simp add: decode'.simps)

  (* NB: tried stating the length check separately as a fact, but Isabelle didn't
         seem to like the proof unless I add if_split_asm to auto *)
  obtain heads' tails' count' bytes where
     Heads : "decode'_dyn_tuple_heads 
               (replicate (nat (decode_uint (take 32 (drop (nat start) full_code)))) t') 0 
               (start + 32, full_code) = 
               Ok (heads', tails', count', bytes)" 
     using "13.prems" Start_nonneg Start_bound Start_idx_size
     by(cases "decode'_dyn_tuple_heads 
               (replicate (nat (decode_uint (take 32 (drop (nat start) full_code)))) t') 0 
               (start + 32, full_code) ";
         auto simp add:decode'.simps Let_def split: if_split_asm)

  (* NB: tried stating the length check separately as a fact, but Isabelle didn't
         seem to like the proof unless I add if_split_asm to auto *)
  then obtain bytes' where
    Tails : "decode'_dyn_tuple_tails tails' 
              (replicate (nat (decode_uint (take 32 (drop (nat start) full_code)))) t') 
              heads' count' (start + 32, full_code) =
              Ok (vs', bytes')" using "13.prems" Start_nonneg Start_bound Start_idx_size
    by(cases "decode'_dyn_tuple_tails tails' 
              (replicate (nat (decode_uint (take 32 (drop (nat start) full_code)))) t') 
              heads' count' (start + 32, full_code)";
        auto simp add:decode'.simps Let_def split: if_split_asm)

  have Min : "(int (min (length full_code) (nat start))) = start"
    using Start_bound Start_nonneg
    by(auto)

  have Len_valid : "uint_value_valid (256::nat) (int (length vs'))"
    using "13.prems" decode'_tuple_tails_length[OF Tails] decode_uint_valid
    by(auto)

  have Len_val : "(nat (decode_uint (take 32 (drop (nat start) full_code)))) = length vs'"
    using "13.prems" decode'_tuple_tails_length[OF Tails] decode_uint_valid
    by(auto)

  have "0 \<le> decode_uint (take 32 (drop (nat start) full_code))"
    by(auto)

  hence Len_val' : "decode_uint (take 32 (drop (nat start) full_code)) = length vs'"
    using arg_cong[OF Len_val, of int]
    by(auto)

  have Start32 : "32 \<le> length full_code - nat start" using Start_idx_size Start_nonneg
    by auto

  hence Len_reencode :
    "encode_int (int (length vs')) = (take 32 (drop (nat start) full_code))"
    using uint_reencode[of "drop (nat start) full_code"]
    unfolding sym[OF Len_val'] Start_idx_size
    by(auto simp del: encode_int.simps)

  have Min1 : "min (length full_code) (nat start) = (nat start)"
    using Start_bound by auto

  have Min2 : "(min (length full_code - nat start) 32) = 32"
    using Start32 by auto

  have Comm: "(nat start + 32) = (32 + nat start)" by auto

  hence Len_encoded_full : 
    "take (nat start) full_code @ encode_int (int (length vs')) @ drop (nat start + 32) full_code
     = full_code" unfolding Len_reencode append_eq_conv_conj using Min1 Min2
    by(auto simp add: Comm)

  have Len_len : "length (encode_int (int (length vs'))) = 32" 
    using int_length by auto

  have Len_can_enc : "can_encode_as (Vuint 256 (int (length vs'))) full_code start"
  proof(rule Estatic_easier; (simp; fail)?)
    show "abi_value_valid (Vuint 256 (int (length vs')))" using Len_valid
      by(auto)
  next
    show "encode_static (Vuint 256 (int (length vs'))) = Ok (take 32 (drop (nat start) full_code))"
      using Len_reencode
      by(auto)
  next
    show "0 \<le> start"
      using Start_nonneg by auto
  next
    show "nat start + nat (abi_static_size (abi_get_type (Vuint 256 (int (length vs'))))) \<le> 
            length full_code" using Start32
      by(auto)
  qed

  obtain heads head_types tails where
    IH_spec :
    " abi_value_valid (Varray t' vs') \<and>
      is_head_and_tail vs' heads head_types tails \<and>
      can_encode_as (Vtuple head_types heads) 
        full_code
        (int (length (take (nat start) full_code)) + 32 + int (length [])) \<and>
      (\<forall>offset v.
          (offset, v) \<in> set tails \<longrightarrow>
            can_encode_as v 
              full_code
              (int (length (take (nat start) full_code)) + 32 + offset)) \<and>
      those (map2 ht_combine heads' 
        (map (\<lambda>a. case a of 
          None \<Rightarrow> None 
          | Some t \<Rightarrow> Some (t - int (length (take (nat start) full_code)) - 32)) tails')) =
      Some heads \<and>
      map (\<lambda>x. fst x + int (length (take (nat start) full_code)) + 32) tails = somes tails' \<and> 
      ht_wellbehaved tails' (map abi_get_type vs') heads'"
    using  "13.prems" Heads Tails Start_nonneg Start_bound Start_idx_size
           "13.IH"(3)[of "Varray t' vs'" t' "encode_int (int (length vs'))"
                        "length vs'" "length vs'" "[]"
                        "take (nat start) full_code "
                        "drop (nat start + 32) full_code" heads' tails' count' bytes count' bytes'] 
                      Min int_length Len_valid Len_val sym[OF Len_encoded_full] Len_len
    by(auto simp add:decode'.simps Let_def  simp del: decode_uint.simps encode_int.simps)      

  have Offs' : 
    "(\<And>offset v. (offset, v) \<in> set tails \<Longrightarrow> can_encode_as v full_code (offset + start + 32))"
  proof-
    fix offset v
    assume Hin : "(offset, v) \<in> set tails"
    have Comm : "offset + start + 32 = start + 32 + offset" by auto
    then show "can_encode_as v full_code (offset + start + 32)"
    using IH_spec Min Hin unfolding Comm
    by(auto)
  qed

  show ?case using "13.prems" Heads Tails IH_spec Min Offs' Len_can_enc
                           Earray[of t' vs' heads head_types tails full_code start]
    by(auto simp add:decode'.simps Let_def split: if_split_asm sum.split_asm)
next
(* Nil *)
  case 14

  {
  (* Vfarray *)
    case 1
    show ?case
    proof(cases n)
      case 0

      have C1 : "is_head_and_tail [] [] [] []" using iht_nil by auto

      have C2 : "can_encode_as (Vtuple [] []) (pre1 @ pre2 @ code)
                      (int (length pre1) + int (length pre2))"
        by(rule Estatic_easier; auto simp add:tuple_value_valid_aux_def)

      show ?thesis using 0 1 C1 C2 by(auto simp add:farray_value_valid_aux_def)
    next
      case (Suc nat)

      obtain tails'h tails't where Tails' : "tails' = tails'h#tails't"
        using Suc 1
        by(cases tails'; auto split:sum.splits prod.splits if_split_asm)

      obtain heads'h heads't where Heads' : "heads' = heads'h#heads't"
        using Suc 1
        by(cases tails'; auto split:sum.splits prod.splits if_split_asm)

      show ?thesis
      proof(cases heads'h)
        case None
        then show ?thesis using 1 Suc by(auto split:sum.split_asm prod.split_asm if_split_asm)
      next
        case (Some a)
        then show ?thesis using 1 Suc by(auto split:sum.split_asm prod.split_asm if_split_asm)
      qed
    qed
  next
  (* Vtuple *)
    case 2
    show ?case
    proof(cases ts)
      case Nil

      have C1 : "is_head_and_tail [] [] [] []" using iht_nil by auto

      have C2 : "can_encode_as (Vtuple [] []) (pre1 @ pre2 @ code)
                      (int (length pre1) + int (length pre2))"
        by(rule Estatic_easier; auto simp add:tuple_value_valid_aux_def)

      then show ?thesis using Nil 2 C1 C2 by(auto simp add:tuple_value_valid_aux_def)
    next
      case (Cons tsh tst)
      obtain tails'h tails't where Tails' : "tails' = tails'h#tails't"
        using Cons 2
        by(cases tails'; auto split:sum.split_asm prod.split_asm if_split_asm)

      obtain heads'h heads't where Heads' : "heads' = heads'h#heads't"
        using Cons 2
        by(cases tails'; auto split:sum.split_asm prod.split_asm if_split_asm)

      show ?thesis
      proof(cases heads'h)
        case None
        then show ?thesis using 2 Cons by(auto split:sum.split_asm prod.split_asm if_split_asm)
      next
        case (Some a)
        then show ?thesis using 2 Cons by(auto split:sum.split_asm prod.split_asm if_split_asm)
      qed
    qed
  next
  (* Varray *)
    case 3

    have C1 : "is_head_and_tail [] [] [] []" using iht_nil by auto

    have C2' : "nat (int (length pre1) + 32 + int (length pre2)) \<le> 
                  length pre1 + (length (encode_int (int n')) + (length pre2 + length code))"
      using int_length[of "int n'"]
      by(auto)

    hence C2 : "can_encode_as (Vtuple [] [])
                (pre1 @ encode_int (int n') @ pre2 @ code)
                (int (length pre1) + 32 + int (length pre2))"
      by(auto intro: Estatic_easier simp add:tuple_value_valid_aux_def int_length 
              simp del: encode_int.simps)

    then show ?case using 3 C1 C2
      by(auto simp add: array_value_valid_aux_def)
  }
next
(* Cons *)
  case (15 vh vt)
  {
  (* Vfarray *)
    case 1
    show ?case
    proof(cases tails')
      case Tnil : Nil

      then have Hnil : "heads' = []" using "1.prems"
        by(cases heads'; auto)

      show ?thesis
      proof(cases n)
        case 0
        then show ?thesis using "1.prems" by(auto)
      next
        case (Suc nat)
        then show ?thesis using "1.prems" Tnil Hnil by(auto)
      qed
    next
      case Tcons : (Cons tails'h tails't)

      then obtain heads'h heads't where Hcons : "heads' = heads'h#heads't" using "1.prems"
        by(cases heads'; auto)

      obtain n' where N' : "n = Suc n'"
        using "1.prems" Tcons Hcons 
        by(cases n; auto split:sum.split_asm prod.split_asm if_split_asm)

      show ?thesis
      proof(cases heads'h)
        case Hnone : None

        obtain t'h where Tsome : "tails'h = Some t'h"
          using "1.prems" Tcons Hcons N' Hnone
          by(cases tails'h; auto)

        obtain vhbytes where Vhdec :
          "decode' t (int (length pre1) + decode_sint (take 32 code), pre1 @ pre2 @ code) = 
              Ok (vh, vhbytes)"
          using "1.prems" Tcons Hcons N' Hnone Tsome 
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain hsbytes where Hsdec :
          "decode'_dyn_tuple_heads (replicate n' t) (int (length pre2) + 32) 
              (int (length pre1), pre1 @ pre2 @ code) =
         Ok (heads't, tails't, count', hsbytes)" using "1.prems" Tcons Hcons N' Hnone Tsome 
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain tsbytes where Tsdec : 
          "decode'_dyn_tuple_tails tails't (replicate n' t) heads't (count'' + vhbytes) 
              (int (length pre1), pre1 @ pre2 @ code) = Ok (vt, tsbytes)"
          using "1.prems" Tcons Hcons N' Hnone Tsome Vhdec
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Codelen' : "32 \<le> length code"
          using "1.prems" Hcons Tcons N' Hnone Tsome 
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        hence Codelen : "int (min (length code) 32) = 32"
          by auto

        hence Codelen_int : "min (length code) 32 = 32"
          by(auto)

        have P2' : "pre2 @ code = pre2 @ (take 32 code) @ (drop 32 code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't (replicate n' t) heads't (count'' + vhbytes) 
              (int (length pre1), pre1 @ (pre2 @ take 32 code) @  drop 32 code) = Ok (vt, tsbytes)"
          using Tsdec unfolding P2' by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads (replicate n' t) (int (length (pre2 @ take 32 code)))
             (int (length pre1), pre1 @ (pre2 @ take 32 code) @ drop 32 code) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec unfolding P2' using Codelen by(auto)

        have Vhenc :
          "can_encode_as vh (pre1 @ pre2 @ code)
            (int (length pre1) + decode_sint (take 32 code))"
          using "1.prems" Tcons Hcons N' Hnone Tsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm )

        obtain heads head_types tails where IHspec :
          "abi_value_valid (Vfarray t n' vt)"
          "is_head_and_tail vt heads head_types tails"
          "can_encode_as (Vtuple head_types heads) (pre1 @ (pre2 @ take 32 code) @ drop 32 code)
              (int (length pre1) + int (length (pre2 @ take 32 code)))"
          "(\<And> offset v . (offset, v) \<in> set tails \<Longrightarrow> 
             can_encode_as v (pre1 @ (pre2 @ take 32 code) @ drop 32 code) 
                             (int (length pre1) + offset))"
          "those (map2 ht_combine heads't (map (\<lambda>a. case a of None \<Rightarrow> None 
                   | Some t \<Rightarrow> Some (t - int (length pre1))) tails't)) = Some heads"
          "map (\<lambda>x. fst x + int (length pre1)) tails = somes tails't"
          "ht_wellbehaved tails't (map abi_get_type vt) heads't"
          using "1.prems" Tcons Hcons N' Hnone Tsome Vhdec Hsdec Tsdec
          "15.IH"(2)[OF refl _ _ Hsdec' Tsdec']
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have C1 : "abi_value_valid v" using IHspec(1) abi_decode'_type_ok[OF Vhdec]
          encode_correct_converse_valid[OF Vhenc] "1.prems" N'
          by(auto simp add:farray_value_valid_aux_def)

        have C2 : "is_head_and_tail (vh # vt) 
            (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)
            (Tsint 256 # head_types)
            ((decode_sint (take (32::nat) code), vh)#tails)"
          using "1.prems" IHspec(2) C1
          by(auto simp add: farray_value_valid_aux_def intro: iht_dynamic)

        have C3 : "can_encode_as (Vtuple (Tsint 256 # head_types) 
                      (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)) 
                      (pre1 @ pre2 @ code)
        (int (length pre1) + int (length pre2))" using IHspec(3)
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)
          show ?thesis 

          proof(rule Estatic_easier; (simp; fail)?)
          show 
            "abi_type_isstatic (abi_get_type (Vtuple (Tsint 256 # head_types) 
                               (Vsint 256 (decode_sint (take 32 code)) # heads)))"
            using is_head_and_tail_head_types_elem[OF IHspec(2)]
            by(auto simp add:list_ex_iff)
          next
            show "abi_value_valid (Vtuple (Tsint 256 # head_types)
                                  (Vsint 256 (decode_sint (take 32 code)) # heads))"
              using Estatic decode_sint_valid256[of "take 32 code"]
              by(auto simp add:farray_value_valid_aux_def tuple_value_valid_aux_def)
          next

            obtain hsenc where Hsenc :
              "those_err (map encode_static heads) = Ok hsenc"
              using Estatic by(auto split: sum.split_asm)

            have Len_nat : "(length pre1) + 
                            (length (pre2 @ take 32 code)) = (length preX)"
              using Estatic by(auto)

            have Codeshift1 : "drop (length preX) (pre1 @ pre2 @ code) = concat hsenc @ postX"
              using Estatic(1)  Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift2 : "drop (length pre1 + (length pre2 + 32)) (pre1 @ pre2 @ code)
              = concat hsenc @ postX"
              using Estatic(1) Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift3 : "drop 32 code = concat hsenc @ postX" 
              using Estatic(1) Estatic(3) Estatic(4) Estatic(5) Hsenc
              Len_nat Codelen 
              by(auto)

            have "(word_rsplit (word_rcat (take 32 code) :: 256 word) :: 8 word list)
                    = take 32 code"
              by(rule word_rsplit_rcat_size; auto simp add: Codelen_int word_size)

            then show "encode_static (Vtuple (Tsint 256 # head_types) 
                                (Vsint 256 (decode_sint (take 32 code)) # heads)) =
                          Ok (take (nat (foldl (+) 32 (map abi_static_size head_types))) code)"
              using Estatic "1.prems" encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
                    Int.nat_add_distrib Hsenc Codelen SMT.int_plus Codeshift3
              by(auto simp add: List.take_add)
          next
            show "nat (int (length pre1) + int (length pre2)) + 
                  nat (abi_static_size (abi_get_type (Vtuple (Tsint 256 # head_types) 
                                       (Vsint 256 (decode_sint (take 32 code)) # heads))))
                      \<le> length (pre1 @ pre2 @ code)"
              using Estatic Codelen encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
              by(auto)
          qed
        next
          case (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis using is_head_and_tail_head_types_elem[OF IHspec(2), of tX]
            by(auto)
        qed

        have C4 : 
          "(\<And> offset v.
             (offset, v) \<in> set ((decode_sint (take (32::nat) code), vh)#tails) \<Longrightarrow>
             can_encode_as v (pre1 @ pre2 @ code) (int (length pre1) + offset))" 
          using "1.prems" "15.IH"(1)[OF Vhdec] IHspec(4) abi_decode'_type_ok[OF Vhdec]
                encode_correct_converse_valid[OF Vhenc] 
          by(auto)

        have C5 :
          "those
            (map2 ht_combine heads'
              (map (case_option None (\<lambda>t. Some (t - int (length pre1)))) tails')) =
           Some (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)"
          using IHspec "1.prems" Tcons Hcons Hnone Tsome N' "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C6 : "map (\<lambda>x. fst x + int (length pre1))  
                    ((decode_sint (take (32::nat) code), vh)#tails) = somes tails'"
          using IHspec "1.prems" Tcons Hcons Hnone Tsome N' "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C7 : "ht_wellbehaved tails' (abi_get_type vh # map abi_get_type vt) heads'"
          using IHspec "1.prems" Tcons Hcons Hnone Tsome N' "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        show ?thesis 
          using C1 C2 C3 C4 C5 C6 C7 by(fastforce)
      next
        case Hsome : (Some h'h)

        hence Tnone : "tails'h = None"
          using "1.prems" Tcons Hcons N' Hsome
          by(cases tails'h; auto)

        then have False using "1.prems" Hcons Tcons Hsome Tnone N'
          by(auto split:if_split_asm sum.split_asm)

        thus ?thesis ..
      qed
    qed
  next
  (* Vtuple *)
    case 2
    show ?case 
    proof(cases tails')
      case Tnil : Nil
      then have Hnil : "heads' = []" using "2.prems"
        by(cases heads'; auto)

      show ?thesis
      proof(cases ts)
        case Nil
        then show ?thesis using "2.prems" by(auto)
      next
        case (Cons tsh tst)
        then show ?thesis using "2.prems" Tnil Hnil by(auto)
      qed
    next
      case Tcons : (Cons tails'h tails't)

      then obtain heads'h heads't where Hcons : "heads' = heads'h#heads't" using "2.prems"
        by(cases heads'; auto)

      obtain tsh tst where Tscons : "ts = tsh#tst"
        using "2.prems" Tcons Hcons 
        by(cases ts; auto split:sum.split_asm prod.split_asm if_split_asm)

      show ?thesis
      proof(cases heads'h)
        (* first tuple element is dynamic *)
        case Hnone : None

        obtain t'h where Tsome : "tails'h = Some t'h"
          using "2.prems" Tcons Hcons Hnone
          by(cases tails'h; auto)

        have Tsh_dyn : "abi_type_isdynamic tsh"
          using "2.prems" Tcons Hcons Tscons Hnone Tsome
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        obtain vhbytes where Vhdec :
          "decode' tsh (int (length pre1) + decode_sint (take 32 code), pre1 @ pre2 @ code) = 
              Ok (vh, vhbytes)"
          using "2.prems" Tcons Hcons Tscons Hnone Tsome Tsh_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain hsbytes where Hsdec :
          "decode'_dyn_tuple_heads tst (int (length pre2) + 32) 
              (int (length pre1), pre1 @ pre2 @ code) =
         Ok (heads't, tails't, count', hsbytes)" using "2.prems" Tcons Hcons Tscons Hnone Tsome 
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain tsbytes where Tsdec : 
          "decode'_dyn_tuple_tails tails't tst heads't (count'' + vhbytes) 
              (int (length pre1), pre1 @ pre2 @ code) = Ok (vt, tsbytes)"
          using "2.prems" Tcons Hcons Tscons Hnone Tsome Vhdec
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Codelen' : "32 \<le> length code"
          using "2.prems" Hcons Tcons Tscons Hnone Tsome 
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        hence Codelen : "int (min (length code) 32) = 32"
          by auto

        hence Codelen_int : "min (length code) 32 = 32"
          by(auto)

        have P2' : "pre2 @ code = pre2 @ (take 32 code) @ (drop 32 code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't tst heads't (count'' + vhbytes) 
              (int (length pre1), pre1 @ (pre2 @ take 32 code) @  drop 32 code) = Ok (vt, tsbytes)"
          using Tsdec unfolding P2' by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads tst (int (length (pre2 @ take 32 code)))
             (int (length pre1), pre1 @ (pre2 @ take 32 code) @ drop 32 code) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec unfolding P2' using Codelen by(auto)

        have Vhenc :
          "can_encode_as vh (pre1 @ pre2 @ code)
            (int (length pre1) + decode_sint (take 32 code))"
          using "2.prems" Tcons Hcons Tscons Hnone Tsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm )

        obtain heads head_types tails where IHspec :
          "abi_value_valid (Vtuple tst vt)"
          "is_head_and_tail vt heads head_types tails"
          "can_encode_as (Vtuple head_types heads) (pre1 @ (pre2 @ take 32 code) @ drop 32 code)
              (int (length pre1) + int (length (pre2 @ take 32 code)))"
          "(\<And> offset v . (offset, v) \<in> set tails \<Longrightarrow> 
             can_encode_as v (pre1 @ (pre2 @ take 32 code) @ drop 32 code) 
                             (int (length pre1) + offset))"
          "those (map2 ht_combine heads't (map (\<lambda>a. case a of None \<Rightarrow> None 
                   | Some t \<Rightarrow> Some (t - int (length pre1))) tails't)) = Some heads"
          "map (\<lambda>x. fst x + int (length pre1)) tails = somes tails't"
          "ht_wellbehaved tails't (map abi_get_type vt) heads't"
          using "2.prems" Tcons Hcons Tscons Hnone Tsome Vhdec Hsdec Tsdec
            "15.IH"(3)[OF refl _  Hsdec' Tsdec']
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        have C1 : "abi_value_valid v" using IHspec(1) abi_decode'_type_ok[OF Vhdec]
          encode_correct_converse_valid[OF Vhenc] "2.prems" Tscons
          by(auto simp add:tuple_value_valid_aux_def)

        have C2 : "is_head_and_tail (vh # vt) 
            (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)
            (Tsint 256 # head_types)
            ((decode_sint (take (32::nat) code), vh)#tails)"
          using "2.prems" IHspec(2) C1 Tsh_dyn Tscons
          by(auto simp add: tuple_value_valid_aux_def intro: iht_dynamic)

        have C3 : "can_encode_as (Vtuple (Tsint 256 # head_types) 
                      (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)) 
                      (pre1 @ pre2 @ code)
        (int (length pre1) + int (length pre2))" using IHspec(3)
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)
          show ?thesis 

          proof(rule Estatic_easier; (simp; fail)?)
          show 
            "abi_type_isstatic (abi_get_type (Vtuple (Tsint 256 # head_types) 
                               (Vsint 256 (decode_sint (take 32 code)) # heads)))"
            using is_head_and_tail_head_types_elem[OF IHspec(2)]
            by(auto simp add:list_ex_iff)
          next
            show "abi_value_valid (Vtuple (Tsint 256 # head_types)
                                  (Vsint 256 (decode_sint (take 32 code)) # heads))"
              using Estatic decode_sint_valid256[of "take 32 code"]
              by(auto simp add:farray_value_valid_aux_def tuple_value_valid_aux_def)
          next

            obtain hsenc where Hsenc :
              "those_err (map encode_static heads) = Ok hsenc"
              using Estatic by(auto split: sum.split_asm)

            have Len_nat : "(length pre1) + 
                            (length (pre2 @ take 32 code)) = (length preX)"
              using Estatic by(auto)

            have Codeshift1 : "drop (length preX) (pre1 @ pre2 @ code) = concat hsenc @ postX"
              using Estatic(1)  Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift2 : "drop (length pre1 + (length pre2 + 32)) (pre1 @ pre2 @ code)
              = concat hsenc @ postX"
              using Estatic(1) Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift3 : "drop 32 code = concat hsenc @ postX" 
              using Estatic(1) Estatic(3) Estatic(4) Estatic(5) Hsenc
              Len_nat Codelen 
              by(auto)

            have "(word_rsplit (word_rcat (take 32 code) :: 256 word) :: 8 word list)
                    = take 32 code"
              by(rule word_rsplit_rcat_size; auto simp add: Codelen_int word_size)

            then show "encode_static (Vtuple (Tsint 256 # head_types) 
                                (Vsint 256 (decode_sint (take 32 code)) # heads)) =
                          Ok (take (nat (foldl (+) 32 (map abi_static_size head_types))) code)"
              using Estatic "2.prems" encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
                    Int.nat_add_distrib Hsenc Codelen SMT.int_plus Codeshift3
              by(auto simp add: List.take_add)
          next
            show "nat (int (length pre1) + int (length pre2)) + 
                  nat (abi_static_size (abi_get_type (Vtuple (Tsint 256 # head_types) 
                                       (Vsint 256 (decode_sint (take 32 code)) # heads))))
                      \<le> length (pre1 @ pre2 @ code)"
              using Estatic Codelen encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
              by(auto)
          qed
        next
          case (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis using is_head_and_tail_head_types_elem[OF IHspec(2), of tX]
            by(auto)
        qed

        have C4 : 
          "(\<And> offset v.
             (offset, v) \<in> set ((decode_sint (take (32::nat) code), vh)#tails) \<Longrightarrow>
             can_encode_as v (pre1 @ pre2 @ code) (int (length pre1) + offset))" 
          using "2.prems" "15.IH"(1)[OF Vhdec] IHspec(4) abi_decode'_type_ok[OF Vhdec]
                encode_correct_converse_valid[OF Vhenc] 
          by(auto)

        have C5 :
          "those
            (map2 ht_combine heads'
              (map (case_option None (\<lambda>t. Some (t - int (length pre1)))) tails')) =
           Some (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)"
          using IHspec "2.prems" Tcons Hcons Hnone Tsome Tscons Tsh_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C6 : "map (\<lambda>x. fst x + int (length pre1))  
                    ((decode_sint (take (32::nat) code), vh)#tails) = somes tails'"
          using IHspec "2.prems" Tcons Hcons Hnone Tsome Tscons Tsh_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C7 : "ht_wellbehaved tails' (abi_get_type vh # map abi_get_type vt) heads'"
          using IHspec "2.prems" Tcons Hcons Hnone Tsome Tscons Tsh_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        show ?thesis 
          using C1 C2 C3 C4 C5 C6 C7 by(fastforce)
      next
        case Hsome : (Some h'h)

        have Tnone : "tails'h = None"
          using "2.prems" Tcons Hcons Hsome
          by(cases tails'h; auto)

        have Tsh_static : "abi_type_isstatic tsh"
          using "2.prems" Tcons Hcons Tscons Hsome Tnone
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        obtain vhbytes where Vhdec :
          "decode' tsh (int (length pre1) + int (length pre2), pre1 @ pre2 @ code) = 
              Ok (vh, vhbytes)"
          using "2.prems" Tcons Hcons Tscons Hsome Tnone Tsh_static
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Tsh_vh : "abi_get_type vh = tsh"
          using Estatic "2.prems" Hsome Tnone Tsh_static Vhdec
          abi_decode'_type_ok[OF Vhdec] by(auto)

        obtain hsbytes where Hsdec :
          "decode'_dyn_tuple_heads tst (int (length pre2) + abi_static_size tsh)
            (int (length pre1), pre1 @ pre2 @ code) =
         Ok (heads't, tails't, count', hsbytes)"
          using "2.prems" Tcons Hcons Tscons Tnone Hsome Tsh_static  abi_static_size_nonneg
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain tsbytes where Tsdec : 
          "decode'_dyn_tuple_tails tails't tst heads't (count'') 
              (int (length pre1), pre1 @ pre2 @ code) = Ok (vt, tsbytes)"
          using "2.prems" Tcons Hcons Tscons Tnone Hsome Vhdec Hsdec
                          Tsh_static abi_static_size_nonneg
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vhenc :
          "can_encode_as vh (pre1 @ pre2 @ code)
            (int (length pre1) + int (length pre2))"
          using "2.prems" Tcons Hcons Tscons Tnone Hsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vh_static : "abi_type_isstatic (abi_get_type vh)"
          using "2.prems" Tcons Hcons Tscons Tnone Hsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vhenc_static' : 
          "encode_static vh = Ok (take (nat (abi_static_size tsh)) code) \<and>
           abi_value_valid vh"
          using Vhenc Vh_static
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)

          have Len_nat : "(length (pre1@ pre2)) = (length preX)"
            using Estatic by auto

          have Len_h_nat : "nat (abi_static_size (abi_get_type vh)) = (length codeX)"
            using Estatic abi_static_size_nonneg[of "abi_get_type vh"]
              encode_static_size[of vh codeX]
            by(auto)

          hence Codeshift1 : "drop ((length pre1) + (length pre2)) ((pre1 @ pre2) @ code)
            = codeX @ postX"
            using Estatic(1) Estatic(5)
            Len_nat 
            by(auto)

          hence Codeshift2 : "code = codeX @ postX" 
            using Estatic(1) Estatic(3) Estatic(4) Estatic(5) 
            Len_nat unfolding List.drop_append
            by(auto)

          then show ?thesis using Estatic encode_static_size[of vh codeX]
              abi_static_size_nonneg[of "tsh"]
              Len_h_nat Tsh_vh
            by(auto)
        next
          (* NB: remaining cases are all trivial contradictions *)
          case (Etuple_dyn ts vs t heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Efarray_dyn t n vs heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Earray t vs heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Ebytes l pre post count code)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Estring s l)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        qed

        hence Vhenc_static : "encode_static vh = Ok (take (nat (abi_static_size tsh)) code)"
          by auto

        have Codelen' : "abi_static_size tsh \<le> length code"
          using encode_static_size[OF Vhenc_static] Tsh_vh Vhenc_static'
          by(auto)

        hence Codelen_int : "min (length code) (abi_static_size tsh) = (abi_static_size tsh)"
          by(auto)

        hence Codelen : "(int (min (length code) (nat (abi_static_size tsh))))
                           = abi_static_size tsh"
          using abi_static_size_nonneg[of tsh]
          by auto

        have P2' : "pre2 @ code = pre2 @ (take (nat (abi_static_size tsh)) code) @ 
                                         (drop (nat (abi_static_size tsh)) code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't tst heads't (count'') 
              (int (length pre1), pre1 @ (pre2 @ (take (nat (abi_static_size tsh)) code)) @  
                                  (drop (nat (abi_static_size tsh)) code)) = Ok (vt, tsbytes)"
          using Tsdec unfolding P2' by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads tst (
                                int (length (pre2 @ take (nat (abi_static_size tsh)) code)))
             (int (length pre1), pre1 @ (pre2 @ (take (nat (abi_static_size tsh)) code)) @  
                                  (drop (nat (abi_static_size tsh)) code)) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec unfolding P2' using Codelen by(auto)

        obtain heads head_types tails where IHspec :
          "abi_value_valid (Vtuple tst vt)"
          "is_head_and_tail vt heads head_types tails"
          "can_encode_as (Vtuple head_types heads) 
                         (pre1 @ (pre2 @ (take (nat (abi_static_size tsh)) code))
                               @ drop (nat (abi_static_size tsh)) code)
              (int (length pre1) + int (length (pre2 @ take (nat (abi_static_size tsh)) code)))"
          "(\<And> offset v . (offset, v) \<in> set tails \<Longrightarrow> 
             can_encode_as v (pre1 @ (pre2 @ take (nat (abi_static_size tsh)) code) 
                                   @ drop (nat (abi_static_size tsh)) code) 
                             (int (length pre1) + offset))"
          "those (map2 ht_combine heads't (map (\<lambda>a. case a of None \<Rightarrow> None 
                   | Some t \<Rightarrow> Some (t - int (length pre1))) tails't)) = Some heads"
          "map (\<lambda>x. fst x + int (length pre1)) tails = somes tails't"
          "ht_wellbehaved tails't (map abi_get_type vt) heads't"
          using "2.prems" Tcons Hcons Tscons Tnone Hsome Vhdec Hsdec Tsdec
          "15.IH"(3)[OF refl _ Hsdec' Tsdec']
          by(auto split:prod.split_asm if_split_asm sum.split_asm)
       
        have C1 : "abi_value_valid v" using IHspec(1) abi_decode'_type_ok[OF Vhdec]
          encode_correct_converse_valid[OF Vhenc] "2.prems" Tscons
          by(auto simp add:tuple_value_valid_aux_def)

        have C2 : "is_head_and_tail (vh # vt) 
            (vh# heads)
            (tsh # head_types)
            (tails)"
          using "2.prems" IHspec(2) C1 Tsh_static Tscons
          by(auto simp add: tuple_value_valid_aux_def intro: iht_static)

        have C3 : "can_encode_as (Vtuple (tsh # head_types) 
                      (vh# heads)) 
                      (pre1 @ pre2 @ code)
        (int (length pre1) + int (length pre2))" using IHspec(3)
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)
          show ?thesis 

          proof(rule Estatic_easier; (simp; fail)?)
          show 
            "abi_type_isstatic (abi_get_type (Vtuple (tsh # head_types) (vh # heads)))"
            using is_head_and_tail_head_types_elem[OF IHspec(2)] Tsh_static
            by(auto simp add:list_ex_iff)
          next
            show "abi_value_valid (Vtuple (tsh # head_types) (vh # heads))"
              using Estatic C1 "2.prems" Tscons
              by(auto simp add:tuple_value_valid_aux_def)
          next
            obtain hsenc where Hsenc :
              "those_err (map encode_static heads) = Ok hsenc"
              using Estatic by(auto split: sum.split_asm)

            have Len_nat : "(length pre1) + 
                            (length (pre2 @  take (nat (abi_static_size tsh)) code)) 
                            = (length preX)"
              using Estatic by(auto)

            have Codeshift1 : "drop (length preX) (pre1 @ pre2 @ code) = concat hsenc @ postX"
              using Estatic(1)  Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift2 : "drop (length pre1 + (length pre2 + nat (abi_static_size tsh))) 
                                (pre1 @ pre2 @ code) = concat hsenc @ postX"
              using Estatic(1) Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift3 : "drop (nat (abi_static_size tsh)) code = concat hsenc @ postX" 
              using Estatic(1) Estatic(3) Estatic(4) Estatic(5) Hsenc
              Len_nat Codelen 
              by(auto)

            then show "encode_static (Vtuple (tsh # head_types) (vh # heads)) =
                          Ok (take (nat (foldl (+) (abi_static_size tsh)
                                        (map abi_static_size head_types))) code)"
              using Estatic Vhenc_static "2.prems" encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of "(abi_static_size tsh)" 0 
                                         "(map abi_static_size head_types)"]]
                    Int.nat_add_distrib Hsenc Codelen SMT.int_plus Codeshift3
              by(auto simp add: List.take_add )
          next
            show "nat (int (length pre1) + int (length pre2)) + 
                  nat (abi_static_size (abi_get_type (Vtuple (tsh # head_types) (vh # heads))))
                      \<le> length (pre1 @ pre2 @ code)"
              using Estatic Codelen encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of "(abi_static_size tsh)" 0 
                                         "(map abi_static_size head_types)"]]
              by(auto)
          qed
        next
          case (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis using is_head_and_tail_head_types_elem[OF IHspec(2), of tX]
            by(auto)
        qed

        have C4 : 
          "(\<And> offset v.
             (offset, v) \<in> set (tails) \<Longrightarrow>
             can_encode_as v (pre1 @ pre2 @ code) (int (length pre1) + offset))" 
          using "2.prems" "15.IH"(1)[OF Vhdec] IHspec(4) abi_decode'_type_ok[OF Vhdec]
                encode_correct_converse_valid[OF Vhenc] 
          by(auto)

        have C5 :
          "those
            (map2 ht_combine heads'
              (map (case_option None (\<lambda>t. Some (t - int (length pre1)))) tails')) =
           Some (vh# heads)"
          using IHspec "2.prems" Tcons Hcons Tnone Hsome Tscons Tsh_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C6 : "map (\<lambda>x. fst x + int (length pre1))  
                    (tails) = somes tails'"
          using IHspec "2.prems" Tcons Hcons Tnone Hsome Tscons Tsh_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C7 : "ht_wellbehaved tails' (abi_get_type vh # map abi_get_type vt) heads'"
          using IHspec "2.prems" Tcons Hcons Tnone Hsome Tscons Tsh_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        show ?thesis 
          using C1 C2 C3 C4 C5 C6 C7 by(fastforce)
      qed
    qed
  next
  (* Varray*)
    case 3
    show ?case
    proof(cases tails')
      case Tnil : Nil
      then have Hnil : "heads' = []" using "3.prems"
        by(cases heads'; auto)

      show ?thesis using "3.prems"
      proof(cases n)
        case 0
        then show ?thesis using "3.prems" by(auto)
      next
        case (Suc np)
        then show ?thesis using "3.prems" Tnil Hnil by(auto)
      qed
    next
      case Tcons : (Cons tails'h tails't)

      then obtain heads'h heads't where Hcons : "heads' = heads'h#heads't" using "3.prems"
        by(cases heads'; auto)

      obtain np where Np : "n = Suc np"
        using "3.prems" Tcons Hcons 
        by(auto split:sum.split_asm prod.split_asm if_split_asm)

      show ?thesis
      proof(cases heads'h)
        (* array of dynamic elements *)
        case Hnone : None

        obtain t'h where Tsome : "tails'h = Some t'h"
          using "3.prems" Tcons Hcons Hnone
          by(cases tails'h; auto)

        have T_dyn : "abi_type_isdynamic t"
          using "3.prems" Tcons Hcons Np Hnone Tsome
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        obtain vhbytes where Vhdec :
          "decode' t (int (length pre1) + 32 + decode_sint (take 32 code),
              pre1 @ encode_int (int n') @ pre2 @ code) = 
              Ok (vh, vhbytes)"
          using "3.prems" Tcons Hcons Np Hnone Tsome T_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have T_vh : "abi_get_type vh = t"
          using Estatic "3.prems" Tsome Hnone T_dyn Vhdec
          abi_decode'_type_ok[OF Vhdec] by(auto)

        obtain hsbytes where Hsdec :
          "decode'_dyn_tuple_heads (replicate (length vt) t) (int (length pre2) + 32) 
              (int (length pre1) + 32, pre1 @ encode_int (int n') @ pre2 @ code) =
             Ok (heads't, tails't, count', hsbytes)"
          using "3.prems" Tcons Hcons Np Hnone Tsome T_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain tsbytes where Tsdec : 
          "decode'_dyn_tuple_tails tails't (replicate (length vt) t) heads't (count'' + vhbytes) 
              (int (length pre1) + 32, pre1 @ encode_int (int n') @ pre2 @ code) = Ok (vt, tsbytes)"
          using "3.prems" Tcons Hcons Np Hnone Tsome Vhdec T_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Codelen' : "32 \<le> length code"
          using "3.prems" Hcons Tcons Np Hnone Tsome T_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        hence Codelen : "int (min (length code) 32) = 32"
          by auto

        hence Codelen_int : "min (length code) 32 = 32"
          by(auto)

        have P2' : "pre2 @ code = pre2 @ (take 32 code) @ (drop 32 code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't (replicate (length vt) t) heads't (count'' + vhbytes) 
              (int (length pre1) + 32, pre1 @ encode_int (int n') @ 
                                       (pre2 @ take 32 code) @ drop 32 code) = Ok (vt, tsbytes)"
          using Tsdec unfolding P2' by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads (replicate (length vt) t) (int (length (pre2 @ take 32 code)))
             (int (length pre1) + 32, pre1 @ encode_int (int n') @  
                                      (pre2 @ take 32 code) @ drop 32 code) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec unfolding P2' using Codelen by(auto)

        have Vhenc :
          "can_encode_as vh (pre1 @ encode_int (int n') @  pre2 @ code)
            (int (length pre1) + 32 + decode_sint (take 32 code))"
          using "3.prems" Tcons Hcons Np Hnone Tsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm )

        have Codelen' : "32 \<le> length code"
          using "3.prems" Hcons Tcons Np Hnone Tsome T_dyn
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        hence Codelen : "int (min (length code) 32) = 32"
          by auto

        hence Codelen_int : "min (length code) 32 = 32"
          by(auto)

        have P2' : "pre2 @ code = pre2 @ (take 32 code) @ (drop 32 code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't (replicate (length vt) t) heads't (count'' + vhbytes) 
              (int (length (pre1 @ encode_int (int n'))), pre1 @ encode_int (int n') @ 
              (pre2 @ take 32 code) @ drop 32 code) = Ok (vt, tsbytes)"
          using Tsdec int_length unfolding P2' by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads (replicate (length vt) t) (int (length (pre2 @ take 32 code)))
             (int (length (pre1 @ encode_int (int n'))), pre1 @ encode_int (int n') @ 
             (pre2 @ take 32 code) @ drop 32 code) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec int_length unfolding P2' using Codelen by(auto)

        have Vhenc :
          "can_encode_as vh (pre1 @ encode_int (int n') @ pre2 @ code)
            (int (length (pre1 @ encode_int (int n'))) + decode_sint (take 32 code))"
          using "3.prems" Tcons Hcons Hnone Tsome Vhdec Hsdec Tsdec T_dyn Np
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm )

        have Vt_len_valid : "uint_value_valid 256 (int (length vt))"
          using "3.prems"
          by(auto simp add: uint_value_valid_def)

        obtain heads head_types tails where IHspec :
          "abi_value_valid (Varray t vt)"
          "is_head_and_tail vt heads head_types tails"
          "can_encode_as (Vtuple head_types heads) 
                         (pre1 @ encode_int (int n') @ (pre2 @ take 32 code) @ drop 32 code)
                         (int (length pre1) + 32 + int (length (pre2 @ take 32 code)))"
          "(\<And> offset v.
              (offset, v) \<in> set tails \<Longrightarrow>
              can_encode_as v (pre1 @ encode_int (int n') @(pre2 @ take 32 code) @ drop 32 code) 
                              (int (length pre1) + 32 + offset))"
          "those
           (map2 ht_combine heads't
            (map (\<lambda>a. case a of None \<Rightarrow> None 
                            | Some t \<Rightarrow> Some (t - int (length pre1) - 32)) tails't)) =
              Some heads"
          "map (\<lambda>x. fst x + int (length pre1) + 32) tails = somes tails't"
          "ht_wellbehaved tails't (map abi_get_type vt) heads't"
          using "3.prems" Tcons Hcons Np Hnone Tsome Vhdec Hsdec Tsdec T_dyn
                "15.IH"(4)[OF refl _ _ Vt_len_valid _ refl _ refl Hsdec' Tsdec']
                int_length[of "int n'"]
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        have C1 : "abi_value_valid v" using IHspec(1) abi_decode'_type_ok[OF Vhdec]
          encode_correct_converse_valid[OF Vhenc] "3.prems" 
          by(auto simp add:array_value_valid_aux_def )

        have C2 : "is_head_and_tail (vh # vt) 
            (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)
            (Tsint 256 # head_types)
            ((decode_sint (take (32::nat) code), vh)#tails)"
          using "3.prems" IHspec(2) C1 T_dyn Np
          by(auto simp add: array_value_valid_aux_def intro: iht_dynamic)

        have C3 : "can_encode_as (Vtuple (Tsint 256 # head_types) 
                      (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)) 
                      (pre1 @ encode_int (int n') @  pre2 @ code)
        (int (length pre1) + 32 + int (length pre2))" using IHspec(3)
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)
          show ?thesis 

          proof(rule Estatic_easier; (fast; fail)?)
          show 
            "abi_type_isstatic (abi_get_type (Vtuple (Tsint 256 # head_types) 
                               (Vsint 256 (decode_sint (take 32 code)) # heads)))"
            using is_head_and_tail_head_types_elem[OF IHspec(2)]
            by(auto simp add:list_ex_iff)
          next
            show "abi_value_valid (Vtuple (Tsint 256 # head_types)
                                  (Vsint 256 (decode_sint (take 32 code)) # heads))"
              using Estatic decode_sint_valid256[of "take 32 code"]
              by(auto simp add:array_value_valid_aux_def tuple_value_valid_aux_def)
          next

            obtain hsenc where Hsenc :
              "those_err (map encode_static heads) = Ok hsenc"
              using Estatic by(auto split: sum.split_asm)

            have Len_nat : "(length pre1) + 32 +
                            (length (pre2 @ take 32 code)) = (length preX)"
              using Estatic by(auto)

            have Codeshift1 : "drop (length preX) (pre1 @ encode_int (int n') @ 
                                                   pre2 @ code) = concat hsenc @ postX"
              using Estatic(1)  Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift2 : "drop (length pre1 + 32 + (length pre2 + 32))
                                     (pre1 @ encode_int (int n') @ pre2 @ code)
              = concat hsenc @ postX"
              using Estatic(1) Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift3 : "drop 32 code = concat hsenc @ postX" 
              using Estatic(1) Estatic(3) Estatic(4) Estatic(5) Hsenc
              Len_nat Codelen int_length
              by(auto)

            have "(word_rsplit (word_rcat (take 32 code) :: 256 word) :: 8 word list)
                    = take 32 code"
              by(rule word_rsplit_rcat_size; auto simp add: Codelen_int word_size)

            then show "encode_static (Vtuple (Tsint 256 # head_types)
                                      (Vsint 256 (decode_sint (take 32 code)) # heads)) =
                           Ok (take (nat (abi_static_size (abi_get_type 
                                      (Vtuple (Tsint 256 # head_types) 
                                        (Vsint 256 (decode_sint (take 32 code)) # heads)))))
                                     (drop (nat (int (length pre1) + 32 + int (length pre2))) 
                                           (pre1 @ encode_int (int n') @ pre2 @ code)))"
              using Estatic "3.prems" encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
                    Int.nat_add_distrib Hsenc Codelen SMT.int_plus Codeshift3
              by(auto simp add: List.take_add)
          next
            show "0 \<le> int (length pre1) + 32 + int (length pre2)" by auto
          next
            show "nat (int (length pre1) + 32 + int (length pre2)) + 
                  nat (abi_static_size (abi_get_type (Vtuple (Tsint 256 # head_types) 
                                       (Vsint 256 (decode_sint (take 32 code)) # heads))))
                      \<le> length (pre1 @ encode_int (int n') @ pre2 @ code)"
              using Estatic Codelen encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of 32 0 "(map abi_static_size head_types)"]]
              by(auto)
          qed
        next
          case (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis using is_head_and_tail_head_types_elem[OF IHspec(2), of tX]
            by(auto)
        qed

        have C4 : 
          "(\<And> offset v.
             (offset, v) \<in> set ((decode_sint (take (32::nat) code), vh)#tails) \<Longrightarrow>
             can_encode_as v (pre1 @ encode_int (int n') 
                                   @ pre2 @ code) (int (length pre1) + 32 +  offset))" 
          using "3.prems" "15.IH"(1)[OF Vhdec] IHspec(4) abi_decode'_type_ok[OF Vhdec]
                encode_correct_converse_valid[OF Vhenc] 
          by(auto)

        have C5 :
          "those
            (map2 ht_combine heads'
              (map (case_option None (\<lambda>t. Some (t - int (length pre1) - 32))) tails')) =
           Some (Vsint (256::nat) (decode_sint (take (32::nat) code))# heads)"
          using IHspec "3.prems" Tcons Hcons Hnone Tsome Np T_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C6 : "map (\<lambda>x. fst x + int (length pre1) + 32)  
                    ((decode_sint (take (32::nat) code), vh)#tails) = somes tails'"
          using IHspec "3.prems" Tcons Hcons Hnone Tsome Np T_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C7 : "ht_wellbehaved tails' (abi_get_type vh # map abi_get_type vt) heads'"
          using IHspec "3.prems" Tcons Hcons Hnone Tsome Np T_dyn "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        show ?thesis 
          using C1 C2 C3 C4 C5 C6 C7 unfolding "3.prems"(8)
          by(fastforce)
      next
        case Hsome : (Some h'h)

        have Tnone : "tails'h = None"
          using "3.prems" Tcons Hcons Hsome
          by(cases tails'h; auto)

        have T_static : "abi_type_isstatic t"
          using "3.prems" Tcons Hcons Np Hsome Tnone
          by(auto split:prod.split_asm if_split_asm sum.split_asm)

        obtain vhbytes where Vhdec :
          "decode' t (int (length pre1) + 32 + int (length pre2),
              pre1 @ encode_int (int n') @ pre2 @ code) = 
              Ok (vh, vhbytes)"
          using "3.prems" Tcons Hcons Np Hsome Tnone T_static
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have T_vh : "abi_get_type vh = t"
          using Estatic "3.prems" Tnone Hsome T_static Vhdec
          abi_decode'_type_ok[OF Vhdec] by(auto)

        obtain hsbytes where Hsdec :
          "decode'_dyn_tuple_heads (replicate (length vt) t) (int (length pre2) + abi_static_size t) 
              (int (length pre1) + 32, pre1 @ encode_int (int n') @ pre2 @ code) =
             Ok (heads't, tails't, count', hsbytes)"
          using "3.prems" Tcons Hcons Np Hsome Tnone T_static T_vh abi_static_size_nonneg
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        obtain tsbytes where Tsdec : 
          "decode'_dyn_tuple_tails tails't (replicate (length vt) t) heads't (count'') 
              (int (length pre1) + 32, pre1 @ encode_int (int n') @ pre2 @ code) = Ok (vt, tsbytes)"
          using "3.prems" Tcons Hcons Np Hsome Tnone Vhdec T_static
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vhenc :
          "can_encode_as vh (pre1 @ encode_int (int n') @  pre2 @ code)
            (int (length pre1) + 32 + int (length pre2))"
          using "3.prems" Tcons Hcons Np Tnone Hsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vh_static : "abi_type_isstatic (abi_get_type vh)"
          using "3.prems" Tcons Hcons Np Tnone Hsome Vhdec Hsdec Tsdec
            abi_decode'_type_ok[OF Vhdec]
            "15.IH"(1)[OF Vhdec]
          by(auto split:sum.split_asm prod.split_asm if_split_asm)

        have Vhenc_static' : 
          "encode_static vh = Ok (take (nat (abi_static_size t)) code) \<and>
           abi_value_valid vh"
          using Vhenc Vh_static
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)

          have Len_nat : "(length (pre1@   encode_int (int n') @ pre2)) = (length preX)"
            using Estatic int_length by auto

          have Len_h_nat : "nat (abi_static_size (abi_get_type vh)) = (length codeX)"
            using Estatic abi_static_size_nonneg[of "abi_get_type vh"]
              encode_static_size[of vh codeX]
            by(auto)

          hence Codeshift1 : "drop ((length pre1) + 32 + (length pre2)) 
                                   ((pre1 @ encode_int (int n') @ pre2) @ code)
            = codeX @ postX"
            using Estatic(1) Estatic(5) int_length[of "int n'"]
            Len_nat 
            by(auto)

          hence Codeshift2 : "code = codeX @ postX" 
            using Estatic(1) Estatic(3) Estatic(4) Estatic(5) 
            Len_nat int_length[of "int n'"]
            unfolding List.drop_append
            by(auto)

          then show ?thesis using Estatic encode_static_size[of vh codeX]
              Len_h_nat T_vh
            by(auto)
        next
          (* NB: remaining cases are all trivial contradictions *)
          case (Etuple_dyn ts vs t heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Efarray_dyn t n vs heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Earray t vs heads head_types tails)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Ebytes l pre post count code)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        next
          case (Estring s l)
          then show ?thesis using Vh_static 
            by(auto simp add:list_all_iff tuple_value_valid_aux_def list_ex_iff)
        qed

        hence Vhenc_static : "encode_static vh = Ok (take (nat (abi_static_size t)) code)"
          by auto

        have Codelen' : "abi_static_size t \<le> length code"
          using encode_static_size[OF Vhenc_static] T_vh Vhenc_static'
          by(auto)

        hence Codelen_int : "min (length code) (abi_static_size t) = (abi_static_size t)"
          by(auto)

        hence Codelen : "(int (min (length code) (nat (abi_static_size t))))
                           = abi_static_size t"
          using abi_static_size_nonneg[of t]
          by auto

        have P2' : "pre2 @ code = pre2 @ (take (nat (abi_static_size t)) code) @ 
                                         (drop (nat (abi_static_size t)) code)"
          by(auto)

        have Tsdec' :
          "decode'_dyn_tuple_tails tails't (replicate (length vt) t) heads't (count'') 
              (int (length (pre1 @ encode_int (int n'))), pre1 @ encode_int (int n') @ 
                                  (pre2 @ (take (nat (abi_static_size t)) code)) @  
                                  (drop (nat (abi_static_size t)) code)) = Ok (vt, tsbytes)"
          using Tsdec unfolding P2' using int_length  by auto

        have Hsdec' :
          "decode'_dyn_tuple_heads (replicate (length vt) t) (
                                int (length (pre2 @ take (nat (abi_static_size t)) code)))
             (int (length (pre1 @ encode_int (int n'))), pre1 @ encode_int (int n') @ 
                                  (pre2 @ (take (nat (abi_static_size t)) code)) @  
                                  (drop (nat (abi_static_size t)) code)) =
              Ok (heads't, tails't, count', hsbytes)" 
          using Hsdec unfolding P2' using int_length Codelen  by(auto)

        have Vt_len_valid : "uint_value_valid 256 (int (length vt))"
          using "3.prems"
          by(auto simp add: uint_value_valid_def)

        obtain heads head_types tails where IHspec :
          "abi_value_valid (Varray t vt)"
          "is_head_and_tail vt heads head_types tails"
          "can_encode_as (Vtuple head_types heads) 
                         (pre1 @ encode_int (int n') @ 
                           (pre2 @ take (nat (abi_static_size t)) code) @ 
                             drop (nat (abi_static_size t)) code)
                         (int (length pre1) + 32 +  
                          int (length (pre2 @ take (nat (abi_static_size t)) code)))"
          "(\<And> offset v.
              (offset, v) \<in> set tails \<Longrightarrow>
              can_encode_as v (pre1 @ encode_int (int n') @ 
                                (pre2 @ take (nat (abi_static_size t)) code) @ 
                                  drop (nat (abi_static_size t)) code) 
                              (int (length pre1) + 32 + offset))"
          "those
           (map2 ht_combine heads't
            (map (\<lambda>a. case a of None \<Rightarrow> None 
                            | Some t \<Rightarrow> Some (t - int (length pre1) - 32)) tails't)) =
              Some heads"
          "map (\<lambda>x. fst x + int (length pre1) + 32) tails = somes tails't"
          "ht_wellbehaved tails't (map abi_get_type vt) heads't"
          using "3.prems" Tcons Hcons Np Tnone Hsome Vhdec Hsdec Tsdec T_static
                "15.IH"(4)[OF refl _ _ Vt_len_valid _ refl _ refl Hsdec' Tsdec']
                int_length[of "int n'"]
          by(auto split:prod.split_asm if_split_asm sum.split_asm)


        have C1 : "abi_value_valid v" using IHspec(1) abi_decode'_type_ok[OF Vhdec]
          encode_correct_converse_valid[OF Vhenc] "3.prems" 
          by(auto simp add:array_value_valid_aux_def )

        have C2 : "is_head_and_tail (vh # vt) 
            (vh# heads)
            (t# head_types)
            (tails)"
          using "3.prems" IHspec(2) C1 T_static Np
          by(auto simp add: array_value_valid_aux_def intro: iht_static)

        have C3 : "can_encode_as (Vtuple (t # head_types) 
                      (vh# heads)) 
                      (pre1 @ encode_int (int n') @  pre2 @ code)
        (int (length pre1) + 32 + int (length pre2))" using IHspec(3)
        proof(cases rule: can_encode_as.cases)
          case (Estatic preX postX codeX)
          show ?thesis 

          proof(rule Estatic_easier; (fast; fail)?)
          show 
            "abi_type_isstatic (abi_get_type (Vtuple (t # head_types) (vh # heads)))"
            using is_head_and_tail_head_types_elem[OF IHspec(2)] T_static
            by(auto simp add:list_ex_iff)
          next
            show "abi_value_valid (Vtuple (t # head_types)
                                  (vh # heads))"
              using Estatic C1 "3.prems" Np
              by(auto simp add:array_value_valid_aux_def tuple_value_valid_aux_def)
          next

            obtain hsenc where Hsenc :
              "those_err (map encode_static heads) = Ok hsenc"
              using Estatic by(auto split: sum.split_asm)

            have Len_nat : "(length pre1) + 32 +
                            (length (pre2 @ take (nat (abi_static_size t)) code)) = (length preX)"
              using Estatic by(auto)

            have Codeshift1 : "drop (length preX) (pre1 @ encode_int (int n') @ 
                                                   pre2 @ code) = concat hsenc @ postX"
              using Estatic(1)  Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift2 : "drop (length pre1 + 32 + (length pre2 + (nat (abi_static_size t))))
                                     (pre1 @ encode_int (int n') @ pre2 @ code)
              = concat hsenc @ postX"
              using Estatic(1) Estatic(5)
              Len_nat Codelen Hsenc
              by(auto)

            hence Codeshift3 : "drop (nat (abi_static_size t)) code = concat hsenc @ postX" 
              using Estatic(1) Estatic(3) Estatic(4) Estatic(5) Hsenc
              Len_nat Codelen int_length
              by(auto)

            then show "encode_static (Vtuple (t # head_types)
                                      (vh # heads)) =
                           Ok (take (nat (abi_static_size (abi_get_type 
                                      (Vtuple (t # head_types) 
                                        (vh # heads)))))
                                     (drop (nat (int (length pre1) + 32 + int (length pre2))) 
                                           (pre1 @ encode_int (int n') @ pre2 @ code)))"
              using Estatic "3.prems" encode_static_size[OF Estatic(5)] 
                    Vhenc_static
                    sym[OF foldl_plus[of "(abi_static_size t)"
                                      0 "(map abi_static_size head_types)"]]
                    Int.nat_add_distrib Hsenc Codelen SMT.int_plus Codeshift3
              by(auto simp add: List.take_add)
          next
            show "0 \<le> int (length pre1) + 32 + int (length pre2)" by auto
          next
            show "nat (int (length pre1) + 32 + int (length pre2)) + 
                  nat (abi_static_size (abi_get_type (Vtuple (t # head_types) 
                                       (vh # heads))))
                      \<le> length (pre1 @ encode_int (int n') @ pre2 @ code)"
              using Estatic Codelen encode_static_size[OF Estatic(5)] 
                    sym[OF foldl_plus[of "(abi_static_size t)"
                                      0 "(map abi_static_size head_types)"]]
              by(auto)
          qed
        next
          case (Etuple_dyn tX headsX head_typesX tailsX)
          then show ?thesis using is_head_and_tail_head_types_elem[OF IHspec(2), of tX]
            by(auto)
        qed

        have C4 : 
          "(\<And> offset v.
             (offset, v) \<in> set tails \<Longrightarrow>
             can_encode_as v (pre1 @ encode_int (int n') 
                                   @ pre2 @ code) (int (length pre1) + 32 +  offset))" 
          using "3.prems" "15.IH"(1)[OF Vhdec] IHspec(4) abi_decode'_type_ok[OF Vhdec]
                encode_correct_converse_valid[OF Vhenc] 
          by(auto)

        have C5 :
          "those
            (map2 ht_combine heads'
              (map (case_option None (\<lambda>t. Some (t - int (length pre1) - 32))) tails')) =
           Some (vh# heads)"
          using IHspec "3.prems" Tcons Hcons Hsome Tnone Np T_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C6 : "map (\<lambda>x. fst x + int (length pre1) + 32)  
                    (tails) = somes tails'"
          using IHspec "3.prems" Tcons Hcons Hsome Tnone Np T_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        have C7 : "ht_wellbehaved tails' (abi_get_type vh # map abi_get_type vt) heads'"
          using IHspec "3.prems" Tcons Hcons Hsome Tnone Np T_static "15.IH"(1)[OF Vhdec]
            abi_decode'_type_ok[OF Vhdec] Vhdec
            encode_correct_converse_valid[OF Vhenc] by(auto split:sum.split_asm if_split_asm)

        show ?thesis 
          using C1 C2 C3 C4 C5 C6 C7 unfolding "3.prems"(8)
          by(fastforce)
      qed
    qed
  }
qed

(* Main theorem 4: Decoder implies specification *)
theorem abi_decode_correct_converse :
  assumes H : "decode t full_code = Ok v"
  shows "can_encode_as v full_code (0)"
proof(-)

  have 0 : "abi_type_valid t" using H by(simp split:if_splits)

  have 1 : "\<exists> len . decode' t (0, full_code) = Ok (v, len)" using H 
    by(simp split:if_splits sum.splits prod.splits)

  then obtain len where 2 : "decode' t (0, full_code) = Ok (v, len)" ..

  have 3 : "abi_get_type v = t" using abi_decode'_type_ok[OF 2] by auto

  show ?thesis using abi_decode_succeed_converse_gen(1)[OF 2 0 3] by assumption
qed

end