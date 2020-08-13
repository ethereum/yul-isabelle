theory AbiEncodeCorrect imports AbiEncodeSpec AbiEncode HOL.Int

begin

(* Alternate induction principle for ABI values
   Removes the need for double-induction on the tree nodes
   and lists of children *)
lemma my_abi_value_induct :
  assumes Huint : "(\<And> n i . P1 (Vuint n i))"
  and Hsint : "(\<And> n i . P1 (Vsint n i))"
  and Haddr : "(\<And> i . P1 (Vaddr i))"
  and Hbool : "(\<And> b . P1 (Vbool b))"
  and Hfixed : "(\<And> m n r . P1 (Vfixed m n r))"
  and Hufixed : "(\<And> m n r . P1 (Vufixed m n r))"
  and Hfbytes : "(\<And> n bs . P1 (Vfbytes n bs))"
  and Hfunction : "(\<And> i j . P1 (Vfunction i j))"
  and Hfarray : "(\<And> t n l . P2 l \<Longrightarrow> P1 (Vfarray t n l))"
  and Htuple : "(\<And> ts vs . P2 vs \<Longrightarrow> P1 (Vtuple ts vs))"
  and Hbytes : "(\<And> bs . P1 (Vbytes bs))"
  and Hstring : "(\<And> s . P1 (Vstring s))"
  and Harray : "(\<And> t vs . P2 vs \<Longrightarrow> P1 (Varray t vs))"
  and Hln : "P2 []"
  and Hlc : "(\<And> t l . P1 t \<Longrightarrow> P2 l \<Longrightarrow>  P2 (t # l))"
shows "P1 v &&& P2 l"
proof-
  {fix v
    have "P1 v \<and> (\<forall> l t n . v = Vfarray t n l \<longrightarrow> P2 l)
               \<and> (\<forall> vs ts . v = Vtuple ts vs \<longrightarrow> P2 vs)
               \<and> (\<forall> vs t . v = Varray t vs \<longrightarrow> P2 vs)"
    proof(induction)
    case (Vuint x1 x2)
    then show ?case using Huint by auto next
    next
      case (Vsint x1 x2)
    then show ?case using Hsint by auto next
    next
      case (Vaddr x)
      then show ?case using Haddr by auto next
    next
      case (Vbool x)
      then show ?case using Hbool by auto next
    next
      case (Vfixed x1 x2 x3a)
      then show ?case using Hfixed by auto next
    next
      case (Vufixed x1 x2 x3a)
      then show ?case using Hufixed by auto next
    next
    case (Vfbytes x1 x2)
      then show ?case using Hfbytes by auto next
    next
      case (Vfunction x1 x2)
      then show ?case using Hfunction by auto next
    next
      case (Vfarray x1 x2 l)
      then show ?case using Hfarray
      proof(induct l)
        case Nil
        then show ?case using Hln Hfarray by auto next
      next
        case (Cons a l)
        hence 0 : "P1 a" by (auto)
        hence 1 : "P2 l" using Cons by(clarsimp; metis)
        show ?case using 0 1 Hlc Hfarray
          by auto
      qed
    next
      case (Vtuple x1 l)
      then show ?case using Htuple
      proof(induct l)
        case Nil
        then show ?case using Hln Htuple by auto next
      next
        case (Cons a l)
        hence 0 : "P1 a" by auto
        have 1 : "P2 l" using Cons by (clarsimp; metis)
        show ?case using 0 1 Hlc Htuple
          by auto
      qed
    next
      case (Vbytes x)
      then show ?case using Hbytes by auto next
    next
      case (Vstring x)
    then show ?case using Hstring by auto next
    next
      case (Varray x1 l)
      then show ?case 
      proof(induct l)
        case Nil
        then show ?case using Hln Harray by auto next
      next
        case (Cons a l)
        hence 0 : "P1 a" by auto
        have 1 : "P2 l" using Cons by (clarsimp; metis)
        then show ?case using 0 1 Hlc Harray
          by auto
      qed
    qed}
  hence Conc' : "P1 v \<and> P2 l" by (cases v; auto)
  show "P1 v" using Conc' by auto
  show "P2 l" using Conc' by auto
qed

(* encoder success implies input validity *)
lemma abi_encode_succeed_valid :
  assumes H : "encode v = Ok full_code" 
  shows "abi_type_valid (abi_get_type v) \<and> abi_value_valid v" using H
  by(induction v arbitrary:full_code; auto simp add:encode_def split:if_splits)

lemma abi_encode_succeed_validt :
      "encode v = Ok full_code \<Longrightarrow>
       abi_type_valid (abi_get_type v)"
  by(simp add:abi_encode_succeed_valid)

lemma abi_encode_succeed_validv :
  assumes H : "encode v = Ok full_code"
  shows "abi_value_valid v" unfolding abi_value_valid.simps
  using abi_encode_succeed_valid[OF H]
  by auto

lemma all_imp_E :
  "(\<And> x . P x \<Longrightarrow> Q x) \<Longrightarrow>
   (\<forall> x . (P x \<longrightarrow> Q x))"
  apply(blast)
  done

(* encode'_tuple_tails and encode'_tuple_heads return a list
   as long as the list of values given as input *)
lemma encode'_tuple_tails_len :
  "\<And> headlen len_total bvs .
      encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
      length vs = length bvs"
proof(induction vs)
  case Nil
  then show ?case by simp
next
  case (Cons a vs)
  then show ?case 
    by(auto split: if_splits sum.splits)
qed

lemma encode'_tuple_heads_len :
  "\<And> bss result .
    encode'_tuple_heads vs bss  = Ok result \<Longrightarrow>
    length vs = length bss"
proof(induction vs)
  case Nil
  then show ?case
    by(cases bss; auto)
next
  case (Cons a vs)
  then show ?case
    by(cases bss; auto  split:if_splits sum.splits prod.splits)
qed

(* if encode'_tuple_tails succeeds, offsets don't overflow sint256 *)
lemma encode'_tuple_tails_correct_overflow :
   "encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
    (v, offset, enc) \<in> set (zip vs bvs) \<Longrightarrow>
     abi_type_isdynamic (abi_get_type v) \<Longrightarrow>
     sint_value_valid 256 offset"
proof(induction vs arbitrary: headlen len_total bvs v offset enc)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    by(auto split:if_split_asm sum.split_asm)
qed

(* auxiliary lemma to show encoder success implies can_encode_as
   if encode'_tuple_tails succeeds, we can find certain values
   such that is_head_and_tail holds
*)

lemma encode'_tuple_tails_correct :
  "\<And> headlen len_total bvs vbvs hds tls.
     encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
     vbvs = (List.zip vs bvs) \<Longrightarrow>
     hds = List.map (\<lambda> (v, (ptr, enc)) .
                        (if (abi_type_isstatic (abi_get_type v)) then v
                            else (Vsint 256 ptr))) vbvs  \<Longrightarrow>
     tls = List.map (\<lambda> (v, (ptr, enc)) . (ptr, v))
                    (List.filter (abi_type_isdynamic o abi_get_type o fst) vbvs) \<Longrightarrow>
     is_head_and_tail vs hds 
                         (List.map (\<lambda> v . if abi_type_isstatic (abi_get_type v) then abi_get_type v
                                              else Tsint 256) vs) (tls)"
proof(induction vs)
  case Nil
  then show ?case
    by(auto intro:iht_nil)
next
  case (Cons a vs)
  then show ?case
  proof (cases "abi_type_isstatic (abi_get_type a)")
    (* static data *)
    case True
    show ?thesis
    proof(cases hds)
      assume Nil' : "hds = []"
      have Nil'_bvs : "bvs = []" using True Cons.prems Nil'
        by(cases bvs; auto)

      show ?thesis using Cons.prems True Nil' Nil'_bvs
        by(auto split:sum.split_asm if_split_asm)
    next
      fix hdh hds'
      assume Cons' : "hds = hdh#hds'"

      obtain res where Res : "encode'_tuple_tails vs headlen len_total = Inl res"
        using Cons.prems Cons' True
        by(cases "encode'_tuple_tails vs headlen len_total"; auto)

      show ?thesis using iht_static[OF Cons.IH[OF Res refl refl refl] refl True] True Cons.prems Res
        by(auto)
    qed
  next

  (* dynamic data *)
    case False
    then show ?thesis
    proof(cases hds)
      assume Nil' : "hds = []"
      have Nil'_bvs : "bvs = []" using False Cons.prems Nil'
        by(cases bvs; auto)

      show ?thesis using Cons.prems False Nil' Nil'_bvs
        by(auto split:sum.split_asm if_split_asm)
    next
      fix hdh hds'
      assume Cons' : "hds = hdh#hds'"

      show ?thesis
      proof(cases bvs)
        assume Nil'' : "bvs = []"

        show ?thesis using Cons.prems False Cons' Nil''
          by(auto)
      next
        fix bvh bvs'
        assume Cons'' : "bvs = bvh # bvs'"
        obtain ph bh where Bvh : "bvh = (ph, bh)" by(cases bvh; auto)

        consider (Vfarray) t n l where "a = Vfarray t n l" |
                 (Vtuple) ts vs where "a = Vtuple ts vs" |
                 (Vbytes) bs where "a = Vbytes bs" |
                 (Vstring) s where "a = Vstring s" |
                 (Varray) t l where "a = Varray t l"
          using False by(cases a; auto)
  
        then show ?thesis
        proof cases
          case Vfarray
          show ?thesis using Cons Vfarray False Cons' Cons'' Bvh
            (* TODO: this oneliner is kind of on the long side. *)
            by(auto simp add: Let_def split:if_split_asm sum.split_asm intro:iht_dynamic)
        next
          case Vtuple
          show ?thesis using Cons Vtuple False Cons' Cons'' Bvh
            by(auto simp add: Let_def split:if_split_asm sum.split_asm intro:iht_dynamic)
        next
          case Vbytes
          show ?thesis using Cons Vbytes False Cons' Cons'' Bvh
            by(auto simp add: Let_def split:if_split_asm sum.split_asm intro:iht_dynamic)
        next
          case Vstring
          show ?thesis using Cons Vstring False Cons' Cons'' Bvh
            by(auto simp add: Let_def split:if_split_asm sum.split_asm intro:iht_dynamic)
        next
          case Varray
          show ?thesis using Cons Varray False Cons' Cons'' Bvh
            by(auto simp add: Let_def split:if_split_asm sum.split_asm intro:iht_dynamic)
        qed
      qed
    qed
  qed
qed

lemma funext :
  "
      (\<forall> a . f a = g a) \<Longrightarrow> (\<lambda> a . f a) = (\<lambda> a . g a)"
proof(auto)
qed

(* Encoding correctness of static tuples
   - first element of pair returned by encode'_tuple_heads *)
lemma encode'_tuple_heads_correct1 :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vsint 256 ptr) vs bvs) \<Longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tsint 256) vs) \<Longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs))) \<Longrightarrow>
   abi_value_valid (Vtuple ys xs) \<Longrightarrow>
   abi_type_isstatic (Ttuple ys) \<Longrightarrow>
   encode'_tuple_heads vs bvs = Ok (heads_code, tails_code) \<Longrightarrow>
   encode_static (Vtuple (ys) (xs)) = Ok (heads_code)" 
proof(induction  arbitrary: bvs heads_code tails_code  rule:AbiEncodeSpec.is_head_and_tail.induct)
  case iht_nil
  then show ?case by(cases bvs; auto)
next
  case (iht_static xs ys ts tails x v)
  then show ?case
  proof(cases bvs)
    case Nil thus ?thesis using iht_static by auto
  next
    case (Cons bvh bvt)
    obtain ph bh where Bvh : "bvh = (ph, bh)" by(cases bvh; auto)
    obtain head where Hd_code : "encode_static x = Ok head"
      using iht_static  Cons Bvh by(cases "encode_static x"; auto)
    then obtain heads' tails' where Hdt'_code : "encode'_tuple_heads xs bvt = Inl (heads', tails')"
      using iht_static  Cons Bvh  by(cases "encode'_tuple_heads xs bvt"; auto)
    then show ?thesis using Cons Bvh iht_static.IH[of bvt heads' tails'] 
        iht_static.prems
      by(auto simp add:tuple_value_valid_aux_def split:sum.split_asm)
  qed
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case 

  proof(cases bvs)
    case Nil thus ?thesis using iht_dynamic by auto
  next
    case (Cons bvh bvt)
    obtain ph bh where Bvh : "bvh = (ph, bh)" by(cases bvh; auto)
    then obtain heads' tails' where Hdt'_code : "encode'_tuple_heads xs bvt = Inl (heads', tails')"
      using iht_dynamic  Cons Bvh  by(cases "encode'_tuple_heads xs bvt"; auto)
    then show ?thesis using Cons Bvh iht_dynamic.prems
          iht_dynamic.IH[of bvt heads' tails'] iht_dynamic.hyps
      by(auto simp add:tuple_value_valid_aux_def  split: sum.split_asm)
  qed
qed



(* Encoding correctness of static tuples
   - second element of pair returned by encode'_tuple_heads *)
lemma encode'_tuple_heads_correct2 [rule_format] :
  "
 is_head_and_tail vs xs ys tails \<Longrightarrow>
   xs = (map2 (\<lambda>v a. case a of (ptr, enc) \<Rightarrow> if \<not> abi_type_isdynamic (abi_get_type v) then v else Vsint 256 ptr) vs bvs) \<Longrightarrow>
   ys = (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then abi_get_type v else Tsint 256) vs) \<Longrightarrow>
   tails = (map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip vs bvs)))  \<Longrightarrow>
   encode'_tuple_tails vs (0::int) (heads_len) = Ok bvs \<Longrightarrow>
   abi_value_valid (Vtuple ys xs) \<Longrightarrow>
   encode'_tuple_heads vs bvs = Ok (heads_code, tails_code) \<Longrightarrow>
   (ac, ab) \<in> set tails \<Longrightarrow>
   abi_type_isdynamic (abi_get_type ab) \<Longrightarrow>
   (\<exists> ab_code pre post . encode' ab = Ok ab_code \<and> 
       tails_code = pre @ ab_code @ post \<and>
       ac = (heads_len) + int (length pre))"
proof(induction arbitrary: bvs heads_len heads_code tails_code ac ab rule:AbiEncodeSpec.is_head_and_tail.induct)
  case iht_nil
  then show ?case by auto
next
  case (iht_static xs ys ts tails x v)
  show ?case
  proof(cases bvs)
    case Nil
    then show ?thesis using iht_static by auto
  next
    case (Cons bvh bvt)
    obtain ph bh where Bvh : "bvh = (ph, bh)" by(cases bvh; auto)
    obtain head where Hd_code : "encode_static x = Ok head"
      using iht_static.prems iht_static.hyps Cons Bvh by (cases "encode_static x"; auto)
    then obtain heads' tails' where Hdt'_code : "encode'_tuple_heads xs bvt = Inl (heads', tails')"
      using iht_static.prems iht_static.hyps  Cons Bvh  by(cases "encode'_tuple_heads xs bvt"; auto)

    hence Tenc : "encode'_tuple_tails xs 0 (heads_len) = Ok bvt"
      using Cons iht_static.prems iht_static.hyps Bvh Hd_code
      by(cases "encode'_tuple_tails xs 0 (heads_len)"; auto)


    have Tl_present :
      "(ac, ab) \<in> set tails"
      using Cons iht_static.prems iht_static.hyps
      by(auto)

    then show ?thesis using Cons iht_static.prems iht_static.hyps  Hd_code Hdt'_code Tenc
      iht_static.IH[of bvt heads_len heads' tails_code ac ab] Tl_present
      by(auto simp add:tuple_value_valid_aux_def)
  qed
next
  case (iht_dynamic xs ys ts tails x ptr)
  show ?case
  proof(cases bvs)
    case Nil
    then show ?thesis using iht_dynamic by auto
  next
    case (Cons bvh bvt)
    obtain ph bh where Bvh : "bvh = (ph, bh)" by(cases bvh; auto)

    then obtain heads' tails' where Hdt'_code : "encode'_tuple_heads xs bvt = Inl (heads', tails')"
      using iht_dynamic.prems iht_dynamic.hyps  Cons  by(cases "encode'_tuple_heads xs bvt"; auto)

    obtain enc' where Enc': "encode' x = Ok enc'"
      using iht_dynamic.prems iht_dynamic.hyps  Cons
      by(cases "encode' x";  auto)

  then obtain tails'' where T''_code : 
        "encode'_tuple_tails xs 0 (heads_len + int (length enc')) = Ok tails''"
      using iht_dynamic.prems iht_dynamic.hyps  Cons Enc' Hdt'_code
      by(cases "encode'_tuple_tails xs 0 (heads_len + int (length enc'))"; auto)

    show ?thesis

    proof(cases "ac = ptr \<and> ab = x")
      case True
      then show ?thesis using iht_dynamic.prems iht_dynamic.hyps 
        by(auto split:if_split_asm split:sum.split_asm) 
    next
      case False
      hence Tl_present :
        "(ac, ab) \<in> set tails"
      using iht_dynamic.prems iht_dynamic.hyps
                              Cons Bvh 
      by(auto)

    obtain ab_code pre post where
      "encode' ab = Ok ab_code \<and> tails' = pre @ ab_code @ post \<and> ac = heads_len + int (length enc') + int (length pre)"
      using iht_dynamic.prems iht_dynamic.hyps
                              iht_dynamic.IH[of bvt "heads_len + (length enc')" 
                                                heads' tails' ac ab]
                              Cons Bvh Hdt'_code T''_code Enc' Tl_present
        by(auto simp add: Let_def tuple_value_valid_aux_def 
                        split:if_split_asm)

      then show ?thesis using iht_dynamic.prems iht_dynamic.hyps
                              Cons Bvh Hdt'_code T''_code Enc' Tl_present
        by(auto simp add: Let_def tuple_value_valid_aux_def 
                        split:if_split_asm
                        intro: exI[of _ "enc' @ pre"])
    qed
  qed
qed

lemma those_err_success :
  "those_err xs = Ok out \<Longrightarrow>
    x \<in> set xs \<Longrightarrow> 
  (\<exists> x' . x = Ok x')"
proof(induction xs arbitrary: x out)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case
    by(cases a; auto split:sum.split_asm)
qed

definition err_force :: "'x orerror \<Rightarrow> 'x" where
"err_force xe =
  (case xe of Ok x \<Rightarrow> x)"

lemma those_err_map :
  "those_err xs = Ok out \<Longrightarrow>
   out = map err_force xs"
proof(induction xs arbitrary: out)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case 
    by(cases a; auto simp add:err_force_def split:sum.split_asm)
qed

lemma foldl_plus [rule_format]:
  "x + (foldl ((+) :: int \<Rightarrow> int \<Rightarrow> int) (i :: int) xs) =
   foldl ((+) :: int \<Rightarrow> int \<Rightarrow> int) (x + i) xs"
proof(induction xs arbitrary: x i)
  case Nil
  then show ?case by auto
next
  case (Cons a xs)
  then show ?case by(auto simp add:add.assoc)
qed

(* correctness of static size calculation  *)
lemma encode_static_size':
  shows
  "(\<And> code. 
     encode_static v = Ok code \<Longrightarrow>
     abi_value_valid v \<Longrightarrow>
     abi_static_size (abi_get_type v) = length code)" and
   "(\<And> t n v code  .
      v = (Vfarray t n vs) \<Longrightarrow>
      encode_static v = Ok code \<Longrightarrow>
      abi_value_valid v \<Longrightarrow>
      n * (abi_static_size t) = length code)" and
    "(\<And> ts v code  .
        v = (Vtuple ts vs) \<Longrightarrow>
        encode_static v = Ok code \<Longrightarrow>
        abi_value_valid v \<Longrightarrow>
        foldl (+) 0 (map abi_static_size ts) = length code)"
proof(induction v and vs rule: my_abi_value_induct)
case (1 n i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (2 n i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (3 i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (4 b)
  then show ?case
    by (cases b; auto simp: word_rsplit_def bin_rsplit_len; fail)
next
  case (5 m n r)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (6 m n r)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  case (7 n bs)
  obtain d rem where Drem : "divmod_nat (min (length bs) n) 32 = (d, rem)"
    by (cases "divmod_nat (min (length bs) n) 32"; auto)

  then show ?case
  proof(cases rem)
    case 0
    then show ?thesis using 7 Drem Nat.dvd_imp_le[of 32 "length code"]
      by(auto simp add:fbytes_value_valid_def divmod_nat_def) 
  next
    case (Suc n')
    then obtain bsh and bst where Bs : "bs = bsh # bst"
      using 7 Drem
      unfolding fbytes_value_valid_def divmod_nat_def
      by (cases bs; auto)
    hence "length bst = n'" using 7 Drem Suc
      by(cases "length bst = 31";
         auto simp add: divmod_nat_def fbytes_value_valid_def)
    thus ?thesis using 7 Drem Suc Bs
      by(auto simp add: divmod_nat_def fbytes_value_valid_def)
  qed
next
  case (8 i j)
  then show ?case
    by(auto simp add: divmod_nat_def function_value_valid_def
        word_rsplit_def bin_rsplit_len)
next
  case (9 t n l)
  then show ?case by auto
next
  case (10 ts vs)
  then show ?case by auto
next
  case (11 bs)
  then show ?case by auto
next
  case (12 s)
  then show ?case by auto
next
  case (13 t vs)
  then show ?case by auto
next
  case 14
  { case 1 then show ?case 
      by (simp add:farray_value_valid_aux_def tuple_value_valid_aux_def) 
  next
    case 2 then show ?case
      by (simp add:farray_value_valid_aux_def tuple_value_valid_aux_def)
  }
next
  case (15 h l)
  { case 1 
    then obtain henc where Henc : "encode_static h = Ok henc"
      by (cases "encode_static h"; auto)

    then obtain lenc where Lenc : "those_err (map encode_static l) = Ok lenc"
      using 1 
      by (cases "those_err (map encode_static l)"; auto)

    show ?case using Henc Lenc
                    1 "15.IH"(1)[of henc] 
                    "15.IH"(2)[of "Vfarray t (length l) l"
                                  "abi_get_type h" "length l" "concat lenc"]
      by(auto simp add:farray_value_valid_aux_def int_distrib split:sum.split_asm)

  next
    case 2  
    then obtain henc where Henc : "encode_static h = Ok henc"
      by (cases "encode_static h"; auto)

    then obtain lenc where Lenc : "those_err (map encode_static l) = Ok lenc"
      using 2
      by (cases "those_err (map encode_static l)"; auto)

    obtain th tt where T : "ts = th # tt" using 2 by (auto simp add:tuple_value_valid_aux_def)

    then show ?case using Henc Lenc
                    2 "15.IH"(1)[of henc] 
                    "15.IH"(3)[of "Vtuple tt l" tt "concat lenc"]
                    foldl_plus[of "int (length henc)" 0
                                  "map (abi_static_size \<circ> abi_get_type) l"]
      by(auto simp add:tuple_value_valid_aux_def  split:sum.split_asm)
  }
qed



lemma encode_static_size :
"encode_static v = Ok code \<Longrightarrow>
 abi_value_valid v \<Longrightarrow>
 abi_static_size (abi_get_type v) = length code"
  using encode_static_size' by auto


lemma encode_tuple_heads_headslength:
  "encode'_tuple_heads l tp = Ok (hds, tls) \<Longrightarrow>
      list_all abi_value_valid l \<Longrightarrow>
      length hds = heads_length l"
proof(induction l arbitrary: tp hds tls)
  case Nil
  then show ?case 
    by(cases tp; auto)
next
  case (Cons lh lt)
  then obtain offset bs tpt where Tp : "tp = (offset, bs) # tpt" by(cases tp; auto)
  
  then show ?case 
  proof(cases "abi_type_isstatic (abi_get_type lh)")
    case True
    then show ?thesis using Cons Tp encode_static_size[of lh]
      by(auto split:sum.split_asm)
  next
    case False
    then show ?thesis using Cons Tp
      by(auto simp add: word_rsplit_def bin_rsplit_len split:sum.split_asm)
  qed
qed

lemma map2_map_fst' :
  "\<And> f l' . 
    length l = length l' \<Longrightarrow>
    map f l = map2 (\<lambda> x _ . f x) l l'"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case by (cases l'; auto)
qed

(* some convenience lemmas about is_head_and_tail *)
lemma is_head_and_tail_vs_elem :
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 x \<in> set xs \<Longrightarrow>
 abi_type_isdynamic (abi_get_type x) \<Longrightarrow>
   (\<exists> offset . (offset, x) \<in> set tails \<and>
            (Vsint 256 offset \<in> set ys))"
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


lemma is_head_and_tail_vs_elem_static :
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 x \<in> set xs \<Longrightarrow>
 abi_type_isstatic (abi_get_type x) \<Longrightarrow>
   (x \<in> set ys )"
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

lemma is_head_and_tail_tails_elem :
assumes Hht : "is_head_and_tail xs ys ts tails"
assumes Hin : "(offset, x) \<in> set tails"
shows "abi_type_isdynamic (abi_get_type x) \<and>
       Vsint 256 offset \<in> set ys \<and>
       x \<in> set xs " using Hht Hin
by(induction rule:is_head_and_tail.induct; auto)

lemma is_head_and_tail_heads_elem :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   h \<in> set heads \<Longrightarrow>
   abi_type_isstatic (abi_get_type h)"
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

lemma is_head_and_tail_head_types_elem :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   ht \<in> set head_types \<Longrightarrow>
   abi_type_isstatic (ht)"
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

lemma is_head_and_tail_heads_elem' :
  "is_head_and_tail vs heads head_types tails \<Longrightarrow>
   x \<in> set heads \<Longrightarrow>
   x \<notin> set vs \<Longrightarrow>
   (\<exists> offset x' . (offset, x') \<in> set tails \<and>
      abi_type_isdynamic (abi_get_type x') \<and>
      x = Vsint 256 offset)"
by(induction rule:is_head_and_tail.induct; auto)



lemma abi_encode_succeed :
  "encode v = Ok code \<Longrightarrow>
   can_encode_as v (pre @ code @ post) (int (length pre))"
proof(induction v arbitrary: code pre post;
     (unfold encode_def; auto split:if_split_asm intro:Estatic; fail)?)

  (* TODO: see if we can reduce the amount of copy-paste in these goals *)
  case (Vfarray t n l)
  then show ?case
  proof(cases "abi_type_isstatic t")
    case True
    then show ?thesis using Vfarray by(auto simp add:encode_def split:if_split_asm intro:Estatic)
  next
    case False

    then have V : "abi_type_valid t"  "farray_value_valid_aux t n l"
                  "list_all abi_value_valid_aux l"
      using Vfarray unfolding encode_def
      by(auto split:if_split_asm)

    then obtain bvs where Bvs : "encode'_tuple_tails l 0 (heads_length l) = Inl bvs"
      using Vfarray False unfolding encode_def
      by(auto split:sum.split_asm)

    then obtain heads tails where Hhts : "encode'_tuple_heads l bvs = Inl (heads, tails)"
      using Vfarray V False unfolding encode_def
      by(auto split:sum.split_asm)

    obtain iht_h where Iht_h : "iht_h = 
      (map2 (\<lambda>v (ptr, enc). 
          if \<not> abi_type_isdynamic (abi_get_type v) then v else Vsint 256 ptr) l bvs)" by auto

    obtain iht_typ where Iht_typ : "iht_typ =
      (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) 
                   then abi_get_type v else Tsint 256) l)" by auto

    obtain iht_tl where Iht_tl : "iht_tl = 
      (map (\<lambda>(v, ptr, enc). (ptr, v))
                  (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l bvs)))" by auto

    have Iht :
      "is_head_and_tail l iht_h iht_typ iht_tl"
      using False Vfarray V Bvs 
            encode'_tuple_tails_correct[OF Bvs refl refl refl]
            unfolding encode_def Iht_h Iht_typ Iht_tl
            by(auto simp add:encode_def)

    have Valid_Aux : "abi_value_valid_aux (Vtuple iht_typ iht_h)"
      unfolding abi_value_valid_aux.simps
    proof(rule conjI)
      show "tuple_value_valid_aux iht_typ iht_h"
        using V map2_map_fst'[OF encode'_tuple_tails_len[OF Bvs],
                              of "(\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then 
                                       abi_get_type v else Tsint 256)"]
        unfolding Iht_typ Iht_h farray_value_valid_aux_def tuple_value_valid_aux_def
        by(auto)
    next
      show "list_all abi_value_valid_aux iht_h" 
        unfolding farray_value_valid_aux_def tuple_value_valid_aux_def
                  list_all_iff Ball_def
      proof(rule allI; rule impI)
        fix x
        assume Hx : "x \<in> set iht_h"
  
        have Xstatic : "abi_type_isstatic (abi_get_type x)"
          using is_head_and_tail_heads_elem[OF Iht Hx] by auto
  
        have Xbad : "\<And> ptr enc . \<not> (x, ptr, enc) \<in> set (zip l bvs)"
        proof
          fix ptr enc
          assume Xcontr : "(x, ptr, enc) \<in> set (zip l bvs)"
  
          show False using set_zip_leftD[OF Xcontr]
            using V False Xstatic Hx
            unfolding Iht_h set_map farray_value_valid_aux_def list_all_iff
            by(auto)
        qed
  
        then obtain x' ptr enc where InSet : "(x', ptr, enc) \<in> set (zip l bvs)" 
          and Xptr : "x = Vsint 256 ptr"
          using V False Xstatic Hx
          unfolding Iht_h set_map farray_value_valid_aux_def list_all_iff
          by(auto split: if_split_asm)
  
  
        hence X't1 : "abi_get_type x' = t"
          using V Bvs False Xstatic Hx set_zip_leftD[OF InSet]
          unfolding Iht_h farray_value_valid_aux_def list_all_iff
          by(auto )
  
        hence X't2 : "abi_type_isdynamic (abi_get_type x')"
          using V False unfolding Iht_h farray_value_valid_aux_def list_all_iff by(auto)
  
        hence Ptr_valid : "sint_value_valid 256 ptr"
          using encode'_tuple_tails_correct_overflow[OF Bvs InSet X't2] by auto  
  
        show "abi_value_valid_aux x"
          using encode'_tuple_tails_correct_overflow[OF Bvs InSet X't2] Xptr by(auto)
      qed
    qed

    have Valid : "abi_value_valid (Vtuple iht_typ iht_h)"
          unfolding abi_value_valid.simps
    proof(rule conjI)
      show "abi_type_valid (abi_get_type (Vtuple iht_typ iht_h))"
        unfolding Iht_typ Iht_h
        using V
        by(auto simp add: farray_value_valid_aux_def tuple_value_valid_aux_def list_all_iff)
    next
      show "abi_value_valid_aux (Vtuple iht_typ iht_h)" using Valid_Aux by auto
    qed

    have Static :"abi_type_isstatic (abi_get_type (Vtuple iht_typ iht_h))" unfolding Iht_typ
      by(auto simp add:list_ex_iff)

    have Code_ht : "code = heads @ tails" using Bvs Hhts Vfarray.prems False
      by(auto simp add:encode_def split:if_split_asm sum.split_asm)

    show ?thesis
    proof(rule Efarray_dyn[OF _ _ Iht])
      show "abi_value_valid (Vfarray t n l)" using V by auto
    next
      show "abi_type_isdynamic t" using False by auto
    next
      show "can_encode_as (Vtuple iht_typ iht_h) (pre @ code @ post) (int (length pre))"
        unfolding Code_ht append_assoc
      proof(rule Estatic[OF Static Valid])
        show "encode_static (Vtuple iht_typ iht_h) = Ok heads"
          using encode'_tuple_heads_correct1[OF Iht Iht_h Iht_typ Iht_tl Valid _ Hhts] Static Vfarray
          by(auto)
      qed
    next
      fix offset v
      assume Hv : "(offset, v) \<in> set iht_tl"
      have Hvl : "v \<in> set l" using is_head_and_tail_tails_elem[OF Iht Hv] by auto
      have Hv_dyn : "abi_type_isdynamic (abi_get_type v)"
        using is_head_and_tail_tails_elem[OF Iht Hv] by auto

      obtain ab_code pre' post' where
        Abc1 :"encode' v = Ok ab_code" and Abc2 : "tails = pre' @ ab_code @ post'"
              and Abc3 : "offset = heads_length l + int (length pre')"
        using encode'_tuple_heads_correct2[OF Iht Iht_h Iht_typ Iht_tl Bvs Valid Hhts Hv Hv_dyn]
        by auto

      have Vt_valid : "abi_type_valid (abi_get_type v)" using V Hvl
        unfolding list_all_iff farray_value_valid_aux_def
        by(auto)

      have Vvalid : "abi_value_valid_aux v" using V Hvl
        unfolding list_all_iff farray_value_valid_aux_def
        by(auto)

      have Abc1' : "encode v = Ok ab_code" using Hv_dyn Abc1 Vvalid Vt_valid
        by(auto simp add:encode_def)

      have Lvalid' : "list_all abi_value_valid l" using V
        unfolding list_all_iff farray_value_valid_aux_def
        by(auto)

      show "can_encode_as v (pre @ code @ post) (offset + int (length pre))"
        using
        Vfarray.IH[OF Hvl Abc1', of "pre @ heads @ pre'" "post'@post"] 
        encode_tuple_heads_headslength[OF Hhts]
        Code_ht Abc2 Abc3 Lvalid'
        by(auto simp add:add.assoc add.commute)
    qed
  qed
next
  case (Vtuple ts l)
  then show ?case
  proof(cases "abi_type_isstatic (Ttuple ts)")
    case True
    then show ?thesis 
      using Vtuple
      by(auto simp add:encode_def split:if_split_asm intro:Estatic)
  next
    case False

    then have V : "list_all abi_type_valid ts"  "tuple_value_valid_aux ts l"
                  "list_all abi_value_valid_aux l"
      using Vtuple unfolding encode_def
      by(auto split:if_split_asm)

    then obtain bvs where Bvs : "encode'_tuple_tails l 0 (heads_length l) = Inl bvs"
      using Vtuple False unfolding encode_def
      by(auto split:sum.split_asm)

    then obtain heads tails where Hhts : "encode'_tuple_heads l bvs = Inl (heads, tails)"
      using Vtuple V False unfolding encode_def
      by(auto split:sum.split_asm)

    obtain iht_h where Iht_h : "iht_h = 
      (map2 (\<lambda>v (ptr, enc). 
          if \<not> abi_type_isdynamic (abi_get_type v) then v else Vsint 256 ptr) l bvs)" by auto

    obtain iht_typ where Iht_typ : "iht_typ =
      (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) 
                   then abi_get_type v else Tsint 256) l)" by auto

    obtain iht_tl where Iht_tl : "iht_tl = 
      (map (\<lambda>(v, ptr, enc). (ptr, v))
                  (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l bvs)))" by auto

    have Iht :
      "is_head_and_tail l iht_h iht_typ iht_tl"
      using False Vtuple V Bvs 
            encode'_tuple_tails_correct[OF Bvs refl refl refl]
            unfolding encode_def Iht_h Iht_typ Iht_tl
            by(auto simp add:encode_def)

    have Valid_Aux : "abi_value_valid_aux (Vtuple iht_typ iht_h)"
      unfolding abi_value_valid_aux.simps
    proof(rule conjI)
      show "tuple_value_valid_aux iht_typ iht_h"
        using V map2_map_fst'[OF encode'_tuple_tails_len[OF Bvs],
                              of "(\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then 
                                       abi_get_type v else Tsint 256)"]
        unfolding Iht_typ Iht_h farray_value_valid_aux_def tuple_value_valid_aux_def
        by(auto)
    next
      show "list_all abi_value_valid_aux iht_h" 
        unfolding farray_value_valid_aux_def tuple_value_valid_aux_def
                  list_all_iff Ball_def
      proof(rule allI; rule impI)
        fix x
        assume Hx : "x \<in> set iht_h"
  
        have Xstatic : "abi_type_isstatic (abi_get_type x)"
          using is_head_and_tail_heads_elem[OF Iht Hx] by auto


        show "abi_value_valid_aux x"
        proof(cases "x \<in> set l")
          assume True' : "x \<in> set l"
          thus ?thesis using V unfolding list_all_iff by(auto)
        next
          assume False' : "x \<notin> set l"

          obtain x' offset where
            X'_in : "(offset, x') \<in> set iht_tl" and
            X'_dyn : "abi_type_isdynamic (abi_get_type x')" and
            X_offset : "x = Vsint 256 offset"
            using is_head_and_tail_heads_elem'[OF Iht Hx False'] by auto

          obtain enc where Conc' : "(x', offset, enc) \<in> set (zip l bvs)"
            using X'_in unfolding Iht_tl by(auto)
  
          show "abi_value_valid_aux x"
            using encode'_tuple_tails_correct_overflow[OF Bvs Conc' X'_dyn] X_offset by(auto)
      qed
    qed
  qed
    have Valid : "abi_value_valid (Vtuple iht_typ iht_h)"
          unfolding abi_value_valid.simps
    proof(rule conjI)
      show "abi_type_valid (abi_get_type (Vtuple iht_typ iht_h))"
        unfolding Iht_typ Iht_h
        using V
        by(auto simp add: farray_value_valid_aux_def tuple_value_valid_aux_def list_all_iff)
    next
      show "abi_value_valid_aux (Vtuple iht_typ iht_h)" using Valid_Aux by auto
    qed

    have Static :"abi_type_isstatic (abi_get_type (Vtuple iht_typ iht_h))" unfolding Iht_typ
      by(auto simp add:list_ex_iff)

    have Code_ht : "code = heads @ tails" using Bvs Hhts Vtuple.prems False
      by(auto simp add:encode_def split:if_split_asm sum.split_asm)

    obtain t where T_in : "t \<in> set ts" and T_dyn : "abi_type_isdynamic t"
      using False unfolding abi_type_isstatic.simps abi_type_isdynamic.simps list_ex_iff
      by auto

    show ?thesis
    proof(rule Etuple_dyn[OF _ T_in T_dyn Iht])
      show "abi_value_valid (Vtuple ts l)" using V by auto
    next
      show "can_encode_as (Vtuple iht_typ iht_h) (pre @ code @ post) (int (length pre))"
        unfolding Code_ht append_assoc
      proof(rule Estatic[OF Static Valid])
        show "encode_static (Vtuple iht_typ iht_h) = Ok heads"
          using encode'_tuple_heads_correct1[OF Iht Iht_h Iht_typ Iht_tl Valid _ Hhts] Static Vtuple
          by(auto)
      qed
    next
      fix offset v
      assume Hv : "(offset, v) \<in> set iht_tl"
      have Hvl : "v \<in> set l" using is_head_and_tail_tails_elem[OF Iht Hv] by auto
      have Hv_dyn : "abi_type_isdynamic (abi_get_type v)"
        using is_head_and_tail_tails_elem[OF Iht Hv] by auto

      obtain ab_code pre' post' where
        Abc1 :"encode' v = Ok ab_code" and Abc2 : "tails = pre' @ ab_code @ post'"
              and Abc3 : "offset = heads_length l + int (length pre')"
        using encode'_tuple_heads_correct2[OF Iht Iht_h Iht_typ Iht_tl Bvs Valid Hhts Hv Hv_dyn]
        by auto

      have Vt_valid : "abi_type_valid (abi_get_type v)" using V Hvl
        unfolding list_all_iff tuple_value_valid_aux_def
        by(auto)

      have Vvalid : "abi_value_valid_aux v" using V Hvl
        unfolding list_all_iff tuple_value_valid_aux_def
        by(auto)

      have Abc1' : "encode v = Ok ab_code" using Hv_dyn Abc1 Vvalid Vt_valid
        by(auto simp add:encode_def)

      have Lvalid' : "list_all abi_value_valid l" using V
        unfolding list_all_iff tuple_value_valid_aux_def
        by(auto)

      show "can_encode_as v (pre @ code @ post) (offset + int (length pre))"
        using
        Vtuple.IH[OF Hvl Abc1', of "pre @ heads @ pre'" "post'@post"] 
        encode_tuple_heads_headslength[OF Hhts]
        Code_ht Abc2 Abc3 Lvalid'
        by(auto simp add:add.assoc add.commute)
    qed
  qed

next
  case (Vbytes bs)
  have V : "abi_value_valid (Vbytes bs)" using Vbytes unfolding encode_def
    by(auto split:if_split_asm)

  have Hcode : "code = encode_int (length bs) @ pad_bytes bs" using Vbytes unfolding encode_def
    by(auto split:if_split_asm)
  show ?case unfolding Hcode append_assoc
  proof(rule Ebytes)
    show "abi_value_valid (Vbytes bs)" using Vbytes unfolding encode_def
      by(auto split:if_split_asm)
  next
    show "pad_bytes bs = pad_bytes bs" by auto
  next
    show "length (encode_int (int (length bs))) = 32"
      by(auto simp add: word_rsplit_def bin_rsplit_len)
  next
    show "can_encode_as (Vuint 256 (int (length bs)))
     (pre @ encode_int (int (length bs)) @ pad_bytes bs @ post) (int (length pre))"
    proof(rule Estatic)
      show "abi_type_isstatic (abi_get_type (Vuint 256 (int (length bs))))" by auto
    next
      show "abi_value_valid (Vuint 256 (int (length bs)))" using V
        by(auto simp add:bytes_value_valid_def)
    next
      show "encode_static (Vuint 256 (int (length bs))) = Ok (encode_int (int (length bs)))"
        by auto
    qed
  qed
next
  case (Vstring s)
  have V : "abi_value_valid (Vstring s)" using Vstring unfolding encode_def
    by(auto split:if_split_asm)

  have Hcode : "code = encode_int (length (string_to_bytes s)) @ 
                       pad_bytes (string_to_bytes s)"
    using Vstring unfolding encode_def
    by(auto simp add:string_value_valid_def Let_def split:if_split_asm)

  show ?case
  proof(rule Estring[OF V refl])
    show "can_encode_as (Vbytes (string_to_bytes s)) (pre @ code @ post) (int (length pre))"
      unfolding Hcode append_assoc
    proof(rule Ebytes)
      show "abi_value_valid (Vbytes (string_to_bytes s))" using V
        by(auto simp add: string_value_valid_def bytes_value_valid_def)
    next
      show "pad_bytes (string_to_bytes s) = pad_bytes (string_to_bytes s)" by auto
    next
      show "length (encode_int (int (length (string_to_bytes s)))) = 32" using V
        by(auto simp add: word_rsplit_def bin_rsplit_len)
    next
      show "can_encode_as (Vuint 256 (int (length (string_to_bytes s))))
                          (pre @ encode_int (int (length (string_to_bytes s))) @ 
                           pad_bytes (string_to_bytes s) @ post)
                          (int (length pre))"
      proof(rule Estatic)
        show "abi_type_isstatic (abi_get_type (Vuint 256 (int (length (string_to_bytes s)))))"
          by auto
      next
        show "abi_value_valid (Vuint 256 (int (length (string_to_bytes s))))" using V
          by (auto simp add:string_value_valid_def)
      next
        show "encode_static (Vuint 256 (int (length (string_to_bytes s)))) = 
              Ok (encode_int (int (length (string_to_bytes s))))" by auto
      qed
    qed
  qed
next
  case (Varray t l)
  then have V : "abi_type_valid t"  "array_value_valid_aux t l"
                "list_all abi_value_valid_aux l"
  using Varray unfolding encode_def
  by(auto split:if_split_asm)
  
  then obtain bvs where Bvs : "encode'_tuple_tails l 0 (heads_length l) = Inl bvs"
    using Varray unfolding encode_def
    by(auto split:sum.split_asm)
  
  then obtain heads tails where Hhts : "encode'_tuple_heads l bvs = Inl (heads, tails)"
    using Varray V unfolding encode_def
    by(auto split:sum.split_asm)
  
  obtain iht_h where Iht_h : "iht_h = 
    (map2 (\<lambda>v (ptr, enc). 
        if \<not> abi_type_isdynamic (abi_get_type v) then v else Vsint 256 ptr) l bvs)" by auto

  obtain iht_typ where Iht_typ : "iht_typ =
    (map (\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) 
                 then abi_get_type v else Tsint 256) l)" by auto

  obtain iht_tl where Iht_tl : "iht_tl = 
    (map (\<lambda>(v, ptr, enc). (ptr, v))
                (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip l bvs)))" by auto

  have Iht :
    "is_head_and_tail l iht_h iht_typ iht_tl"
    using Varray V Bvs 
          encode'_tuple_tails_correct[OF Bvs refl refl refl]
          unfolding encode_def Iht_h Iht_typ Iht_tl
          by(auto simp add:encode_def)

  have Valid_Aux : "abi_value_valid_aux (Vtuple iht_typ iht_h)"
    unfolding abi_value_valid_aux.simps
  proof(rule conjI)
    show "tuple_value_valid_aux iht_typ iht_h"
      using V map2_map_fst'[OF encode'_tuple_tails_len[OF Bvs],
                            of "(\<lambda>v. if \<not> abi_type_isdynamic (abi_get_type v) then 
                                     abi_get_type v else Tsint 256)"]
      unfolding Iht_typ Iht_h farray_value_valid_aux_def tuple_value_valid_aux_def
      by(auto)
  next
    show "list_all abi_value_valid_aux iht_h" 
      unfolding farray_value_valid_aux_def tuple_value_valid_aux_def
                list_all_iff Ball_def
    proof(rule allI; rule impI)
      fix x
      assume Hx : "x \<in> set iht_h"

      show "abi_value_valid_aux x"
      proof(cases "x \<in> set l")
        assume True' : "x \<in> set l"
        thus ?thesis using V unfolding list_all_iff by(auto)
      next
        assume False' : "x \<notin> set l"

        obtain x' offset where
          X'_in : "(offset, x') \<in> set iht_tl" and
          X'_dyn : "abi_type_isdynamic (abi_get_type x')" and
          X_offset : "x = Vsint 256 offset"
          using is_head_and_tail_heads_elem'[OF Iht Hx False'] by auto

        obtain enc where Conc' : "(x', offset, enc) \<in> set (zip l bvs)"
          using X'_in unfolding Iht_tl by(auto)

        show "abi_value_valid_aux x"
          using encode'_tuple_tails_correct_overflow[OF Bvs Conc' X'_dyn] X_offset by(auto)
      qed
    qed
  qed

  have Valid : "abi_value_valid (Vtuple iht_typ iht_h)"
        unfolding abi_value_valid.simps
  proof(rule conjI)
    show "abi_type_valid (abi_get_type (Vtuple iht_typ iht_h))"
      unfolding Iht_typ Iht_h
      using V
      by(auto simp add: array_value_valid_aux_def tuple_value_valid_aux_def list_all_iff)
  next
    show "abi_value_valid_aux (Vtuple iht_typ iht_h)" using Valid_Aux by auto
  qed

  have Static :"abi_type_isstatic (abi_get_type (Vtuple iht_typ iht_h))" unfolding Iht_typ
    by(auto simp add:list_ex_iff)

  have Code_ht : "code = encode_int (int (length l)) @ heads @ tails"
    using Bvs Hhts Varray.prems
    by(auto simp add:encode_def split:if_split_asm sum.split_asm)

  have EncLen : "int (length (encode_int (int (length l)))) = 32"
    by(auto simp: word_rsplit_def bin_rsplit_len)


  show ?case
  proof(rule Earray[OF _ Iht])
    show "abi_value_valid (Varray t l)" using V by auto
  next
    show "can_encode_as (Vuint 256 (int (length l)))
            (pre @ code @ post) (int (length pre))" using V
      unfolding Code_ht append_assoc array_value_valid_aux_def
      by(auto intro: Estatic)
  next
    have Conc' : "encode_static (Vtuple iht_typ iht_h) = Ok heads"
      using encode'_tuple_heads_correct1[OF Iht Iht_h Iht_typ Iht_tl Valid _ Hhts] Static Varray
      by(auto)


    show "can_encode_as (Vtuple iht_typ iht_h) (pre @ code @ post) (int (length pre) + 32)"
      using Estatic[OF Static Valid Conc', of "pre@encode_int (int (length l))"  ]
            EncLen
      unfolding Code_ht append_assoc
      by(auto simp add: add.assoc add.commute)
  next
    fix offset v
    assume Hv : "(offset, v) \<in> set iht_tl"
    have Hvl : "v \<in> set l" using is_head_and_tail_tails_elem[OF Iht Hv] by auto
    have Hv_dyn : "abi_type_isdynamic (abi_get_type v)"
      using is_head_and_tail_tails_elem[OF Iht Hv] by auto

    obtain ab_code pre' post' where
      Abc1 :"encode' v = Ok ab_code" and Abc2 : "tails = pre' @ ab_code @ post'"
            and Abc3 : "offset = heads_length l + int (length pre')"
      using encode'_tuple_heads_correct2[OF Iht Iht_h Iht_typ Iht_tl Bvs Valid Hhts Hv Hv_dyn]
      by auto

    have Vt_valid : "abi_type_valid (abi_get_type v)" using V Hvl
      unfolding list_all_iff array_value_valid_aux_def
      by(auto)

    have Vvalid : "abi_value_valid_aux v" using V Hvl
      unfolding list_all_iff
      by(auto)

    have Abc1' : "encode v = Ok ab_code" using Hv_dyn Abc1 Vvalid Vt_valid
      by(auto simp add:encode_def)

    have Lvalid' : "list_all abi_value_valid l" using V
      unfolding list_all_iff array_value_valid_aux_def
      by(auto)

    have Rearrange : 
      "(int (length pre) + (32 + (heads_length l + int (length pre')))) =
       (heads_length l + int (length pre') + int (length pre) + 32)" by arith
    

    show "can_encode_as v (pre @ code @ post) (offset + int (length pre) + 32)"
      using
      Varray.IH[OF Hvl Abc1', of "pre @ encode_int (int (length l)) @ heads @ pre'" "post'@post"] 
      encode_tuple_heads_headslength[OF Hhts]
      Code_ht Abc2 Abc3 Lvalid' EncLen
      by(auto simp add:Rearrange)
  qed
qed

(* begin masking out rest of file *)
(*
lemma encode_tuple_heads_fail [rule_format]:
  "\<forall> bss err.
    encode'_tuple_heads vs bss = Err err \<longrightarrow>
    length vs = length bss \<longrightarrow>
    (\<exists> v err' . v \<in> set vs \<and> encode' v = Err err')"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(clarsimp)
    apply(case_tac bss; clarsimp)
    apply(drule_tac x = list in spec) apply(clarsimp)
    apply(case_tac "abi_type_isdynamic (abi_get_type a)"; clarsimp)
     apply(simp split:if_split_asm sum.split_asm prod.splits)

     apply(clarsimp)
     apply(case_tac "abi_type_isdynamic (abi_get_type v)"; clarsimp)
      apply(rule_tac x = v in exI) apply(clarsimp)
     apply(rule_tac x = v in exI) apply(clarsimp)

    apply(case_tac "encode_static a"; clarsimp)
    apply(case_tac "encode'_tuple_heads vs list"; clarsimp)
     apply(rule_tac x = v in exI) apply(clarsimp)
     apply(rule_tac conjI) apply(clarsimp)
     apply(clarsimp)

     apply(rule_tac x = a in exI) apply(clarsimp)
    done
qed

(* induction on is_head_and_tail? *)
(*
lemma encode_tuple_tails_overflow_fail [rule_format]:
  "\<forall> vs headlen len_total err v .
     encode'_tuple_tails (vs) headlen len_total = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> v . v \<in> set vs \<and> 
     "
  sorry
*)

(* the problem here is that our spec doesn't care if we can't encode
   (empty) offsets for heads that are too big. but our implementation does *)
(* need to generalize for different arguments of encode_tuple_tails *)


(* lemma for tails will be similar, but we also need to take into
   account the possibility that the encoding fails because the
   length is too large *)


lemma is_head_and_tail_vs_elem [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> x . x \<in> set xs \<longrightarrow>
 abi_type_isdynamic (abi_get_type x) \<longrightarrow>
   (\<exists> offset . (offset, x) \<in> set tails \<and>
      (Vsint 256 offset \<in> set ys)))"
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


lemma is_head_and_tail_vs_elem_static [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> x . x \<in> set xs \<longrightarrow>
 abi_type_isstatic (abi_get_type x) \<longrightarrow>
   (x \<in> set ys ))"
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

lemma those_err_forall [rule_format]:
  "\<forall> l' x . those_err l = Ok l' \<longrightarrow>
      x \<in> set l \<longrightarrow>
      (\<exists> x' . x = Ok x' \<and> x' \<in> set l')"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac a; clarsimp)
    apply(case_tac "those_err l"; clarsimp)
    apply(auto)
    done
qed

lemma map_elem [rule_format]:
  "\<forall> x f .
    x \<in> set l \<longrightarrow>
    f x \<in> set (map f l)"
proof(induction l; auto)
qed

lemma can_encode_as_tuple_split [rule_format]:
"can_encode_as v full_code offset \<Longrightarrow>
 (\<forall> ts vs vd .  v = (Vtuple ts vs) \<longrightarrow>
    vd \<in> set vs \<longrightarrow>
    (\<exists> coded offsetd . can_encode_as vd coded offsetd))"
proof(induction rule: can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case
    apply(clarsimp)
    apply(simp split:sum.splits)
    apply(drule_tac x = "encode_static vd" in those_err_forall)
     apply(simp)
    apply(clarsimp)
    apply(cut_tac v = vd in can_encode_as.Estatic)
       apply(simp add:list_all_iff list_ex_iff)
    apply(rotate_tac 1)
       apply(simp add:tuple_value_valid_aux_def)
    apply(frule_tac x = vd and f = abi_get_type in map_elem)
       apply(drule_tac x = "abi_get_type vd" in bspec) apply(simp) apply(simp)
       apply(simp add:list_all_iff list_ex_iff)
apply(drule_tac x = vd in bspec)
       apply(simp add:list_all_iff list_ex_iff)

      apply(simp add:tuple_value_valid_aux_def)
    apply(frule_tac x = vd and f = abi_get_type in map_elem)
       apply(drule_tac x = "abi_get_type vd" in bspec) apply(simp) apply(simp)
       apply(simp add:tuple_value_valid_aux_def)
    apply(simp add:list_all_iff list_ex_iff)

    apply(auto)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def)
    apply(case_tac "abi_type_isdynamic (abi_get_type vd)")
     apply(clarsimp)
     apply(frule_tac x = vd in is_head_and_tail_vs_elem)
       apply(simp) apply(simp)
     apply(clarsimp)
     apply(atomize)apply(drule_tac x = offset in spec) apply(rotate_tac -1)
     apply(drule_tac x = vd in spec) apply(clarsimp)
     apply(fastforce)

     apply(frule_tac x = vd in is_head_and_tail_vs_elem_static)
       apply(simp) apply(simp)
    apply(clarsimp)
    done
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Ebytes l pre post count code)
  then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed

lemma can_encode_as_start [rule_format]:
"can_encode_as v full_code offset \<Longrightarrow>
 (offset \<le> int (length (full_code)))"
proof(induction rule:can_encode_as.inducts)
case (Estatic v pre post code)
  then show ?case 
    apply(auto)
    done
next
case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case apply(auto)
    done
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case 
    apply(auto)
    done
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Ebytes l pre post count code)
then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed
  

(* --- *)


lemma is_head_and_tail_tails_elem [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> offset x . (offset, x) \<in> set tails \<longrightarrow>
 (abi_type_isdynamic (abi_get_type x)  \<and> 
  Vsint 256 offset \<in> set ys \<and>
      x \<in> set xs))"
proof(induction rule:is_head_and_tail.induct; auto)
qed

(*
lemma is_head_and_tail_elem''' [rule_format]:
"is_head_and_tail xs ys ts tails \<Longrightarrow>
 (\<forall> y . y  \<in> set ys \<longrightarrow>
    (abi_type_isstatic (abi_get_type y)))"
  sorry
*)

(*
lemma encode_tuple_tails_shift [rule_format]:
  "\<forall> headlen len_total x bss .
    encode'_tuple_tails vs headlen len_total = Ok bss \<longrightarrow>
    encode'_tuple_tails vs headlen (len_total + x) = Ok (map (\<lambda> (offset, bs) . (offset + x, bs)) bss)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
    apply(clarify)
    apply(simp only:encode'_tuple_tails.simps)
    apply(case_tac "abi_type_isstatic (abi_get_type a) ") apply(clarsimp)
    apply(clarsimp)
qed
*)

(*
lemma encode_tuple_tails_overflow_fail' [rule_format]:
  "
     (\<forall> err vs1 vs2 code .
      vs = vs1 @vs2 \<longrightarrow>
     encode'_tuple_tails vs1 0 (heads_length vs) = Ok code \<longrightarrow>
     encode'_tuple_tails (vs2) 0 (foldr (+) (map (\<lambda> (offset, code') . int (length (code'))) code) (heads_length vs) ) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> offset v . (offset, v) \<in> set tls \<and>
     \<not> (uint_value_valid 256 offset)))
     "
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case 
    apply(
qed
*)

(* generalization: compare to heads_length vs, subtract
   this formulation isn't quite right because it doesn't
   invoke heads_length *)
(*
lemma encode_tuple_tails_overflow_fail' [rule_format] :
"
     is_head_and_tail vs hds bvs tls \<Longrightarrow>
     (\<forall> err headlen .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     (\<exists> offset v . (offset - headlen, v) \<in> set tls \<and> offset > headlen \<and>
     \<not> (uint_value_valid 256 (offset - headlen))))
     "
*)
(*

  case iht_nil
  then show ?case
    apply(clarsimp)
    done
next
  case (iht_static xs ys ts tails x v)
  then show ?case 
    apply(clarsimp)
    apply(simp split:if_splits sum.splits)
    done
next
  case (iht_dynamic xs ys ts tails x ptr)
  then show ?case
    apply(clarsimp)
    apply(simp split:if_splits sum.splits)
      apply(frule_tac encode_tuple_tails_correct)
         apply(simp)
        apply(simp)
       apply(simp)

      defer



      apply(clarsimp)
      apply(drule_tac x = err in spec)
    apply(drule_tac x = "headlen + int (length (x1))" in spec)
      apply(clarsimp)
      apply(rule_tac x = "offset - ( int (length (x1)))" in exI)
      apply(clarsimp)
      apply(rule_tac conjI)
       apply(rule_tac x = v in exI)
       apply(clarsimp) 
       apply(subgoal_tac "offset - (headlen + int (length x1)) = offset - int (length x1) - headlen") apply(clarsimp)
       apply(arith)
      apply(clarsimp)
       apply(subgoal_tac "offset - (headlen + int (length x1)) = offset - int (length x1) - headlen") apply(clarsimp)
       apply(arith)

     apply(clarsimp)

    apply(drule_tac x = x in spec) apply(clarsimp)

  (* deferred goal *)

    apply(case_tac x; clarsimp)
    apply(simp split:sum.splits prod.splits)
    
(* need lemma about determinism of is_head_and_tail *)
    apply(clarsimp)
    apply(frule_tac encode'_tuple_tails_correct_overflow)
    apply(rule_tac x = "ptr + headlen" in exI) apply(clarsimp)
    apply(rule_tac conjI) apply(rule_tac x = x in exI) apply(clarsimp)
    apply(subgoal_tac
"(map (\<lambda>(v::abi_value, ptr::int, enc::8 word list). (ptr, v)) (filter (abi_type_isdynamic \<circ> abi_get_type \<circ> fst) (zip xs x1a)))
=
tails")

    apply(clarsimp)
    sorry
qed
*)

lemma encode_static_correct_converse [rule_format] :
  "can_encode_as v full_code start \<Longrightarrow>
    (\<forall> pre code post . full_code = pre @ code @ post \<longrightarrow>
       start = length pre \<longrightarrow>
     abi_type_isstatic (abi_get_type v) \<longrightarrow>
       abi_static_size (abi_get_type v) = length code \<longrightarrow>
     (abi_value_valid v \<and> encode_static v = Ok code))"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case 
    apply(clarsimp)
    apply(frule_tac encode_static_size)
     apply(simp)
    apply(simp)
    done
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    apply(simp add:tuple_value_valid_aux_def)
    apply(simp add:list_ex_iff)
    done
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    done
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case
    apply(clarsimp)
    done
next
  case (Ebytes l pre post count code)
  then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed

lemma encode_correct_converse_valid [rule_format] :
  "can_encode_as v full_code start \<Longrightarrow>
     (abi_value_valid v)"
proof(induction rule:can_encode_as.induct)
  case (Estatic v pre post code)
  then show ?case by auto
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case by auto
next
  case (Efarray_dyn t n vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Earray t vs heads head_types tails start full_code)
  then show ?case by auto
next
  case (Ebytes l pre post count code)
  then show ?case by auto
next
  case (Estring full_code s l start)
  then show ?case by auto
qed


(*
lemma can_encode_as_inv_static [rule_format] :
  "abi_type_isstatic (abi_get_type v) \<longrightarrow>
   can_encode_as v full_code l \<longrightarrow>
   (\<exists> 
*)

definition list_nonneg :: "int list \<Rightarrow> bool" where
"list_nonneg l = list_all (\<lambda> x . 0 \<le> x) l"

lemma list_nonneg_sum [rule_format]:
  " list_nonneg l \<longrightarrow>
         0 \<le> list_sum l"
proof(induction l)
  case Nil
  then show ?case 
    apply(simp add: list_nonneg_def list_sum_def)
    done
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(simp add:list_nonneg_def list_sum_def) apply(clarsimp)
    apply(cut_tac x = a and i = 0 and xs = l in foldl_plus) apply(clarsimp)
    done
qed


lemma elem_lt_list_sum [rule_format] :
  "\<forall> x . x \<in> set l \<longrightarrow>
     list_nonneg l \<longrightarrow>
      x \<le> list_sum l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp) apply(simp add:list_sum_def list_nonneg_def)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(cut_tac l = l in list_nonneg_sum) apply(simp add:list_nonneg_def)
     apply(simp add:list_sum_def)
     apply(cut_tac i = 0 and x = a and xs = l in foldl_plus) apply(clarsimp)

    apply(clarsimp)
     apply(cut_tac l = l in list_nonneg_sum) apply(simp add:list_nonneg_def)
     apply(simp add:list_sum_def)
    apply(cut_tac i = 0 and x = a and xs = l in foldl_plus) apply(clarsimp)
    apply(drule_tac x = x in spec) apply(clarsimp)
    done
qed

lemma abi_static_size_nonneg :
  "0 \<le> abi_static_size v"
  apply(induction v; clarsimp)
  apply(atomize)
  apply(cut_tac l = "map abi_static_size x" in list_nonneg_sum)
   apply(simp add:list_nonneg_def) apply(simp add:list_all_iff)

  apply(simp add:list_sum_def)
  done

lemma abi_dynamic_size_bound_nonneg :
  "0 \<le> abi_dynamic_size_bound v"
  apply(induction v; clarsimp)

  (* farray *)
    apply(atomize)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(simp add: abi_static_size_nonneg)
    apply(clarsimp)

    apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x3a)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x3a \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)

(* tuple *)
    apply(atomize)
    apply(rule_tac conjI)
    apply(clarsimp)
  apply(cut_tac l = "map abi_static_size x1" in list_nonneg_sum)
  apply(simp add:list_nonneg_def)
  apply(simp add:list_all_iff)
    apply(simp add: abi_static_size_nonneg)
    apply(simp add:list_sum_def)

  apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x2)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x2 \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)

(* array *)
      apply(atomize)
  apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x2)")
     apply(drule_tac list_nonneg_sum) apply(arith)

     apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff)
    apply(clarsimp)
  apply(case_tac " x \<in> (\<lambda>x::abi_value. abi_static_size (abi_get_type x)) ` (set x2 \<inter> {x::abi_value. \<not> abi_type_isdynamic (abi_get_type x)})")
     apply(clarsimp)
     apply(drule_tac x = xa in spec) apply(clarsimp)
    apply(clarsimp)
  apply(drule_tac x = xa in spec) apply(clarsimp)
  done

lemma zero_leq_nat:
  "0 \<le> int (n :: nat)"
proof(induction n; auto)
qed

lemma oneplus_times :
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow>
  (1 + a :: int) * (b :: int) =
   b + a * b"
  apply(simp add:int_distrib)
  done

lemma mythin :
  "P \<Longrightarrow> True"
proof(auto)
qed

(*

    encode'_tuple_heads (?vs::abi_value list) (?bss::(int \<times> 8 word list) list) =
    Ok (?result::8 word list \<times> 8 word list) \<Longrightarrow>
    length ?vs = length ?bss


*)


lemma encode_tuple_heads_len2 [rule_format] :
  "\<forall> bss heads tails . encode'_tuple_heads vs bss = Ok (heads, tails) \<longrightarrow>
    length tails = list_sum (map (\<lambda> (i, l) . length l) bss)"
proof(induction vs)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(case_tac bss)
     apply(auto simp add:list_sum_def)
    done
next
  case (Cons a vs)
  then show ?case
    apply(clarsimp)
    apply(case_tac bss; clarsimp)
    apply(simp split:if_splits sum.splits prod.splits)

     apply(clarsimp)
     apply(drule_tac x = list in spec) apply(clarsimp)
     apply(simp add:list_sum_def)
     apply(simp add:foldl_plus)

    apply(clarsimp)
apply(drule_tac x = list in spec) apply(clarsimp)
     apply(simp add:list_sum_def)
     apply(simp add:foldl_plus)
    done
qed

lemma encode_tuple_tails_len_sum [rule_format]:
  "\<And> headlen len_total bvs headlen' len_total' bvs'.
      encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
      encode'_tuple_tails vs headlen' len_total' = Ok bvs' \<Longrightarrow>
      (map (\<lambda> (i, l) . length l) bvs) = (map (\<lambda> (i, l) . length l) bvs')"
proof(induction vs)
  case Nil
  then show ?case 
    apply(auto)
    done
next
  case (Cons a vs)
  then show ?case 
    apply(clarsimp)
    apply(case_tac "\<not> abi_type_isdynamic (abi_get_type a)")
     apply(clarsimp)
     apply(case_tac "encode'_tuple_tails vs headlen len_total")
      apply(simp del:encode'_tuple_tails.simps)
     apply(case_tac "encode'_tuple_tails vs headlen' len_total'")
       apply(simp del:encode'_tuple_tails.simps)
       apply(atomize)
       apply(drule_tac x = headlen in spec) apply(drule_tac x = len_total in spec)
       apply(drule_tac x = aa in spec)
apply(drule_tac x = headlen' in spec) apply(drule_tac x = len_total' in spec)
       apply(drule_tac x =aaa in spec)
       apply(clarsimp)

      apply(clarsimp)
     apply(clarsimp)

    apply(clarsimp)
    apply(split sum.splits; clarsimp)
    apply(case_tac "encode'_tuple_tails vs headlen (len_total + int (length x1))"; clarsimp)
    apply(case_tac "encode'_tuple_tails vs headlen' (len_total' + int (length x1))"; clarsimp)
    apply(simp split:if_split_asm)

    apply(atomize)
    apply(clarify)
  apply(drule_tac x = headlen in spec) apply(drule_tac x = "len_total + int (length x1)" in spec)
       apply(drule_tac x = aa in spec)
apply(drule_tac x = headlen' in spec) apply(drule_tac x ="len_total' + int (length x1)" in spec)
    apply(drule_tac x =aaa in spec)
    apply(clarify)
    apply(rotate_tac 4)
    apply(drule_tac mythin)
    apply(clarsimp)
    done
qed

lemma encode'_tuple_tails_dyn_success [rule_format]:
  " \<forall> x heads_length bvs v . encode'_tuple_tails l x heads_length = Ok bvs \<longrightarrow>
      v \<in> set l \<longrightarrow>
      abi_type_isdynamic (abi_get_type v) \<longrightarrow>
      (\<exists> code . encode' v = Ok code)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(rule_tac conjI)

     apply(clarsimp)
     apply(simp split:sum.split_asm)

    apply(clarsimp)
    apply(case_tac "abi_type_isdynamic (abi_get_type a)"; clarsimp)
     apply(simp split:sum.split_asm if_split_asm)
     apply(clarsimp)
    apply(subgoal_tac "(\<exists>(x::int) (heads_length::int) bvs::(int \<times> 8 word list) list. encode'_tuple_tails l x heads_length = Ok bvs)")
      apply(clarsimp)
     apply(fastforce)

     apply(simp split:sum.split_asm if_split_asm)
    apply(subgoal_tac "(\<exists>(x::int) (heads_length::int) bvs::(int \<times> 8 word list) list. encode'_tuple_tails l x heads_length = Ok bvs)")
      apply(clarsimp)
     apply(fastforce)
    done
qed

lemma encode'_tuple_heads_static_success [rule_format]:
  "\<forall> bvs hs ts v . encode'_tuple_heads l bvs = Ok (hs, ts) \<longrightarrow>
     v \<in> set l \<longrightarrow>
     abi_type_isstatic (abi_get_type v) \<longrightarrow>
     (\<exists> code . encode' v = Ok code)"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(case_tac bvs; clarsimp)
     apply(simp split:sum.splits)

     apply(case_tac bvs; clarsimp)
    apply(simp split:if_split_asm)
     apply(simp split:sum.splits prod.splits)
     apply(clarsimp)
    apply(subgoal_tac "(\<exists>(bvs::(int \<times> 8 word list) list) (hs::8 word list) ts::8 word list. encode'_tuple_heads l bvs = Ok (hs, ts))")
      apply(clarsimp)
     apply(rule_tac x = list in exI) apply(clarsimp)

    apply(simp split:sum.splits prod.splits)
    apply(subgoal_tac "(\<exists>(bvs::(int \<times> 8 word list) list) (hs::8 word list) ts::8 word list. encode'_tuple_heads l bvs = Ok (hs, ts))")
     apply(clarsimp)
    apply(clarsimp)
     apply(rule_tac x = list in exI) apply(clarsimp)
    done
qed


lemma heads_length_nonneg :
  "0 \<le> heads_length l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    apply(clarsimp)
    apply(simp add: Let_def split:if_split_asm)
    apply(simp add:abi_static_size_nonneg)
    done
qed

lemma encode_tuple_tails_dyn_offset [rule_format]:
  "\<forall> heads_length bvs heads_length' . encode'_tuple_tails l (0 :: int) heads_length = Ok bvs \<longrightarrow>
       0 \<le> heads_length' \<longrightarrow>
       heads_length' \<le> heads_length \<longrightarrow>
       (\<exists> bvs' . encode'_tuple_tails l (0 :: int) heads_length' = Ok bvs')"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(auto)
     apply(simp split:sum.splits)
     apply(clarsimp)
      apply(drule_tac x = heads_length in spec) apply(clarsimp)
     apply(drule_tac x = heads_length' in spec) apply(clarsimp)

 
     apply(simp split:sum.splits)
    apply(simp split:if_split_asm)
    apply(clarsimp)
    apply(rule_tac conjI) apply(clarsimp)
    apply(simp add:sint_value_valid_def)

    apply(clarsimp)
    apply(drule_tac x = "heads_lengtha + int (length x1b)" in spec)
    apply(clarsimp)
    apply(drule_tac x = "heads_length' + int (length x1b)" in spec)
    apply(clarsimp)
    done
qed

lemma encode_tuple_heads_static [rule_format] :
  "\<forall> bvs hs ts . encode'_tuple_heads l bvs = Ok (hs, ts) \<longrightarrow>
       list_all (abi_type_isstatic o abi_get_type) l \<longrightarrow>
        (\<exists> hss . those_err (map encode_static l) = Ok hss \<and>
           concat hss = hs)"
proof(induction l)
  case Nil
  then show ?case
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    done
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    apply(simp split:sum.splits prod.splits)
    apply(clarsimp)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(drule_tac x = list in spec) apply(drule_tac x = x1b in spec) apply(clarsimp)

    apply(clarsimp)
    done
qed

lemma encode_tuple_tails_static [rule_format] :
  "\<forall> x heads_length bvs offset v. encode'_tuple_tails l x heads_length  = Ok bvs \<longrightarrow>
       list_all (abi_type_isstatic o abi_get_type) l \<longrightarrow>
       list_all (\<lambda> bv . \<exists> offset . bv = (offset, [])) bvs"
proof(induction l)
  case Nil
  then show ?case
    apply(clarsimp)
    done
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac bvs; clarsimp)
    apply(simp split:sum.splits prod.splits)
    done
qed

lemma abi_dynamic_size_bound_static [rule_format] :
  "abi_type_isstatic (abi_get_type v) \<Longrightarrow>
   abi_dynamic_size_bound v = abi_static_size (abi_get_type v)"
  apply(simp)
  done

lemma abi_dynamic_size_bound_static_list [rule_format] :
"\<forall> i . list_sum (map abi_dynamic_size_bound l) = i \<longrightarrow>
       list_all (abi_type_isstatic o abi_get_type) l \<longrightarrow>
       list_sum (map (abi_static_size o abi_get_type) l) = i"
proof(induction l)
case Nil
then show ?case by auto
next
case (Cons a l)
  then show ?case
    apply(simp del:abi_dynamic_size_bound.simps)
    apply(clarsimp)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac v = a in abi_dynamic_size_bound_static)
     apply(simp add:list_sum_def)
    apply(rotate_tac -1)
    apply(drule_tac sym)
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac i = 0 and x = "(abi_static_size (abi_get_type a))"
and xs = "(map (\<lambda>a::abi_value. abi_static_size (abi_get_type a)) l)" in foldl_plus)

    apply(cut_tac i = 0 and x = "(abi_static_size (abi_get_type a))"
and xs = "(map abi_dynamic_size_bound l)" in foldl_plus)
    apply(rotate_tac -1) apply(drule_tac sym)
    apply(clarsimp)
    done
qed

lemma list_sum_zero :
  "list_all (\<lambda> x . x = 0) l \<Longrightarrow>
   list_sum l = 0"
proof(induction l)
  case Nil
  then show ?case by (auto simp add:list_sum_def)
next
  case (Cons a l)
  then show ?case by (auto simp add:list_sum_def)
qed

        

(* need the more general induction principle *)
lemma abi_dynamic_size_bound_correct' [rule_format] :
"
(\<forall> bound code . encode v = Ok code \<longrightarrow>
    abi_dynamic_size_bound v = bound \<longrightarrow>           
            abi_value_valid v \<longrightarrow>
            length code \<le> bound) \<and>
    (
     (\<forall> t n v code  .
        v = (Vfarray t n vs) \<longrightarrow>
        encode v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        (length code \<le> n * 32 + list_sum (map abi_dynamic_size_bound vs))) \<and>
      ( \<forall> ts v code  .
        v = (Vtuple ts vs) \<longrightarrow>
        encode v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        length code \<le> (length vs * 32) + list_sum (map abi_dynamic_size_bound vs)) \<and>
      ( \<forall> t v code  .
        v = (Varray t vs) \<longrightarrow>
        encode v = Ok code \<longrightarrow>
        abi_value_valid v \<longrightarrow>
        length code \<le> 32 + (length vs * 32) + list_sum (map abi_dynamic_size_bound vs))
      )"

proof(induction rule: my_abi_value_induct)
  case (1 n i)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (2 n i)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (3 i)
  then show ?case
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (4 b)
  then show ?case
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (5 m n r)
  then show ?case
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (6 m n r)
  then show ?case
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (7 n bs)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  case (8 i j)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(auto)
    done
next
  (* Vfarray *)
  case (9 t n l)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps abi_dynamic_size_bound.simps)

    (* static *)
    apply(case_tac "abi_type_isstatic t") apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
     apply(clarsimp) apply(clarsimp)

    (* dynamic *)
    apply(clarsimp)
    apply(simp split:sum.splits prod.splits del:encode_static.simps abi_dynamic_size_bound.simps)
    apply(clarify)
    apply(rotate_tac -4) apply(drule_tac mythin) apply(drule_tac mythin)
    apply(drule_tac x = t in spec)
    apply(drule_tac x = n in spec)
    apply(drule_tac x = "x1b @ x2" in spec) apply(clarsimp)
    done
next
    (* Vtuple *)
  case (10 ts vs)
  then show ?case 
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps abi_dynamic_size_bound.simps)

    (* static *)
    apply(case_tac "\<not> list_ex abi_type_isdynamic ts") apply(clarify)
    apply(simp add:encode_def del:encode_static.simps)
    apply(drule_tac encode_static_size)
      apply(clarsimp) apply(clarsimp)


    (* dynamic *)
    apply(clarsimp)
    apply(simp split:sum.splits prod.splits del:encode_static.simps abi_dynamic_size_bound.simps)
    apply(clarify)
    apply(rotate_tac -3) apply(drule_tac mythin) apply(rotate_tac -3) apply(drule_tac mythin)
    apply(drule_tac x = ts in spec) 
    apply(drule_tac x = "x1b @ x2" in spec) apply(clarsimp)
    done
next
  (* Vbytes *)
  case (11 bs)
  then show ?case
    apply(clarsimp) apply(simp add:bytes_value_valid_def encode_def uint_value_valid_def split:prod.splits)
    apply(clarsimp)
apply(case_tac x2; clarsimp)
    apply(simp add:word_rsplit_def bin_rsplit_len)
        apply(simp add:word_rsplit_def bin_rsplit_len)
    done
next
  (* Vstring *)
  case (12 s)
  then show ?case 
    apply(clarsimp) apply(simp add:Let_def string_value_valid_def bytes_value_valid_def encode_def uint_value_valid_def split:prod.splits)
    apply(case_tac x2; clarsimp)
     apply(simp add:word_rsplit_def bin_rsplit_len)
apply(simp add:word_rsplit_def bin_rsplit_len)
    done
next
  (* Varray *)
  case (13 t vs)
  then show ?case
    apply(clarify)
    apply(simp add:encode_def del:encode_static.simps abi_dynamic_size_bound.simps)
    apply(simp split:sum.splits prod.splits del:encode_static.simps abi_dynamic_size_bound.simps)
    apply(clarify)
    apply(rotate_tac 1) apply(drule_tac mythin) apply(drule_tac mythin)
    apply(drule_tac x = t in spec) 
    apply(drule_tac x = "word_rsplit (word_of_int (int (length vs)) :: 256 word) @ x1b @ x2" in spec) apply(clarsimp)
    done
next
  case 14
  then show ?case 
    apply(auto simp add:encode_def farray_value_valid_aux_def array_value_valid_aux_def list_sum_def)
    apply(simp add:word_rsplit_def bin_rsplit_len)
    done
next
  case (15 t l)
  then show ?case 

(*---------------
    farray 
--------------- *)
    apply(rule_tac conjI)
     apply(clarify)
     apply(rotate_tac  2) apply(drule_tac mythin) apply(drule_tac mythin)
(*     apply(frule_tac pre = "[]" and post = "[]" in abi_encode_succeed) apply(rotate_tac -1)
    apply(drule_tac encode_correct_converse_valid) *)
    apply(simp del:abi_dynamic_size_bound.simps add:encode_def)
     apply(clarify)
     apply(case_tac "\<not> abi_type_isdynamic ta")
      apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
    apply(clarify)
      apply(drule_tac x = "nat (abi_dynamic_size_bound t)" in spec)
      apply(case_tac "encode_static t")
       apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
       apply(clarify)
    apply(drule_tac x = a in spec)
       apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)

       apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def)
       apply(clarify)
       apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t") 
        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def)

    
        apply(drule_tac x = "(abi_get_type t)" in spec)
        apply(simp del:abi_dynamic_size_bound.simps)
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
        apply(cut_tac i = 0 and x = "(abi_dynamic_size_bound t)" and xs = "(map abi_dynamic_size_bound l)" in foldl_plus)
        apply(simp)

       apply(simp add:abi_dynamic_size_bound_nonneg del:abi_dynamic_size_bound.simps)

      apply(clarsimp)

(* here is where we first hit two subgoals *)
        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

     apply(case_tac "sint_value_valid (256::nat) ((32::int) + heads_length l)")
        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)
      apply(clarify)
      apply(drule_tac x = "abi_get_type t" in spec)
      apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)
        apply(clarify)

        apply(drule_tac x = "nat (abi_dynamic_size_bound t)" in spec)
      apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)
        apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t")
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

(* idea: need to relate (x1g, x2b) to (x1f, x2a) *)
    apply(frule_tac bvs = x1c in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1b in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac a = x1c in encode_tuple_heads_headslength)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
         apply(frule_tac a = x1b in encode_tuple_heads_headslength)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

         apply(drule_tac encode_tuple_heads_len2)
         apply(drule_tac encode_tuple_heads_len2)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac
headlen' = 0
and len_total' = "heads_length l"
and bvs' = x1b
in encode_tuple_tails_len_sum)

    apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac x = "(abi_dynamic_size_bound t)"
and i = 0
and xs = "(map abi_dynamic_size_bound l)"
in foldl_plus)
    apply(rotate_tac -1)
    apply(drule_tac sym)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"int (length (word_rsplit (word_of_int ((32::int) + heads_length l) :: 256 word) :: 8 word list)) = 32")
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1c) =
foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1b)")


           apply(arith)


    apply(cut_tac f= int and g = "(\<lambda>(i::int, y::8 word list). length y)"
and list = x1c in List.map.compositionality)


          apply(fastforce)

         apply(simp add:word_rsplit_def bin_rsplit_len)

        apply(cut_tac v = t in abi_dynamic_size_bound_nonneg) apply(simp)

       apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
       apply(frule_tac encode_tuple_heads_fail)
        apply(frule_tac bvs = x1b in encode_tuple_tails_len) apply(simp)
       apply(clarify)

(* idea: if encode'_tuple_tails succeeds, all dynamic values can encode (encode') *)

       apply(drule_tac v = v in encode'_tuple_tails_dyn_success)
         apply(simp)
        apply(simp add:list_all_iff)
       apply(clarsimp)

      apply(drule_tac heads_length' = "(heads_length l)" in encode_tuple_tails_dyn_offset)
        apply(simp)
        apply(simp add:heads_length_nonneg)
       apply(simp)
      apply(clarsimp)

    apply(clarsimp)

(*---------------
    tuple
--------------- *)

    apply(rule_tac conjI)
     apply(clarify)
     apply(rotate_tac  1)  apply(drule_tac mythin)
     apply(rotate_tac  1)
     apply(drule_tac mythin)
(*     apply(frule_tac pre = "[]" and post = "[]" in abi_encode_succeed) apply(rotate_tac -1)
    apply(drule_tac encode_correct_converse_valid) *)
    apply(simp del:abi_dynamic_size_bound.simps add:encode_def)
     apply(clarify)
     apply(case_tac "list_ex abi_type_isdynamic ts")
      apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
         apply(clarify)
         apply(case_tac " abi_type_isdynamic (abi_get_type t)")
      apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
    apply(case_tac "sint_value_valid (256::nat) ((32::int) + heads_length l)")
    apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)

      apply(drule_tac x = "nat (abi_dynamic_size_bound t)" in spec)
       apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
           apply(clarify)
           apply(case_tac ts; simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits prod.splits)
           apply(simp del:abi_dynamic_size_bound.simps add:encode_def tuple_value_valid_aux_def split:sum.splits)
           apply(clarify)
           apply(case_tac "\<not> list_ex abi_type_isdynamic (map abi_get_type l)")
            apply(simp del:abi_dynamic_size_bound.simps add:encode_def tuple_value_valid_aux_def split:sum.splits)

       apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t") 
        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def)

    
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
              apply(cut_tac i = 0 and x = "(abi_dynamic_size_bound t)" and xs = "(map abi_dynamic_size_bound l)" in foldl_plus)
    apply(rotate_tac -1) apply(drule_tac sym)
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(cut_tac v = "Vtuple (map abi_get_type l) l" and code = "concat x1" in encode_static_size)
       apply(simp add:abi_dynamic_size_bound_nonneg del:abi_dynamic_size_bound.simps)
           apply(simp add:abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)
              apply(frule_tac encode_tuple_heads_static)
             apply(simp add:list_all_iff list_ex_iff abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)

    apply(clarify)
           apply(simp add:abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)

    apply(frule_tac encode_tuple_heads_len2)
              apply(simp add:abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)

    apply(frule_tac bvs = x1b in encode_tuple_tails_static)
             apply(simp add:list_all_iff list_ex_iff abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)
             apply(simp add:list_all_iff list_ex_iff abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)

    apply(subgoal_tac
"list_sum (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1b) = 0")
             apply(simp add:list_all_iff list_ex_iff list_sum_def abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)
    apply(subgoal_tac " int (length (word_rsplit (word_of_int ((32::int) + heads_length l) :: 256 word) :: 8 word list)) = 32")
                apply(simp add:list_all_iff list_ex_iff list_sum_def abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)
        apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t")
                 apply(arith)
                apply(clarify)
    apply(cut_tac v = t in abi_dynamic_size_bound_nonneg) apply(clarify)
    apply(subgoal_tac "abi_static_size (abi_get_type (Vtuple (map abi_get_type l) l)) =
list_sum (map abi_dynamic_size_bound l)")
               apply(simp add:abi_dynamic_size_bound_nonneg list_sum_def del:abi_dynamic_size_bound.simps)
    apply(frule_tac encode_tuple_heads_len)
    apply(frule_tac encode_tuple_heads_len2)
               apply(simp add:abi_dynamic_size_bound_nonneg list_sum_def del:abi_dynamic_size_bound.simps)
    apply(clarify)
      apply(clarsimp)
                apply(simp add:word_rsplit_def bin_rsplit_len)

               apply(simp add:list_sum_def)
               apply(cut_tac l = l in abi_dynamic_size_bound_static_list)
                 apply(simp)
   apply(simp add:list_all_iff list_ex_iff abi_dynamic_size_bound_nonneg tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps)
               apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)
    apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)
              apply(cut_tac l = "(map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1b)" in list_sum_zero)
               apply(simp add:list_all_iff) apply(clarify)
               apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)
               apply(rotate_tac -2) apply(drule_tac x = "(a, b)" in bspec)
               apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)
               apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)
               apply(simp add:list_sum_def del:abi_dynamic_size_bound.simps)

             apply(simp add:abi_dynamic_size_bound_nonneg del:abi_dynamic_size_bound.simps)
            apply(frule_tac encode_tuple_heads_static)
             apply(simp add:list_all_iff list_ex_iff list_sum_def del:abi_dynamic_size_bound.simps)
    apply(clarsimp)


        apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t")
        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

    apply(frule_tac bvs = x1b in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1 in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac a = x1b in encode_tuple_heads_headslength)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
         apply(frule_tac a = x1 in encode_tuple_heads_headslength)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

         apply(drule_tac encode_tuple_heads_len2)
         apply(drule_tac encode_tuple_heads_len2)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac
headlen' = 0
and bvs = x1b
and len_total' = "heads_length l"
and bvs' = x1
in encode_tuple_tails_len_sum)


        apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)
              apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
    apply(cut_tac i = 0 and x = "abi_dynamic_size_bound t"
and xs = "map abi_dynamic_size_bound l" in foldl_plus)
    apply(rotate_tac -1)
              apply(drule_tac sym)
              apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)

    apply(subgoal_tac
"int (length (word_rsplit (word_of_int ((32::int) + heads_length l) :: 256 word) :: 8 word list)) = 32")
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1) =
foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1b)")

           apply(arith)


    apply(cut_tac f= int and g = "(\<lambda>(i::int, y::8 word list). length y)"
and list = x1b in List.map.compositionality)
              apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)

         apply(simp add:word_rsplit_def bin_rsplit_len)

         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
       apply(frule_tac encode_tuple_heads_fail)
        apply(frule_tac bvs = x1 in encode_tuple_tails_len) apply(simp)
       apply(clarify)

(* idea: if encode'_tuple_tails succeeds, all dynamic values can encode (encode') *)
    apply(case_tac "abi_type_isdynamic (abi_get_type v)")
       apply(drule_tac v = v in encode'_tuple_tails_dyn_success)
         apply(simp)
        apply(simp add:list_all_iff)
       apply(clarsimp)

             apply(frule_tac bvs = x1b and v = v in encode'_tuple_heads_static_success)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
              apply(simp)
    apply(clarsimp)

      apply(drule_tac heads_length' = "(heads_length l)" in encode_tuple_tails_dyn_offset)
        apply(simp)
        apply(simp add:heads_length_nonneg)
       apply(simp)
      apply(clarsimp)

    apply(cut_tac v = t in abi_dynamic_size_bound_nonneg)
    apply(clarsimp)

    apply(clarsimp)

         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
         apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
         apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)

         apply(drule_tac x = "nat (abi_dynamic_size_bound t)" in spec)
         apply(drule_tac x = x1a in spec)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
         apply(case_tac "abi_type_valid (abi_get_type t)")
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
          apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t")
           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
           apply(case_tac ts) apply(clarsimp)
    apply(clarify)
           apply(drule_tac x = list in spec)
           apply(case_tac "encode' (Vtuple list l)")
           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def 
tuple_value_valid_aux_def split:sum.splits prod.splits)
            apply(clarify)


    apply(frule_tac bvs = x1c in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)
    apply(frule_tac bvs = x1 in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1c in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)


         apply(frule_tac bss = x1 in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac a = x1c in encode_tuple_heads_headslength)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
         apply(frule_tac a = x1 in encode_tuple_heads_headslength)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

         apply(drule_tac encode_tuple_heads_len2)
         apply(drule_tac encode_tuple_heads_len2)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac
headlen' = 0
and bvs = x1c
and len_total' = "heads_length l"
and bvs' = x1
in encode_tuple_tails_len_sum)
    apply(simp)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def
tuple_value_valid_aux_def split:sum.splits prod.splits)

    apply(subgoal_tac
"foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1) =
foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1c)")
    apply(cut_tac i = 0 and x = "abi_dynamic_size_bound t"
and xs = "map abi_dynamic_size_bound l" in foldl_plus)
    apply(rotate_tac -1)
              apply(drule_tac sym)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)


    apply(cut_tac f= int and g = "(\<lambda>(i::int, y::8 word list). length y)"
and list = x1c in List.map.compositionality)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)

           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def 
tuple_value_valid_aux_def  split:sum.splits prod.splits)
            apply(clarify)
            apply(frule_tac encode_tuple_heads_fail)
        apply(frule_tac bvs = x1 in encode_tuple_tails_len) apply(simp)
            apply(clarify)
    apply(case_tac "abi_type_isstatic (abi_get_type v)")
             apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def )
    apply(frule_tac v = v in encode'_tuple_heads_static_success)
    apply(simp) apply(simp) apply(clarsimp)

            apply(frule_tac v = v in encode'_tuple_tails_dyn_success)
apply(simp) apply(simp) apply(clarsimp)
           apply(frule_tac heads_length' = "heads_length l" in encode_tuple_tails_dyn_offset)
             apply(simp add:heads_length_nonneg) apply(simp) apply(clarsimp)

    apply(cut_tac v = t in abi_dynamic_size_bound_nonneg)
          apply(simp)
         apply(simp split:if_split_asm)
    apply(case_tac ts; clarsimp)
    apply(simp add:tuple_value_valid_aux_def)

        apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
    apply(case_tac "abi_type_isdynamic (abi_get_type t)")
    apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
         apply(case_tac "encode'_tuple_tails l (0::int) ((32::int) + heads_length l + int (length x1a))")

          apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
          apply(frule_tac heads_length' = "32 +heads_length l" in encode_tuple_tails_dyn_offset)
            apply(simp add:heads_length_nonneg) apply(simp) apply(clarify)
          apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
         apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
        apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )
       apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def )

   apply(simp del:abi_dynamic_size_bound.simps encode'.simps add:list_sum_def Let_def split:if_split_asm )
        apply(clarify)
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def Let_def split:if_split_asm sum.splits prod.splits)
       apply(case_tac x1) apply(clarsimp)
       apply(case_tac x1a) apply(clarify)
        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def Let_def split:if_split_asm sum.splits prod.splits)

        apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def Let_def split:if_split_asm sum.splits prod.splits)

          apply(simp del:abi_dynamic_size_bound.simps encode_static.simps encode'.simps add:list_sum_def Let_def split:sum.splits)
     apply(drule_tac encode_static_size)
      apply(simp add:list_all_iff list_ex_iff)
    apply(clarsimp)
     apply(rule_tac conjI)
      apply(case_tac ts; clarsimp) apply(simp add:tuple_value_valid_aux_def)
      apply(simp add:tuple_value_valid_aux_def)
      apply(clarsimp)
    apply(cut_tac i = "foldl (+) (abi_static_size (abi_get_type t)) (map abi_dynamic_size_bound l)" and l = "t#l" in abi_dynamic_size_bound_static_list)
        apply(clarsimp)
        apply(simp add:list_sum_def)
       apply(simp add:list_all_iff list_ex_iff)
      apply(simp add:list_sum_def)
     apply(clarsimp)
      apply(case_tac ts; clarsimp) apply(simp add:tuple_value_valid_aux_def)
     apply(simp add:tuple_value_valid_aux_def)

(*---------------
array
--------------- *)

     apply(clarify) apply(rotate_tac 1)
     apply(drule_tac mythin) apply(drule_tac mythin)
(*     apply(frule_tac pre = "[]" and post = "[]" in abi_encode_succeed) apply(rotate_tac -1)
    apply(drule_tac encode_correct_converse_valid) *)
    apply(simp del:abi_dynamic_size_bound.simps add:encode_def)
     apply(clarify)
     apply(case_tac "\<not> abi_type_isdynamic ta")
      apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
    apply(clarify)
      apply(drule_tac x = "nat (abi_dynamic_size_bound t)" in spec)
      apply(case_tac "encode_static t")
         apply(simp del:abi_dynamic_size_bound.simps add:encode_def Let_def split:sum.splits)
         apply(case_tac "abi_type_isdynamic (abi_get_type t)")
          apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
    apply(case_tac "sint_value_valid (256::nat) ((32::int) + heads_length l)")
          apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)

       apply(clarify)
    apply(drule_tac x = a in spec)
       apply(simp del:abi_dynamic_size_bound.simps add:encode_def split:sum.splits)
    apply(case_tac "abi_type_valid (abi_get_type t)")
       apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:prod.splits)
       apply(clarify)
       apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t") 
             apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def)

    
        apply(drule_tac x = "(abi_get_type t)" in spec)
        apply(simp del:abi_dynamic_size_bound.simps)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
             apply(drule_tac x = "x1d @ x2" in spec)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def)
    apply(cut_tac v = t in abi_dynamic_size_bound_nonneg)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:prod.splits)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def)

          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def)
         apply(clarify)
    apply(case_tac "abi_dynamic_size_bound t")

         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def)
    apply(case_tac "encode'_tuple_heads l x1c ")
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits)
           apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits)

           apply(drule_tac x = "abi_get_type t" in spec)
           apply(case_tac "encode' (Varray (abi_get_type t) l)")
           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits sum.splits)

            apply(drule_tac x = "word_rsplit (word_of_int (int (length l)) :: 256 word) @ x1e @ x2" in spec)
    apply(case_tac "uint_value_valid (256::nat) (int (length l))")
           apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits sum.splits)
             apply(clarify)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits sum.splits)
    apply(subgoal_tac "int (length (word_rsplit (word_of_int ((1::int) + int (length l))))) = 32")
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def split:prod.splits sum.splits)


(* idea: need to relate (x1g, x2b) to (x1f, x2a) *)
    apply(frule_tac bvs = x1c in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

    apply(frule_tac bvs = x1b in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1c in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1b in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac a = x1c in encode_tuple_heads_headslength)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
         apply(frule_tac a = x1b in encode_tuple_heads_headslength)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

         apply(drule_tac encode_tuple_heads_len2)
         apply(drule_tac encode_tuple_heads_len2)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac
headlen' = 0
and len_total' = "heads_length l"
and bvs' = x1b
in encode_tuple_tails_len_sum)

    apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac x = "(abi_dynamic_size_bound t)"
and i = 0
and xs = "(map abi_dynamic_size_bound l)"
in foldl_plus)
    apply(rotate_tac -1)
    apply(drule_tac sym)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"int (length (word_rsplit (word_of_int ((1::int) + length x1c) :: 256 word) :: 8 word list)) = 32")
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1c) =
foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1b)")

    apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound l)")
    apply(subgoal_tac "0 \<le> heads_length l")


           apply(arith)

                 apply(simp add:heads_length_nonneg)
                apply(cut_tac l = "map abi_dynamic_size_bound l" in list_nonneg_sum)
                 apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_nonneg_def list_all_iff)
                 apply(clarify)
                 apply(cut_tac v = x in abi_dynamic_size_bound_nonneg)
                 apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
                apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(cut_tac f= int and g = "(\<lambda>(i::int, y::8 word list). length y)"
and list = x1c in List.map.compositionality)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

         apply(simp add:word_rsplit_def bin_rsplit_len)

            apply(simp add:uint_value_valid_def)
    
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
            apply(clarify)
            apply(drule_tac encode_tuple_heads_fail)
             apply(drule_tac bvs = x1b in encode_tuple_tails_len)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
            apply(clarify)
            apply(drule_tac v = v in encode'_tuple_heads_static_success)
              apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)

             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
            apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def split:sum.splits prod.splits)
    apply(clarify)

    apply(frule_tac heads_length' = "heads_length l" in
encode_tuple_tails_dyn_offset)
             apply(rule_tac heads_length_nonneg)
    apply(simp)

    apply(clarify)
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(cut_tac v = t in abi_dynamic_size_bound_nonneg)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

      apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
      apply(clarify)
    apply(drule_tac x = "abi_get_type t" in spec)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)

    apply(subgoal_tac
"\<not>abi_type_isdynamic (abi_get_type t)")
      apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def array_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
    apply(case_tac "sint_value_valid (256::nat) ((32::int) + heads_length l)")
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
     apply(clarify)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
     apply(clarify)
    apply(drule_tac x = "abi_get_type t" in spec)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(case_tac " encode' (Varray (abi_get_type t) l)")
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(drule_tac x = "word_rsplit (word_of_int (int (length l)) :: 256 word) @ x1e @ x2" in spec)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(case_tac "uint_value_valid (256::nat) (int (length l))")
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(clarify)
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(drule_tac x = "nat(abi_dynamic_size_bound t)" in spec)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)
    apply(case_tac "(0::int) \<le> abi_dynamic_size_bound t")
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac bvs = x1c in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

    apply(frule_tac bvs = x1 in encode_tuple_tails_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1c in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac bss = x1 in encode_tuple_heads_len)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def split:sum.splits prod.splits)

         apply(frule_tac a = x1c in encode_tuple_heads_headslength)
         apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)
         apply(frule_tac a = x1 in encode_tuple_heads_headslength)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

         apply(drule_tac encode_tuple_heads_len2)
         apply(drule_tac encode_tuple_heads_len2)
          apply(simp del:abi_dynamic_size_bound.simps add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits)

    apply(frule_tac
headlen' = 0
and len_total' = "heads_length l"
and bvs' = x1
in encode_tuple_tails_len_sum)

    apply(clarify)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac x = "(abi_dynamic_size_bound t)"
and i = 0
and xs = "(map abi_dynamic_size_bound l)"
in foldl_plus)
    apply(rotate_tac -1)
    apply(drule_tac sym)
         apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"int (length (word_rsplit (word_of_int ((32::int) + heads_length l) :: 256 word) :: 8 word list)) = 32")
          apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(subgoal_tac
"foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1c) =
foldl (+) (0::int) (map (int \<circ> (\<lambda>(i::int, y::8 word list). length y)) x1)")

          apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound l)")
           apply(subgoal_tac "(int (length (word_rsplit (word_of_int (int (length x1c)) :: 256 word) :: 8 word list))) = 32")
apply(subgoal_tac "(int (length (word_rsplit (word_of_int (1 + int (length x1c)) :: 256 word) :: 8 word list))) = 32")
    apply(subgoal_tac "0 \<le> nat (abi_dynamic_size_bound t)")
    apply(subgoal_tac "0 \<le> heads_length l")
             apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

           apply(arith)

             apply(simp)

         apply(simp add:word_rsplit_def bin_rsplit_len)
           apply(simp add:word_rsplit_def bin_rsplit_len)

          apply(simp)

                apply(cut_tac l = "map abi_dynamic_size_bound l" in list_nonneg_sum)
                 apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def list_nonneg_def list_all_iff)
                 apply(clarify)
                 apply(cut_tac v = x in abi_dynamic_size_bound_nonneg)
                 apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    apply(cut_tac f= int and g = "(\<lambda>(i::int, y::8 word list). length y)"
and list = x1c in List.map.compositionality)
    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

        apply(simp add:word_rsplit_def bin_rsplit_len)

       apply(cut_tac v = t in abi_dynamic_size_bound_nonneg)

       apply(clarify)

    apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
      apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def uint_value_valid_def)

     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

    apply(case_tac "encode'_tuple_tails l (0::int) (heads_length l)")
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
      apply(case_tac "encode'_tuple_heads l a")
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
      apply(case_tac "aa")
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

      apply(frule_tac encode_tuple_heads_fail)
    apply(frule_tac bvs = a in encode_tuple_tails_len)
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
      apply(clarify)
    apply(frule_tac v = v and bvs = a in encode'_tuple_tails_dyn_success)
        apply(clarify)
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

     apply(drule_tac heads_length' = "heads_length l" in encode_tuple_tails_dyn_offset)
    apply(clarify) apply(simp add:heads_length_nonneg)
       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
     apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)

       apply(simp del:abi_dynamic_size_bound.simps add:list_sum_def)
    done
qed

lemma abi_dynamic_size_bound_correct [rule_format]:
"(\<forall> bound code . encode v = Ok code \<longrightarrow>
    abi_dynamic_size_bound v = bound \<longrightarrow>           
            abi_value_valid v \<longrightarrow>
            length code \<le> bound)"
  apply(cut_tac v = v in abi_dynamic_size_bound_correct')
  apply(clarify) apply(rotate_tac 1)
  apply(drule_tac mythin)
  apply(simp)
  done
(*
lemma abi_dynamic_size_dyn_32 [rule_format] :
"abi_type_isdynamic (abi_get_type v) \<Longrightarrow> 32 \<le> abi_dynamic_size_bound v"
  apply(case_tac v; simp add:list_sum_def)
    apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x93)")
  apply(drule_tac list_nonneg_sum) apply(simp add:list_sum_def)
  apply(simp del:abi_dynamic_size_bound.simps add:list_nonneg_def list_all_iff)
  done
*)
lemma abi_dynamic_size_bound_headslength [rule_format]:
"heads_length vs \<le> 32 * int (length vs) + foldl (+) (0::int) (map abi_dynamic_size_bound vs)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
    apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
    apply(case_tac "abi_type_isdynamic (abi_get_type a)")
     apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
     apply(cut_tac i = 0 and 
x = "(abi_dynamic_size_bound a)"
and
xs = "(map abi_dynamic_size_bound vs)" in foldl_plus)
    apply(rotate_tac -1)
    apply(drule_tac sym)
     apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
    apply(subgoal_tac "0 \<le> abi_dynamic_size_bound a")
    apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
    apply(rule_tac abi_dynamic_size_bound_nonneg)
     apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
     apply(cut_tac i = 0 and 
x = "(abi_dynamic_size_bound a)"
and
xs = "(map abi_dynamic_size_bound vs)" in foldl_plus)
     apply(rotate_tac -1) apply(drule_tac sym)
     apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
     apply(cut_tac v = a in abi_dynamic_size_bound_static) apply(simp)
     apply(simp del:abi_dynamic_size_bound.simps add:Let_def list_sum_def)
    done
qed

lemma encode_tuple_tails_overflow_fail' [rule_format] :
"
     (\<forall> err headlen   .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     list_all abi_value_valid vs \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     heads_length vs \<le> headlen \<longrightarrow>
     \<not> sint_value_valid 256 (int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs)))
     "
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case

    apply(clarify)
    apply(simp only:encode'_tuple_tails.simps)
    apply(case_tac " abi_type_isstatic (abi_get_type a)") 
    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
           
     apply(rotate_tac -2)
     apply(drule_tac x = err in spec) apply(drule_tac x = headlen in spec)
    apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
     apply(simp only:sint_value_valid_def)
     apply(subgoal_tac "heads_length vs \<le> headlen") apply(simp only:) apply(clarify)
      apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac l = "(abi_dynamic_size_bound a # map abi_dynamic_size_bound vs)" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
    apply(rule_tac conjI)
        apply(rule_tac abi_dynamic_size_bound_nonneg)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
        apply(rule_tac abi_dynamic_size_bound_nonneg)

(*      apply(subgoal_tac " (0::int) \<le> int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs)")
*)
    apply(subgoal_tac
"- (57896044618658097711785492504343953926634992332820282019728792003956564819968::int)
       \<le> int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs)")
       apply(clarify)

       apply(simp add:list_sum_def  del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp)

      apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(clarsimp)

     apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
     apply(arith)

    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
      apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)


       apply(simp add: list_sum_def del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp  del: encode'.simps abi_dynamic_size_bound.simps
 add:sint_value_valid_def) apply(clarify)
(*
      apply(subgoal_tac "0 \<le> headlen")
*)
    apply(subgoal_tac " - (57896044618658097711785492504343953926634992332820282019728792003956564819968::int) \<le> headlen")
       apply(clarify)
    apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound vs)")
        apply(simp del: encode'.simps abi_dynamic_size_bound.simps)

        apply(subgoal_tac "heads_length vs \<le> 32 * int (length vs) + foldl (+) (0::int) (map abi_dynamic_size_bound vs)") 
         apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
    apply(rule_tac "abi_dynamic_size_bound_headslength")
      apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(clarsimp) apply(simp add:list_sum_def)

    apply(cut_tac l = vs in heads_length_nonneg)
      apply(simp del: encode'.simps abi_dynamic_size_bound.simps)

        apply(clarify)
        apply(drule_tac x = err in spec) apply(drule_tac x = "headlen + length (x1)" in spec)
        apply(clarify)
        apply(subgoal_tac "heads_length vs \<le>  headlen + int (length x1)")
       apply(simp add: list_sum_def del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp  del: encode'.simps abi_dynamic_size_bound.simps
 add:sint_value_valid_def) apply(clarify)
    apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound vs)")
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
          apply(subgoal_tac "length x1 \<le> abi_dynamic_size_bound a")
           apply(arith)

    apply(cut_tac v = a and code = x1
and bound = "nat (abi_dynamic_size_bound a)" in abi_dynamic_size_bound_correct)
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps add: encode_def abi_dynamic_size_bound_correct)
         apply(simp)
        apply(simp add:list_all_iff)
    apply(simp)

    apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps add: list_sum_def list_nonneg_def list_all_iff encode_def abi_dynamic_size_bound_correct)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(simp add:list_sum_def)
     apply(simp)

    apply(clarify)
    apply(drule_tac x = a in spec)
    apply(clarsimp)
    done

qed
(*
lemma encode_tuple_tails_overflow_fail_array' [rule_format] :
"
     (\<forall> err headlen   .
     encode'_tuple_tails (vs) 0 (headlen) = Err err \<longrightarrow>
     list_all abi_value_valid vs \<longrightarrow>
     (\<forall> v . v \<in> set vs \<longrightarrow> abi_type_isdynamic (abi_get_type v) \<longrightarrow> (\<exists> code . encode' v = Ok code)) \<longrightarrow>
     heads_length vs \<le> headlen \<longrightarrow>
     \<not> uint_value_valid 256 (int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs)))
     "
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case

    apply(clarify)
    apply(simp only:encode'_tuple_tails.simps)
    apply(case_tac " abi_type_isstatic (abi_get_type a)") 
    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
           
     apply(rotate_tac -2)
     apply(drule_tac x = err in spec) apply(drule_tac x = headlen in spec)
    apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
     apply(simp only:uint_value_valid_def)
     apply(subgoal_tac "heads_length vs \<le> headlen") apply(simp only:) apply(clarify)
      apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac l = "(abi_dynamic_size_bound a # map abi_dynamic_size_bound vs)" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
    apply(rule_tac conjI)
        apply(rule_tac abi_dynamic_size_bound_nonneg)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
        apply(rule_tac abi_dynamic_size_bound_nonneg)

      apply(subgoal_tac " (0::int) \<le> int (length vs) * (32::int) + list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs)")
       apply(clarify)

       apply(simp add:list_sum_def  del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp)

      apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(clarsimp)

     apply(cut_tac v = "abi_get_type a" in abi_static_size_nonneg)
     apply(arith)

    apply(simp del:encode'.simps abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)
      apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps split:sum.split_asm prod.splits if_splits)


       apply(simp add: list_sum_def del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp  del: encode'.simps abi_dynamic_size_bound.simps
 add:uint_value_valid_def) apply(clarify)
      apply(subgoal_tac "0 \<le> headlen")
       apply(clarify)
    apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound vs)")
        apply(simp del: encode'.simps abi_dynamic_size_bound.simps)

        apply(subgoal_tac "heads_length vs \<le> 32 * int (length vs) + foldl (+) (0::int) (map abi_dynamic_size_bound vs)") 
         apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
    apply(rule_tac "abi_dynamic_size_bound_headslength")
      apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
       apply(simp only:list_nonneg_def)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
       apply(simp add:list_all_iff del: encode'.simps abi_dynamic_size_bound.simps)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(clarsimp) apply(simp add:list_sum_def)

    apply(cut_tac l = vs in heads_length_nonneg)
      apply(simp del: encode'.simps abi_dynamic_size_bound.simps)

        apply(clarify)
        apply(drule_tac x = err in spec) apply(drule_tac x = "headlen + length (x1)" in spec)
        apply(clarify)
        apply(subgoal_tac "heads_length vs \<le>  headlen + int (length x1)")
       apply(simp add: list_sum_def del: encode'.simps abi_dynamic_size_bound.simps)
       apply(cut_tac x = "(abi_dynamic_size_bound a)" and i = 0 and xs = "map abi_dynamic_size_bound vs"
in foldl_plus) apply(rotate_tac -1) apply(drule_tac sym)
       apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
      apply(cut_tac v = a in abi_dynamic_size_bound_nonneg)
    apply(simp  del: encode'.simps abi_dynamic_size_bound.simps
 add:uint_value_valid_def) apply(clarify)
    apply(subgoal_tac "0 \<le> foldl (+) (0::int) (map abi_dynamic_size_bound vs)")
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps)
          apply(subgoal_tac "length x1 \<le> abi_dynamic_size_bound a")
           apply(arith)

    apply(cut_tac v = a and code = x1
and bound = "nat (abi_dynamic_size_bound a)" in abi_dynamic_size_bound_correct)
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps add: encode_def abi_dynamic_size_bound_correct)
         apply(simp)
        apply(simp add:list_all_iff)
    apply(simp)

    apply(cut_tac l = "map abi_dynamic_size_bound vs" in list_nonneg_sum)
          apply(simp del: encode'.simps abi_dynamic_size_bound.simps add: list_sum_def list_nonneg_def list_all_iff encode_def abi_dynamic_size_bound_correct)
       apply(clarify)
       apply(rule_tac abi_dynamic_size_bound_nonneg)
      apply(simp add:list_sum_def)
     apply(simp)

    apply(clarify)
    apply(drule_tac x = a in spec)
    apply(clarsimp)
    done

qed
*)

lemma
those_err_exists [rule_format]:
    "\<forall> err . those_err l = Err err \<longrightarrow>
    (\<exists> x err' . x \<in> set l \<and> x = Err err')"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
    apply(clarsimp)
    apply(case_tac a; clarsimp)
     apply(simp split:sum.splits)
     apply(clarify)
     apply(fastforce)

    apply(rule_tac x = a in exI) apply(simp)
    done
qed

value "2 ^ 64:: int"

lemma encode_correct_converse [rule_format] :
  "\<forall> code start . 
      can_encode_as v code start \<longrightarrow>
      sint_value_valid 256 (abi_dynamic_size_bound v)  \<longrightarrow>
  (\<exists> code' . encode v = Ok code')"
proof(induction v)
case (Vuint x1 x2)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vsint x1 x2)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vaddr x)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vbool x)
  then show ?case
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfixed x1 x2 x3a)
  then show ?case

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vufixed x1 x2 x3a)
  then show ?case

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfbytes x1 x2)
  then show ?case 

    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vfunction x1 x2)
  then show ?case sorry
next
  case (Vfarray x1 x2 x3a)
  then show ?case
    apply(atomize)
    apply(clarify)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    apply(simp add: farray_value_valid_aux_def) apply(clarsimp)
    apply(simp split:sum.splits)
    apply(rule_tac conjI)
     apply(clarsimp)
     apply(frule_tac encode_tuple_heads_fail)
    apply(simp add:encode_tuple_tails_len)
     apply(clarsimp)
     apply(frule_tac x = v in is_head_and_tail_vs_elem) apply(simp)

      apply(subgoal_tac "abi_type_isdynamic (abi_get_type v)")
       apply(clarsimp)
      defer

      apply(subgoal_tac "abi_type_isdynamic (abi_get_type v)")
       apply(clarsimp)
    

    apply(drule_tac x = v in spec)
      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
       apply(clarsimp)
    apply(case_tac
"sint_value_valid (256::nat)
        (case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l)
         | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs) | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs + (32::nat))
         | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s + (32::nat)) | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))")        apply(clarsimp)

    apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v") apply(clarsimp)
    apply(clarsimp)
        apply(clarsimp)

        apply(cut_tac v = "Vfarray x1 x2 x3a" in abi_dynamic_size_bound_nonneg)
        apply(simp)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x3a)" in elem_lt_list_sum)
          apply(clarsimp)
         apply(simp add:list_nonneg_def)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)

        apply(simp)
        apply(simp add:sint_value_valid_def)
    apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
    apply(simp)

       apply(atomize)
    apply(drule_tac x = offset in spec) apply(rotate_tac -1) apply(drule_tac x= v in spec)
        apply(clarsimp)
       apply(fastforce)

      apply(simp add:list_all_iff)

   apply(clarsimp)
     apply(frule_tac encode_tuple_tails_overflow_fail') apply(simp add:list_all_iff)

       apply(atomize)
         apply(clarsimp)

(* at this point, the intuition is that the offset can't encode as a s256 *)
       apply(frule_tac x = v in is_head_and_tail_vs_elem) apply(simp) apply(simp) apply(clarify)
       apply(drule_tac x = offset in spec) apply(rotate_tac -1)
       apply(drule_tac x = v in spec) apply(clarsimp)
    apply(drule_tac x = v in spec) apply(clarsimp)


    apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
     apply(clarsimp)

(* need to talk about how length of full encoding works out implies length of sub encoding
also does *)

    apply(subgoal_tac " sint_value_valid (256::nat)
        (case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l) | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs)
         | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs + (32::nat)) | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s + (32::nat))
         | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))")
      apply(clarsimp)

    apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v") apply(clarsimp)
         apply(clarsimp)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x3a)" in elem_lt_list_sum)
       apply(clarsimp) apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff) apply(clarsimp)
      apply(rotate_tac 1)

         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)
         apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)
        apply(simp add:sint_value_valid_def)

       apply(rule_tac x = full_code in exI) apply(fastforce)
      apply(simp)
     apply(simp add:uint_value_valid_def)

    apply(simp add:list_all_iff)

    done
next
  case (Vtuple x1 x2)
  then show ?case

    apply(clarify)
    apply(atomize)
       apply(drule_tac can_encode_as.cases; auto simp add:encode_def simp del:abi_dynamic_size_bound.simps)
    apply(simp add: tuple_value_valid_aux_def del:abi_dynamic_size_bound.simps) apply(clarify)
     apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)
     apply(clarify)
     apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)

     apply(frule_tac those_err_exists)
    apply(clarify)
     apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)
     apply(subgoal_tac "\<exists> xe \<in> set x2 . encode_static xe = Err err'")
      apply(clarify)
     apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)

      apply(frule_tac x = xa in is_head_and_tail_vs_elem_static) apply(simp)
       apply(simp add:list_ex_iff)
    apply(drule_tac v = "(Vtuple head_types heads)" and vd = xa in 
can_encode_as_tuple_split)
        apply(simp)
       apply(simp)
      apply(clarify)
      apply(drule_tac x = xa in spec) apply(clarify)
    apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as xa code))")
         apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)
       apply(subgoal_tac "sint_value_valid (256::nat) (abi_dynamic_size_bound xa)")
    apply(clarify)
        apply(simp del:abi_dynamic_size_bound.simps split:sum.splits if_splits)

    apply(subgoal_tac " abi_type_isstatic (abi_get_type xa)")
        apply(simp del:abi_dynamic_size_bound.simps split:sum.splits if_splits)
    apply(simp add:list_ex_iff)

        apply(cut_tac x = "abi_dynamic_size_bound xa" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)
       apply(clarsimp) apply(simp add:list_nonneg_def)
        apply(simp del:abi_dynamic_size_bound.simps add:list_all_iff) apply(clarify)
        apply(rule_tac abi_dynamic_size_bound_nonneg)
       apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)

       apply(simp del:abi_dynamic_size_bound.simps add:sint_value_valid_def list_sum_def)
       apply(clarify)
    apply(clarsimp)
    apply(rule_tac conjI) apply(clarsimp)

    apply(simp add:list_all_iff list_ex_iff)

       apply(clarsimp)

    apply(simp add:list_all_iff list_ex_iff)
      apply(rule_tac x = coded in exI) apply(fastforce)

     apply(clarify)
     apply(fastforce)


    apply(simp add:tuple_value_valid_aux_def list_ex_iff del:abi_dynamic_size_bound.simps)
    apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps)
    apply(simp add:Set.image_iff del:abi_dynamic_size_bound.simps)
    apply(clarify)

      apply(frule_tac x = xa in is_head_and_tail_vs_elem)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

    apply(clarify)
    apply(atomize)

    apply(simp del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits)
    apply(rule_tac conjI)
    apply(clarify)

     apply(frule_tac encode_tuple_heads_fail)
      apply(simp add:encode_tuple_tails_len)
     apply(clarify)

     apply(drule_tac x = v in spec) apply(clarify)
     apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code)) ")
    apply(simp del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits)
      apply(clarify)

      apply(subgoal_tac "sint_value_valid (256::nat) (abi_dynamic_size_bound v)")
    apply(clarify)

       apply(simp del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)
       apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
       apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(simp only:list_all_iff)
        apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(clarify)
    apply(rule_tac abi_dynamic_size_bound_nonneg)
        apply(simp only:list_all_iff)
        apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)

      apply(simp add: sint_value_valid_def list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
(* new *)
       apply(subgoal_tac "- (57896044618658097711785492504343953926634992332820282019728792003956564819968::int) \<le> abi_dynamic_size_bound v")
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
    apply(case_tac "abi_type_isstatic (Ttuple (map abi_get_type x2))")
         apply(simp only:abi_dynamic_size_bound.simps)
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
    apply(cut_tac l = x2 in abi_dynamic_size_bound_static_list)
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
           apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
          apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
         apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(clarify)
         apply(simp only:abi_dynamic_size_bound.simps)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
    apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)

apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)


(*
    apply(subgoal_tac "map abi_dynamic_size_bound x2 = map (abi_static_size \<circ> abi_get_type) x2")
        apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(rule_tac map_ext)
        apply(clarify)
        apply(simp)
        apply(clarsimp)
        apply(simp add:list_all_iff list_ex_iff)
        apply(simp add:list_all_iff list_ex_iff)
        apply(simp add:list_all_iff list_ex_iff)
*)
     apply(case_tac "abi_type_isdynamic (abi_get_type v)")
(*    apply(simp del:  abi_dynamic_size_bound.simps split:sum.splits) *)

      apply(frule_tac x = v in is_head_and_tail_vs_elem)
    apply(simp)
    apply(simp)
      apply(clarify)
    apply(drule_tac x = offseta in spec) apply(drule_tac x = v in spec)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
      apply(rule_tac x = full_code in exI)
    apply(fastforce)

      apply(frule_tac x = v in is_head_and_tail_vs_elem_static)
    apply(simp)
      apply(simp)
     apply(drule_tac vd = v in can_encode_as_tuple_split)
apply(simp)
      apply(simp)
     apply(clarify)


    apply(clarify)

    apply(frule_tac encode_tuple_tails_overflow_fail')
    apply(simp add:list_all_iff)

      apply(frule_tac x = v in is_head_and_tail_vs_elem)
        apply(simp)
       apply(simp) apply(clarify)
    apply(drule_tac x = offseta in spec) apply(rotate_tac -1) apply(drule_tac x = v in spec)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

      apply(drule_tac x = v in spec)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
       apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
       apply(subgoal_tac "sint_value_valid (256::nat) (abi_dynamic_size_bound v)")
        apply(clarify)
       apply(simp del: abi_dynamic_size_bound.simps encode'.simps split:if_splits)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)
       apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
       apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(simp only:list_all_iff)
        apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(clarify)
    apply(rule_tac abi_dynamic_size_bound_nonneg)
        apply(simp only:list_all_iff)
        apply(simp add: list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)

       apply(simp add: sint_value_valid_def list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)

(* new *)
       apply(subgoal_tac "- (57896044618658097711785492504343953926634992332820282019728792003956564819968::int) \<le> abi_dynamic_size_bound v")
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
    apply(case_tac "abi_type_isstatic (Ttuple (map abi_get_type x2))")
         apply(simp only:abi_dynamic_size_bound.simps)
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
    apply(cut_tac l = x2 in abi_dynamic_size_bound_static_list)
        apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
           apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
          apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
         apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(clarify)
         apply(simp only:abi_dynamic_size_bound.simps)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
        apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
    apply(arith)
apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)

apply(simp add: abi_dynamic_size_bound_nonneg list_nonneg_def list_all_iff list_ex_iff del: abi_dynamic_size_bound.simps encode'.simps split:sum.splits if_splits)
(* end new *)

      apply(rule_tac x = full_code in exI)
    apply(fastforce)
     apply(clarsimp)
    apply(simp add:list_sum_def sint_value_valid_def del:abi_dynamic_size_bound.simps)
    apply(clarify)

    apply(simp)
    apply(case_tac "list_ex abi_type_isdynamic (map abi_get_type x2)")
     apply(simp add:list_sum_def)

        apply(simp add:list_all_iff list_ex_iff)
    done
next
  case (Vbytes x)
  then show ?case 
    apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def)
    done
next
  case (Vstring x)
  then show ?case
apply(clarsimp)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def string_value_valid_def)
    apply(drule_tac can_encode_as.cases; auto simp add:encode_def string_value_valid_def)
    done
next
  case (Varray x1 x2)
  then show ?case 
    apply(clarify)
    apply(atomize)
       apply(drule_tac can_encode_as.cases; auto simp add:encode_def simp del:abi_dynamic_size_bound.simps)
    apply(simp add: array_value_valid_aux_def del:abi_dynamic_size_bound.simps) apply(clarify)
    apply(simp del:abi_dynamic_size_bound.simps split:sum.splits)
    apply(rule_tac conjI)
     apply(clarify)
     apply(frule_tac encode_tuple_heads_fail)
      apply(simp add:encode_tuple_tails_len del:abi_dynamic_size_bound.simps)
    apply(clarify)

      apply(case_tac "abi_type_isdynamic (abi_get_type v)")

      apply(frule_tac x = v in is_head_and_tail_vs_elem)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

      apply(clarify)

      apply(drule_tac x = v in spec) 
      apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code)) ")
         apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

    apply(subgoal_tac "sint_value_valid (256::nat) (abi_dynamic_size_bound v)")
        apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
        apply(clarify)
        apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v")
         apply(simp del: abi_dynamic_size_bound.simps encode'.simps)
        apply(simp del: abi_dynamic_size_bound.simps encode'.simps)

       apply(simp add:sint_value_valid_def del: abi_dynamic_size_bound.simps encode'.simps)
       apply(clarify)
        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)

    apply(simp)

    apply(case_tac "sint_value_valid (256::nat)
        (case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l)
         | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs)
         | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs + (32::nat)) | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s + (32::nat))
         | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))")
    apply(clarsimp)
         apply(simp add:list_nonneg_def)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)

         apply(simp add:list_nonneg_def)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(cut_tac v = xa in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)


        apply(simp)
    apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
    apply(simp)

    apply(rule_tac x = full_code in exI)
    apply(fastforce)

     apply(simp del: abi_dynamic_size_bound.simps)
     apply(drule_tac x = v in spec)
     apply(simp del: abi_dynamic_size_bound.simps)
    apply(atomize)
      apply(frule_tac x = v in is_head_and_tail_vs_elem_static)
       apply(simp) apply(simp)
     apply(drule_tac v = "(Vtuple head_types heads)" and vd =  v in can_encode_as_tuple_split)
       apply(simp) apply(simp)
     apply(clarify)
(*
    apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
     apply(simp del: abi_dynamic_size_bound.simps)
      apply(clarify)
  *)  
(*
    apply(drule_tac x = v in spec)
      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
       apply(clarsimp)
    apply(case_tac
"uint_value_valid (256::nat)
        (case v of Vfarray (t::abi_type) (n::nat) (l::abi_value list) \<Rightarrow> int (n * (32::nat)) + list_sum (map abi_dynamic_size_bound l)
         | Vtuple (ts::abi_type list) (vs::abi_value list) \<Rightarrow> int (length vs * (32::nat)) + list_sum (map abi_dynamic_size_bound vs) | Vbytes (bs::8 word list) \<Rightarrow> int ((32::nat) + length bs + (32::nat))
         | Vstring (s::char list) \<Rightarrow> int ((32::nat) + length s + (32::nat)) | Varray (t::abi_type) (l::abi_value list) \<Rightarrow> int ((32::nat) + length l * (32::nat)) + list_sum (map abi_dynamic_size_bound l))")        apply(clarsimp)

    apply(case_tac "abi_type_valid (abi_get_type v) \<and> abi_value_valid_aux v") apply(clarsimp)
    apply(clarsimp)
        apply(clarsimp)
*)
        apply(cut_tac v = "Varray x1 x2" in abi_dynamic_size_bound_nonneg)
        apply(simp)

        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)
          apply(clarsimp)
         apply(simp add:list_nonneg_def)

         apply(simp add:list_all_iff) apply(clarsimp)
         apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)
         apply(clarsimp)

    apply(subgoal_tac "sint_value_valid (256::nat) (abi_static_size (abi_get_type v))")
      apply(clarsimp)
      apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))") apply(clarsimp)
       apply(simp split:if_splits)
      apply(rule_tac x = coded in exI) apply(fastforce)

     apply(simp add:sint_value_valid_def)
     apply(cut_tac v = "abi_get_type v" in abi_static_size_nonneg) apply(arith)

    apply(clarify)
    apply(frule_tac "encode_tuple_tails_overflow_fail'")
       apply(simp del: abi_dynamic_size_bound.simps add:list_all_iff)
      apply(atomize)
    
(* at this point, the intuition is that the offset can't encode as a s256 *)
       apply(frule_tac x = v in is_head_and_tail_vs_elem) apply(simp) apply(simp) apply(clarify)
       apply(drule_tac x = offset in spec) apply(rotate_tac 1)
       apply(drule_tac x = v in spec) apply(simp del: abi_dynamic_size_bound.simps)
    apply(drule_tac x = v in spec) apply(simp del: abi_dynamic_size_bound.simps)


    apply(subgoal_tac "(\<exists>code::8 word list. Ex (can_encode_as v code))")
apply(simp del: abi_dynamic_size_bound.simps)

(* need to talk about how length of full encoding works out implies length of sub encoding
also does *)

    apply(subgoal_tac " sint_value_valid (256::nat)
(abi_dynamic_size_bound v)")
      apply(clarify)
apply(simp del: abi_dynamic_size_bound.simps split:if_splits)


        apply(cut_tac x = "abi_dynamic_size_bound v" and l = "(map abi_dynamic_size_bound x2)" in elem_lt_list_sum)
       apply(clarsimp) apply(simp add:list_nonneg_def)
    apply(simp add:list_all_iff) apply(clarsimp)
      apply(rotate_tac 1)

         apply(cut_tac v = x in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)
         apply(cut_tac v = v in abi_dynamic_size_bound_nonneg)
         apply(clarsimp)
        apply(simp add:sint_value_valid_def)

       apply(rule_tac x = full_code in exI) apply(fastforce)
      apply(simp)
     apply(simp add:sint_value_valid_def)

    apply(subgoal_tac "list_nonneg (map abi_dynamic_size_bound x2)")
     apply(drule_tac list_nonneg_sum)
apply(simp)

apply(simp add:list_nonneg_def)

    apply(simp only:list_all_iff)
    apply(simp del: abi_dynamic_size_bound.simps )
    apply(clarify)
    apply(rule_tac abi_dynamic_size_bound_nonneg)
    done
qed
 

(* other direction: 

lemma abi_encode_succeed_gen :
  "\<forall>  full_code offset . encode v = Ok full_code \<longrightarrow>
         (can_encode_as v full_code offset (length full_code + offset))"
proof(induction v)
  case (Vuint x1 x2)
  then show ?case 
    apply(cut_tac n = x1 and i = x2 and pre1 = "[]" and post1 in Euint)
    apply(auto simp add: encode_def intro:can_encode_as_can_encode_as_list_can_encode_as_list_dyn.intros)
    apply(simp split:if_splits)
    apply(cut_tac Euint) apply(auto)
        apply(auto simp add: encode_def intro:Euint)

next
  case (Vsint x1 x2)
  then show ?case sorry
next
  case (Vaddr x)
  then show ?case sorry
next
  case (Vbool x)
then show ?case sorry
next
  case (Vfixed x1 x2 x3a)
  then show ?case sorry
next
  case (Vufixed x1 x2 x3a)
  then show ?case sorry
next
  case (Vfbytes x1 x2)
  then show ?case sorry
next
  case (Vfunction x1 x2)
  then show ?case sorry
next
  case (Vfarray x1 x2 x3a)
  then show ?case 
  proof(cases "abi_type_isdynamic x1")
    case True
    then show ?thesis using Vfarray
      apply(simp)
      apply(drule_tac all_imp_E)
      apply(clarsimp)
      apply(rule_tac pre_and_vs_code_len = "(int (length full_code) + int offset)" in Efarray_dyn)
(* i dont really understand why we are getting
a metavariable here. *)
        apply(simp)

        defer defer
        apply(case_tac x3a) apply(clarsimp) apply(simp add:encode_def)
      apply(simp split:if_split_asm)
         apply(rule_tac n = "int offset" in Elnil_dyn)

        apply(clarsimp) apply(simp add:encode_def)
      apply(case_tac a; clarsimp)
        apply(case_tac "abi_type_isdynamic (abi_get_type a)")
      
         apply(rule_tac Elcons_dyn_h) apply(simp)

      sorry
  next
    case False
    then show ?thesis using Vfarray
      apply(clarsimp)
      apply(rule_tac Efarray_static)
      defer apply(simp )
  qed
    
    sorry
next
  case (Vtuple x1 x2)
  then show ?case sorry
next
  case (Vbytes x)
  then show ?case sorry
next
  case (Vstring x)
  then show ?case sorry
next
  case (Varray x1 x2)
  then show ?case sorry
qed
  sorry
   

(* if the encoder fails, there is no valid encoding according to spec *)
lemma abi_encode_fail :
  "\<And> v full_code . encode v = None \<Longrightarrow>
         can_encode_as v full_code 0 (int (length full_code)) \<Longrightarrow>
         False"

  sorry
*)
*)
end
