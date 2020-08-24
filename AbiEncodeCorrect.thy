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
  (* Vuint *)
  case (1 n i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  (* Vsint *)
  case (2 n i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  (* Vaddr *)
  case (3 i)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  (* Vbool *)
  case (4 b)
  then show ?case
    by (cases b; auto simp: word_rsplit_def bin_rsplit_len; fail)
next
  (* Vfixed *)
  case (5 m n r)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  (* Vufixed *)
  case (6 m n r)
  then show ?case
    by (auto simp: word_rsplit_def bin_rsplit_len; fail)?
next
  (* Vfbytes *)
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
  (* Vfunction *)
  case (8 i j)
  then show ?case
    by(auto simp add: divmod_nat_def function_value_valid_def
        word_rsplit_def bin_rsplit_len)
next
  (* Vfarray *)
  case (9 t n l)
  then show ?case by auto
next
  (* Vtuple *)
  case (10 ts vs)
  then show ?case by auto
next
  (* Vbytes *)
  case (11 bs)
  then show ?case by auto
next
  (* Vstring *)
  case (12 s)
  then show ?case by auto
next
  (* Varray *)
  case (13 t vs)
  then show ?case by auto
next
  (* Nil *)
  case 14
  { case 1 then show ?case 
      by (simp add:farray_value_valid_aux_def tuple_value_valid_aux_def) 
  next
    case 2 then show ?case
      by (simp add:farray_value_valid_aux_def tuple_value_valid_aux_def)
  }
next
  (* Cons *)
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


lemma encode'_tuple_heads_headslength:
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


(*
 * main theorem 1:
 * if encoder succeeds, result is a valid encoding w/r/t spec
 *)
theorem abi_encode_succeed :
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
        encode'_tuple_heads_headslength[OF Hhts]
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
        encode'_tuple_heads_headslength[OF Hhts]
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
      encode'_tuple_heads_headslength[OF Hhts]
      Code_ht Abc2 Abc3 Lvalid' EncLen
      by(auto simp add:Rearrange)
  qed
qed

(* if encoding of heads fails, entire encoding fails *)
lemma encode'_tuple_heads_fail:
  "encode'_tuple_heads vs bss = Err err \<Longrightarrow>
   length vs = length bss \<Longrightarrow>
    (\<exists> v err' . v \<in> set vs \<and> encode' v = Err err')"
proof(induction vs arbitrary: bss err)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then obtain offset bs bst where Bsh : "(bss = (offset, bs)#bst)"
    by(cases bss; auto)
  then show ?case
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case True
    then obtain err' where Herr' : "encode'_tuple_heads vs bst = Err err'" using Cons.prems Bsh
      by(auto split:sum.split_asm)
    then show ?thesis using Cons.prems Cons.IH[OF Herr'] Bsh 
      by(auto)
  next
    case False 
    then show ?thesis
    proof(cases "encode_static a")
      case (Inl bs)
      then obtain err' where Herr' : "encode'_tuple_heads vs bst = Err err'" using False Cons.prems Bsh
        by(auto split:sum.split_asm)
      then show ?thesis using Cons.prems Cons.IH[OF Herr'] Bsh 
        by(auto)
    next
      case (Inr err')
      show ?thesis
        by(rule exI[of _ a]; auto simp add: Bsh Inr False)
    qed
  qed
qed

lemma those_err_forall:
  "those_err l = Ok l' \<Longrightarrow>
    x \<in> set l \<Longrightarrow>
    (\<exists> x' . x = Ok x' \<and> x' \<in> set l')"
proof(induction l arbitrary: l' x)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain a' where A' : "a = Ok a'" using Cons.prems by(cases a; auto)
  then obtain l'' where L' : "those_err l = Ok l''" using Cons.prems
    by(cases "those_err l"; auto)
  then show ?case
  proof(cases "x = a")
    case True
    then show ?thesis using Cons.prems A' by(auto split:sum.split_asm)
  next
    case False
    hence X_in_l : "x \<in> set l" using Cons.prems by auto
    then show ?thesis using Cons.prems Cons.IH[OF L' X_in_l] L' A' by(auto)
  qed
qed

lemma map_elem :
  "x \<in> set l \<Longrightarrow>
   f x \<in> set (map f l)"
proof(induction l arbitrary: f x; auto)
qed

(* if a tuple can be encoded according to spec,
   so can all its elements *)
lemma can_encode_as_tuple_split [rule_format]:
"can_encode_as v full_code offset \<Longrightarrow>
 v = (Vtuple ts vs) \<Longrightarrow>
 vd \<in> set vs \<Longrightarrow>
 (\<exists> coded offsetd . can_encode_as vd coded offsetd)"
proof(induction arbitrary: ts vs vd rule: can_encode_as.induct)
  case (Estatic v pre post code)
  then obtain encs where Encs : "those_err (map encode_static vs) = Ok encs"
    by(auto split:sum.splits)

  obtain vd' where Vd' : "encode_static vd = Ok vd'" using Estatic
      those_err_forall[OF Encs] by(auto)

  have Vd_static : "abi_type_isstatic (abi_get_type vd)"
    using Estatic by(auto simp add:tuple_value_valid_aux_def list_ex_iff)

  have Valid : "abi_value_valid vd"
    using Estatic by(auto simp add:tuple_value_valid_aux_def list_all_iff)

  then show ?case using Estatic can_encode_as.Estatic[OF Vd_static Valid Vd', of "[]" "[]"]
    by auto
next
  case (Etuple_dyn ts' vs' t heads head_types tails start full_code)
  then show ?case
  proof(cases "abi_type_isdynamic (abi_get_type vd)")
    case False
    then show ?thesis using Etuple_dyn is_head_and_tail_vs_elem_static
      by(auto)
  next
    case True
    have Vd_in : "vd \<in> set vs'" using Etuple_dyn by auto
    obtain offset'  where Vd_in_tails: "(offset', vd) \<in> set tails"
      using is_head_and_tail_vs_elem[OF Etuple_dyn(4) Vd_in True] by auto
    show ?thesis using Etuple_dyn.hyps(6)[OF Vd_in_tails] by auto
  qed
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

(* the offset at which an encoding begins
   is always less than the length of the entire byte-string *)
lemma can_encode_as_start :
"can_encode_as v full_code offset \<Longrightarrow>
 (offset \<le> int (length (full_code)))"
proof(induction rule:can_encode_as.inducts; auto)
qed

(* if an encoding for a static piece of data exists according to spec,
   the static encoder will return it *)
lemma encode_static_correct_converse :
  "can_encode_as v full_code start \<Longrightarrow>
   full_code = pre @ code @ post \<Longrightarrow>
   start = length pre \<Longrightarrow>
   abi_type_isstatic (abi_get_type v) \<Longrightarrow>
   abi_static_size (abi_get_type v) = length code \<Longrightarrow>
   (abi_value_valid v \<and> encode_static v = Ok code)"
proof(induction arbitrary: pre code post rule:can_encode_as.induct)
  case (Estatic v pre' post' code')
  then show ?case using encode_static_size by auto
next
  case (Etuple_dyn ts vs t heads head_types tails start full_code)
  then show ?case by(auto simp add: tuple_value_valid_aux_def list_ex_iff)
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

(* can_encode_as only holds for valid data *)
lemma encode_correct_converse_valid :
  "can_encode_as v full_code start \<Longrightarrow>
     (abi_value_valid v)"
proof(induction rule:can_encode_as.induct; auto)
qed

definition list_nonneg :: "int list \<Rightarrow> bool" where
"list_nonneg l = list_all (\<lambda> x . 0 \<le> x) l"

(* non-negative lists have non-negative sum *)
lemma list_nonneg_sum :
  " list_nonneg l \<Longrightarrow>
    0 \<le> list_sum l"
proof(induction l)
  case Nil
  then show ?case 
    by(simp add: list_nonneg_def list_sum_def)
next
  case (Cons a l)
  then show ?case unfolding list_nonneg_def list_sum_def
      using foldl_plus[of a 0 l] by auto
qed

(* for nonnegative lists, each element is less than the sum *)
lemma elem_lt_list_sum :
  "x \<in> set l \<Longrightarrow>
   list_nonneg l \<Longrightarrow>
   x \<le> list_sum l"
proof(induction l arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have L_nonneg : "list_nonneg l" using Cons unfolding list_nonneg_def by auto
  show ?case
  proof(cases "x = a")
    case True
    show ?thesis using Cons True  list_nonneg_sum[OF L_nonneg] 
      foldl_plus[of a 0 l]
      unfolding list_sum_def by(auto)
  next
    case False
    then have Xl : "x \<in> set l" using Cons by auto
    have Xnonneg : "0 \<le> x" using Cons unfolding list_nonneg_def list_all_iff by auto
    have Anonneg : "0 \<le> a" using Cons unfolding list_nonneg_def list_all_iff by auto
    then show ?thesis using Cons.IH[OF Xl L_nonneg] foldl_plus[of a 0 l]
      unfolding list_sum_def by(auto)
  qed
qed

lemma abi_static_size_nonneg :
  "0 \<le> abi_static_size v"
proof(induction v; (auto; fail)?)
  fix x
  assume H : "\<And>xa. xa \<in> set x \<Longrightarrow> 0 \<le> abi_static_size xa"
  then show "0 \<le> abi_static_size (Ttuple x)"
    using list_nonneg_sum[of "map abi_static_size x"]
    unfolding list_nonneg_def list_sum_def list_all_iff
    by auto
qed

lemma abi_dynamic_size_bound_nonneg :
  "0 \<le> abi_dynamic_size_bound v"
proof(induction v; (auto; fail)?)
  case (Vfarray t n vs)
  thus "0 \<le> abi_dynamic_size_bound (Vfarray t n vs)"
  proof(cases "abi_type_isdynamic t")
    case False
    then show ?thesis 
     by(simp add: abi_static_size_nonneg)
  next
    case True
    have Nonneg : "list_nonneg (map abi_dynamic_size_bound vs)"
      unfolding list_nonneg_def list_all_iff
    proof
      fix x
      assume Hx : "x \<in> set (map abi_dynamic_size_bound vs)"
      then obtain x' where X'in : "x' \<in> set vs"
                       and X'bound: "x = abi_dynamic_size_bound x'"
        by(auto)
      show "0 \<le> x" using Vfarray[OF X'in] X'bound by auto
    qed

    hence "0 \<le> list_sum (map abi_dynamic_size_bound vs)"
      using list_nonneg_sum by auto

    thus ?thesis using True by(auto)
  qed
next

  case (Vtuple ts vs)
  thus "0 \<le> abi_dynamic_size_bound (Vtuple ts vs)"
  proof(cases "abi_type_isdynamic (Ttuple ts)")
    case False
    have Nonneg : "list_nonneg (map abi_static_size ts)"
      using abi_static_size_nonneg
      unfolding list_nonneg_def list_all_iff by auto
    have "0 \<le> foldl (+) 0 (map abi_static_size ts)"
      using list_nonneg_sum[OF Nonneg]
      unfolding list_sum_def by auto
    then show ?thesis using False by(auto)
  next
    case True
    have Nonneg : "list_nonneg (map abi_dynamic_size_bound vs)"
      unfolding list_nonneg_def list_all_iff
    proof
      fix x
      assume Hx : "x \<in> set (map abi_dynamic_size_bound vs)"
      then obtain x' where X'in : "x' \<in> set vs"
                       and X'bound: "x = abi_dynamic_size_bound x'"
        by(auto)
      show "0 \<le> x" using Vtuple[OF X'in] X'bound by auto
    qed

    hence "0 \<le> list_sum (map abi_dynamic_size_bound vs)"
      using list_nonneg_sum by auto

    thus ?thesis using True by(auto)
  qed
next

  case (Varray t vs)
  have Nonneg : "list_nonneg (map abi_dynamic_size_bound vs)"
    unfolding list_nonneg_def list_all_iff
  proof
    fix x
    assume Hx : "x \<in> set (map abi_dynamic_size_bound vs)"
    then obtain x' where X'in : "x' \<in> set vs"
                     and X'bound: "x = abi_dynamic_size_bound x'"
      by(auto)
    show "0 \<le> x" using Varray[OF X'in] X'bound by auto
  qed

  hence "0 \<le> list_sum (map abi_dynamic_size_bound vs)"
    using list_nonneg_sum by auto

  thus "0 \<le> abi_dynamic_size_bound (Varray t vs)"  by(auto)
qed

lemma zero_leq_nat:
  "0 \<le> int (n :: nat)"
proof(induction n; auto)
qed

lemma oneplus_times :
  "0 \<le> a \<Longrightarrow> 0 \<le> b \<Longrightarrow>
  (1 + a :: int) * (b :: int) =
   b + a * b"
  by(simp add:int_distrib)


lemma encode'_tuple_heads_len2 :
  "encode'_tuple_heads vs bss = Ok (heads, tails) \<Longrightarrow>
   length tails = list_sum (map (\<lambda> (i, l) . length l) bss)"
proof(induction vs arbitrary: bss heads tails)
  case Nil
  then show ?case by (cases bss; auto simp add: list_sum_def)
next
  case (Cons a vs)
  then obtain ofh ench bst where Bss : "bss = (ofh, ench) # bst"
    by(cases bss; auto)
  show ?case
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case True
    then obtain heads' tails' where "encode'_tuple_heads vs bst = Ok (heads', tails')"
      using Cons Bss by(auto split:sum.split_asm)
    then show ?thesis using Cons Bss True
      using foldl_plus
      by (auto simp add:list_sum_def)
  next
    case False
    then obtain aenc where Aenc : "encode_static a = Ok aenc" using Cons False Bss
      by(auto split:sum.split_asm)

    then obtain heads' tails' where "encode'_tuple_heads vs bst = Ok (heads', tails')"
      using Cons Bss False by(auto split:sum.split_asm)

    then show ?thesis using Cons Bss False Aenc
      using foldl_plus
      by(auto simp add:list_sum_def)
  qed
qed

(* lengths of tails produced by encode'_tuple_tails
   don't depend on headlen and len_total *)
lemma encode'_tuple_tails_lengths :
  "encode'_tuple_tails vs headlen len_total = Ok bvs \<Longrightarrow>
   encode'_tuple_tails vs headlen' len_total' = Ok bvs' \<Longrightarrow>
   (map (\<lambda> (i, l) . length l) bvs) = (map (\<lambda> (i, l) . length l) bvs')"
proof(induction vs arbitrary: headlen len_total bvs headlen' len_total' bvs')
  case Nil
  then show ?case by(auto)
next
  case (Cons a vs)
  then show ?case 
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case False
    then obtain ts1 where Ts1 : "encode'_tuple_tails vs headlen len_total = Ok ts1"
      using Cons
      by (auto split:sum.split_asm)
    obtain ts2 where Ts2 : "encode'_tuple_tails vs headlen' len_total' = Ok ts2"
      using Cons False
      by (auto split:sum.split_asm)

    show ?thesis using Cons.prems Cons.IH[OF Ts1 Ts2] False Ts1 Ts2
      by auto
  next

    case True
    then obtain aenc where Aenc : "encode' a = Ok aenc"
      using Cons by(auto simp del:encode'.simps split:sum.split_asm)

    obtain ts1 where Ts1 : "encode'_tuple_tails vs headlen (len_total + int (length aenc)) = Ok ts1"
      using Cons True Aenc
      by (auto split:sum.split_asm)

    obtain ts2 where Ts2 : "encode'_tuple_tails vs headlen' (len_total' + int (length aenc)) = Ok ts2"
      using Cons True Aenc
      by (auto split:sum.split_asm)

    show ?thesis using Cons.prems Cons.IH[OF Ts1 Ts2] True Aenc Ts1 Ts2
      by(auto simp del: encode'.simps split:if_split_asm)
  qed
qed

(* if encode'_tuple_tails succeeds,
   we can encode all dynamic data *)
lemma encode'_tuple_tails_dyn_success:
  "encode'_tuple_tails l x heads_len = Ok bvs \<Longrightarrow>
   v \<in> set l \<Longrightarrow>
   abi_type_isdynamic (abi_get_type v) \<Longrightarrow>
   (\<exists> code . encode' v = Ok code)"
proof(induction l arbitrary: x heads_len bvs v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case False
    then obtain ts where Ts : "encode'_tuple_tails l x heads_len = Ok ts"
      using Cons 
      by(auto simp del:encode'.simps split:sum.split_asm)
    show ?thesis using Cons False Ts
      by(auto simp del:encode'.simps) 
  next
    case True
    then obtain aenc where Aenc : "encode' a = Ok aenc"
      using Cons by(auto simp del:encode'.simps split:sum.split_asm)

    then obtain ts where Ts : "encode'_tuple_tails l x (heads_len + int (length aenc)) = Ok ts"
      using Cons True
      by(auto simp del:encode'.simps split:sum.split_asm)

    then show ?thesis using Cons True Aenc Ts by(auto simp del:encode'.simps)
  qed
qed

(* if encode'_tuple_heads succeeds, we can encode all static data *)
lemma encode'_tuple_heads_static_success :
  "encode'_tuple_heads l bss = Ok (hs, ts) \<Longrightarrow>
   v \<in> set l \<Longrightarrow>
   abi_type_isstatic (abi_get_type v) \<Longrightarrow>
   (\<exists> code . encode' v = Ok code)"
proof(induction l arbitrary: bss hs ts v)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then obtain ofh ench bst where Bss : "bss = (ofh, ench) # bst"
    by(cases bss; auto)
  show ?case
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case True
    then obtain heads' tails' where Tenc : "encode'_tuple_heads l bst = Ok (heads', tails')"
      using Cons Bss by(auto split:sum.split_asm)
    then show ?thesis using Cons Bss True by(auto)
  next
    case False
    then obtain aenc where Aenc : "encode_static a = Ok aenc"
      using Cons Bss by(auto split:sum.split_asm)
    then obtain heads' tails' where Tenc : "encode'_tuple_heads l bst = Ok (heads', tails')"
      using Cons Bss False by(auto split:sum.split_asm)

    then show ?thesis using Cons Bss Aenc False by(auto)
  qed
qed


lemma heads_length_nonneg :
  "0 \<le> heads_length l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    by(simp add: Let_def abi_static_size_nonneg split:if_split_asm)
qed

(* if encode'_tuple_tails suceeds wbith a given heads-length
   it will also succeed with a smaller heads-length *)
lemma encode'_tuple_tails_dyn_offset:
  "encode'_tuple_tails l (0 :: int) heads_len = Ok bvs \<Longrightarrow>
   0 \<le> heads_len' \<Longrightarrow>
   heads_len' \<le> heads_len \<Longrightarrow>
   (\<exists> bvs' . encode'_tuple_tails l (0 :: int) heads_len' = Ok bvs')"
proof(induction l arbitrary: heads_len bvs heads_len')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case False
    then obtain ts where Ts : "encode'_tuple_tails l 0 heads_len = Ok ts"
      using Cons
      by(auto split: sum.split_asm)
    then show ?thesis using Cons.prems Cons.IH[OF Ts, of heads_len'] False
      by(auto)
  next
    case True
    then obtain aenc where Aenc : "encode' a = Ok aenc"
      using Cons
      by(auto split: sum.split_asm)

    then obtain ts where Ts : "encode'_tuple_tails l 0 (heads_len + int (length aenc)) = Ok ts"
      using Cons True
      by(auto split: sum.split_asm)

    then show ?thesis using Cons.prems Cons.IH[OF Ts, of "heads_len' + int (length aenc)"] 
                            True Aenc Ts
      by(auto simp add:sint_value_valid_def simp del:encode'.simps split:if_split_asm)
  qed
qed

(* for lists of static data, encode'_tuple_heads will
   return static encodings *)
lemma encode'_tuple_heads_static  :
  "encode'_tuple_heads l bvs = Ok (hs, ts) \<Longrightarrow>
   list_all (abi_type_isstatic o abi_get_type) l \<Longrightarrow>
   (\<exists> hss . those_err (map encode_static l) = Ok hss \<and> concat hss = hs)"
proof(induction l arbitrary: bvs hs ts)
  case Nil
  then show ?case
    by(cases bvs; auto)
next
  case (Cons a l)
  then obtain ofh ench bvt where Bss : "bvs = (ofh, ench) # bvt"
    by(cases bvs; auto)

  then obtain aenc where Aenc : "encode_static a = Ok aenc"
    using Cons by(auto split:sum.split_asm)

  then obtain heads' tails' where Tenc : "encode'_tuple_heads l bvt = Ok (heads', tails')"
    using Cons Bss by(auto split:sum.split_asm)

  then show ?case using Cons.prems Cons.IH[OF Tenc] Bss Aenc
    by(auto)
qed

(* for lists of static data, encode'_tuple_tails will not produce tail data *)
lemma encode'_tuple_tails_static :
  "encode'_tuple_tails l x heads_len = Ok bvs \<Longrightarrow>
   list_all (abi_type_isstatic o abi_get_type) l \<Longrightarrow>
   list_all (\<lambda> bv . \<exists> offset . bv = (offset, [])) bvs"
proof(induction l arbitrary: x heads_len bvs)
  case Nil
  then show ?case by simp
next
  case (Cons a l)
  then show ?case
    by(cases bvs; auto split:sum.split_asm prod.split_asm)
qed

(* dynamic size bound agrees with static size (for static values) *)
lemma abi_dynamic_size_bound_static :
  "abi_type_isstatic (abi_get_type v) \<Longrightarrow>
   abi_dynamic_size_bound v = abi_static_size (abi_get_type v)"
  by(simp)

(* dynamic size bound agrees with static size
   (for lists of) static values) *)
lemma abi_dynamic_size_bound_static_list :
"list_sum (map abi_dynamic_size_bound l) = i \<Longrightarrow>
 list_all (abi_type_isstatic o abi_get_type) l \<Longrightarrow>
 list_sum (map (abi_static_size o abi_get_type) l) = i"
proof(induction l arbitrary: i)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  have Astatic : "abi_type_isstatic (abi_get_type a)"
    using Cons by auto
  show ?case using Cons.prems Cons.IH[OF refl]
                   abi_dynamic_size_bound_static[OF Astatic]
                   foldl_plus[of "(abi_static_size (abi_get_type a))" 0
                                 "(map abi_dynamic_size_bound l)"]
                   foldl_plus[of "(abi_static_size (abi_get_type a))" 0
                                 "(map (abi_static_size \<circ> abi_get_type) l)"]
    unfolding list_sum_def
    by(simp del: abi_dynamic_size_bound.simps)
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

lemma length_concat_list_sum :
  "int (length (concat l)) = list_sum (map (int o length) l)"
proof(induction l)
  case Nil
  then show ?case
    by (auto simp add:list_sum_def)
next
  case (Cons a l)
  then show ?case using foldl_plus
    by(auto simp add:list_sum_def)
qed

        
(* abi_dynamic_size_bound bounds encoding size *)
(* TODO: make this look more like encode_static_size' *)
lemma abi_dynamic_size_bound_correct' :
  shows "(\<And> bound code .
              encode v = Ok code \<Longrightarrow>
              abi_dynamic_size_bound v = bound \<Longrightarrow>
              abi_value_valid v \<Longrightarrow>
              length code \<le> bound)" and
        "\<And> t n v ts code  .
          (v = (Vfarray t n vs) \<Longrightarrow>
            encode v = Ok code \<Longrightarrow>
            abi_value_valid v \<Longrightarrow>
            length code \<le> n * 32 + list_sum (map abi_dynamic_size_bound vs)) &&&
          (v = (Vtuple ts vs) \<Longrightarrow>
            encode v = Ok code \<Longrightarrow>
            abi_value_valid v \<Longrightarrow>
            length code \<le> (length vs * 32) + list_sum (map abi_dynamic_size_bound vs)) &&&
          (v = (Varray t vs) \<Longrightarrow>
           encode v = Ok code \<Longrightarrow>
           abi_value_valid v \<Longrightarrow>
           length code \<le> 32 + (length vs * 32) + list_sum (map abi_dynamic_size_bound vs))"
proof(induction v and vs rule: my_abi_value_induct)
  (* Vuint *)
  case (1 n i)
  then show ?case using encode_static_size[of "Vuint n i"]
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vsint *)
  case (2 n i)
  then show ?case using encode_static_size[of "Vsint n i"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vaddr *)
  case (3 i)
  then show ?case using encode_static_size[of "Vaddr i"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vbool *)
  case (4 b)
  then show ?case using encode_static_size[of "Vbool b"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vfixed *)
  case (5 m n r)
  then show ?case using encode_static_size[of "Vfixed m n r"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vufixed *)
  case (6 m n r)
  then show ?case using encode_static_size[of "Vufixed m n r"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vfbytes *)
  case (7 n bs)
  then show ?case using encode_static_size[of "Vfbytes n bs"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vfunction *)
  case (8 i j)
  then show ?case using encode_static_size[of "Vfunction i j"] 
    by(auto simp add:encode_def simp del:encode_static.simps)
next
  (* Vfarray *)
  case (9 t n l)
  show ?case
  proof(cases "abi_type_isstatic (Tfarray t n)")
    case True
    then show ?thesis using "9.prems" "9.IH"(1)[OF refl "9.prems"(1)]
                            encode_static_size[of "Vfarray t n l"]
        by(auto simp add:encode_def)
  next
    case False
    hence "abi_dynamic_size_bound (Vfarray t (length l) l) = 
          int (length l) * 32 + list_sum (map abi_dynamic_size_bound l)" 
      using abi_dynamic_size_bound_static_list
      by(auto )
    then show ?thesis using "9.prems" 
      "9.IH"(1)[OF refl "9.prems"(1)] False
      by(auto simp add:farray_value_valid_aux_def list_all_iff split:sum.splits prod.splits 
              simp del:encode_static.simps abi_dynamic_size_bound.simps)
  qed
next
  (* Vtuple *)
  (* case split on static *)
  case (10 ts vs)
  show ?case
  proof(cases "abi_type_isstatic (Ttuple ts)")
    case True
    then show ?thesis using "10.prems" "10.IH"(2)[OF refl "10.prems"(1)]
                            encode_static_size[of "Vtuple ts vs"]
      by(auto simp add:encode_def)
  next
    case False
    hence "abi_dynamic_size_bound (Vtuple ts vs) =
           int (length vs) * 32 + list_sum (map abi_dynamic_size_bound vs)"
      using abi_dynamic_size_bound_static_list
      by(auto )
    then show ?thesis using "10.prems" "10.IH"(2)[OF refl "10.prems"(1)] False
      by(auto simp add:tuple_value_valid_aux_def list_all_iff split:sum.splits prod.splits 
              simp del:encode_static.simps abi_dynamic_size_bound.simps)
  qed
next
  (* Vbytes *)
  case (11 bs)
  obtain dv rem where DivMod: "divmod_nat (length bs) 32 = (dv, rem)"
    by(cases "divmod_nat (length bs) 32"; auto)
  then show ?case 
  proof(cases rem)
    case 0
    then show ?thesis using 11 DivMod
      by(auto simp add:bytes_value_valid_def encode_def uint_value_valid_def
                       word_rsplit_def bin_rsplit_len)
  next
    case (Suc rem')
    then show ?thesis using 11 DivMod
      by(auto simp add:bytes_value_valid_def encode_def uint_value_valid_def
                       word_rsplit_def bin_rsplit_len)
  qed
next
  (* Vstring *)
  case (12 s)
  obtain dv rem where DivMod: "divmod_nat (length s) 32 = (dv, rem)"
    by(cases "divmod_nat (length s) 32"; auto)
  then show ?case 
  proof(cases rem)
    case 0
    then show ?thesis using 12 DivMod
      by(auto simp add: Let_def string_value_valid_def encode_def uint_value_valid_def
                        word_rsplit_def bin_rsplit_len)
  next
    case (Suc nat)
    then show ?thesis using 12 DivMod
      by(auto simp add: Let_def string_value_valid_def encode_def uint_value_valid_def
                        word_rsplit_def bin_rsplit_len)
  qed
next
  (* Varray *)
  case (13 t vs)
  hence "abi_dynamic_size_bound (Varray t vs) =
           int (32 + length vs * 32) + list_sum (map abi_dynamic_size_bound vs)"
    using abi_dynamic_size_bound_static_list
    by(auto )

  then show ?case using "13.prems" "13.IH"(3)[OF refl "13.prems"(1)] 
    by(auto simp add:tuple_value_valid_aux_def list_all_iff split:sum.splits prod.splits 
            simp del:encode_static.simps abi_dynamic_size_bound.simps)
next
  (* Nil *)
  case 14
  {
    (* Vfarray *)
    case (1 t n)
    then show ?case
      by(cases "abi_type_isdynamic (Tfarray t n)";
         auto simp add:encode_def list_sum_def)
  next
    (* Vtuple *)
    case (2 ts)
    then show ?case
      by(cases "abi_type_isdynamic (Ttuple ts)";
         auto simp add:encode_def list_sum_def)
  next
    (* Varray *)
    case (3 t)
    then show ?case
      by(auto simp add:encode_def farray_value_valid_aux_def list_sum_def
                       word_rsplit_def bin_rsplit_len)
  }
next
  (* Cons *)
  case (15 vh vt)
  {
    (* Vfarray *)
    case (1 t n v) 
    then show ?case
    proof(cases "abi_type_isdynamic t")
      case False
      then obtain vhenc where Vhenc : "encode_static vh = Ok vhenc"
        using 1
        by(cases "encode_static vh"; auto simp add:encode_def)

      have Vh_static : "\<not> abi_type_isdynamic (abi_get_type vh)"
        using 1 False
        by(auto simp add:list_all_iff farray_value_valid_aux_def)

      hence Vhenc' : "encode vh = Ok vhenc" using 1 False Vhenc
        by(auto simp add:encode_def list_all_iff farray_value_valid_aux_def)

      have Vt_static : "list_all (abi_type_isstatic \<circ> abi_get_type) vt "
        using 1 False
        by(auto simp add:list_all_iff farray_value_valid_aux_def)

      have Vh_valid : "abi_value_valid (vh)"
        using 1 by(auto simp add:farray_value_valid_aux_def)

      obtain vtenc where Vtenc : "those_err (map encode_static vt) = Ok vtenc"
        using 1 Vhenc False
        by(cases "those_err (map encode_static vt)"; auto simp add:encode_def)

      have Vtenc' : "encode (Vfarray t (n - 1) vt) = Ok (concat vtenc)"
        using 1 False Vhenc' Vtenc
        by(auto simp add:encode_def farray_value_valid_aux_def split:sum.splits)

      have Vt_valid : "abi_value_valid (Vfarray t (n - 1) vt)"
        using 1 False
        by(auto simp add:encode_def farray_value_valid_aux_def split:sum.splits)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_static_size (abi_get_type vh)))"
        using abi_dynamic_size_bound_static[of vh] Vh_static
              abi_static_size_nonneg[of "abi_get_type vh"] by(auto)

      have Code : "code = vhenc @ concat vtenc"
        using Vtenc Vhenc 1 False by(auto simp add:encode_def)

      show ?thesis using 1 False Vhenc Vtenc Code 
                              "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
                              "15.IH"(2)[OF refl Vtenc' Vt_valid]
                              abi_dynamic_size_bound_static[of vh] Vh_static
                              abi_dynamic_size_bound_static_list[of vt, OF refl] Vt_static
                              length_concat_list_sum[of vtenc]
                              abi_static_size_nonneg[of "abi_get_type vh"]
                              sym[OF foldl_plus[of "(abi_static_size (abi_get_type vh))" 0]]
          by(auto simp add:encode_def list_sum_def 
                     simp del:abi_dynamic_size_bound.simps)
    next
      case True

      have Vh_dyn : "abi_type_isdynamic (abi_get_type vh)"
        using 1 True
        by(auto simp add:list_all_iff farray_value_valid_aux_def)

      obtain vhenc where Vhenc : "encode' vh = Ok vhenc" using 1 True Vh_dyn
        by(cases "encode' vh"; auto simp add:encode_def )

      hence Vhenc' : "encode vh = Ok vhenc" using Vh_dyn 1
        by(auto simp add:encode_def farray_value_valid_aux_def)

      have Vh_valid : "abi_value_valid vh" using 1
        by(auto simp add:encode_def farray_value_valid_aux_def)

      have Vt_dyn : "list_all (abi_type_isdynamic \<circ> abi_get_type) vt"
        using 1 True
        by(auto simp add:list_all_iff farray_value_valid_aux_def)

      have Vt_valid : "abi_value_valid (Vfarray t (n - 1) vt)"
        using 1 True
        by(auto simp add:list_all_iff farray_value_valid_aux_def)

      obtain vt_tailenc where
        Vt_tailenc : "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc)) = 
                      Ok vt_tailenc" using 1 True Vh_dyn Vhenc
        by(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc))";
            auto simp add:encode_def)
        
      have Len_valid : "sint_value_valid 256 (32 + heads_length vt)"
        using 1 True Vh_dyn Vhenc Vt_tailenc
        by(cases "sint_value_valid 256 (32 + heads_length vt)";
            auto simp add:encode_def)

      obtain vt_heads vt_tails where
        Vt_headenc : "encode'_tuple_heads vt vt_tailenc = Ok (vt_heads, vt_tails)"
        using 1 True Vh_dyn Vhenc Vt_tailenc Len_valid
        by(cases "encode'_tuple_heads vt vt_tailenc";
            auto simp add:encode_def)

      have Heads_len_valid :
        "sint_value_valid 256 (32 + heads_length vt)"
        using 1 True Vh_dyn Vhenc Vt_tailenc Len_valid Vt_headenc
        by(cases "sint_value_valid 256 (32 + heads_length vt)";
           auto simp add:encode_def)

      have Code :
        "code = encode_int (32 + heads_length vt) @ vt_heads @ vhenc @ vt_tails"
        using 1 True Vh_dyn Vhenc Vt_tailenc Len_valid Vt_headenc 
        by(auto simp add:encode_def)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
        using abi_dynamic_size_bound_nonneg[of vh] by(auto)

      obtain vt_tailenc_small where
        Vt_tailenc_small :
        "encode'_tuple_tails vt 0 (heads_length vt) = Ok (vt_tailenc_small)"
        using encode'_tuple_tails_dyn_offset[OF Vt_tailenc, of "heads_length vt"]
        heads_length_nonneg[of vt]
        by auto

      have Tailenc_len_eq :
        "length vt = length vt_tailenc_small"
        using encode'_tuple_tails_len[OF Vt_tailenc_small]
        by auto

      then show ?thesis
      proof(cases "encode'_tuple_heads vt vt_tailenc_small")
        case (Inr err)
        obtain vbad vbad_err where Vbad_in : "vbad \<in> set vt" and 
                                   Vbad_bad : "encode' vbad = Err vbad_err"
          using encode'_tuple_heads_fail[OF Inr Tailenc_len_eq]
          by auto
        hence Vbad_dyn : "abi_type_isdynamic (abi_get_type vbad)"
          using 1 True
          by(auto simp add:list_all_iff farray_value_valid_aux_def)

        hence False using encode'_tuple_tails_dyn_success[OF Vt_tailenc_small Vbad_in Vbad_dyn]
                         Vbad_bad by auto

        thus ?thesis by auto
      next
        case (Inl vtht_small)
        then obtain vt_heads_small vt_tails_small
          where Vtht_small : "vtht_small = (vt_heads_small, vt_tails_small)" 
          by (cases vtht_small; auto)
        
        hence Vtenc' : "encode (Vfarray t (n - 1) vt) = Ok (vt_heads_small @ vt_tails_small )"
          using 1 True Vt_tailenc_small Vhenc' Vt_tailenc Vt_headenc Inl
          by(auto simp add:encode_def farray_value_valid_aux_def )

        have Enc32 : "length (encode_int (32 + heads_length vt)) = 32"
          by(auto simp add: word_rsplit_def bin_rsplit_len)


        have Vt_valid' : "list_all abi_value_valid vt"
          using Vt_valid unfolding abi_value_valid.simps
          by(auto simp add:farray_value_valid_aux_def list_all_iff)

        have Vt_heads_small_eq : "length (vt_heads) = length (vt_heads_small)"
          using encode'_tuple_heads_headslength[of vt vt_tailenc_small vt_heads_small
                                                   vt_tails_small] Inl Vtht_small
                encode'_tuple_heads_headslength[OF Vt_headenc]
                Vt_valid'
          by(auto simp add:farray_value_valid_aux_def)


        have Vt_tails_small_eq : "length (vt_tails) = length (vt_tails_small)"
          using encode'_tuple_heads_len2[of vt vt_tailenc_small vt_heads_small
                                            vt_tails_small] 
                encode'_tuple_heads_len2[OF Vt_headenc] Inl Vtht_small
                encode'_tuple_tails_lengths[OF Vt_tailenc_small Vt_tailenc]
          by(auto)
        
        have N_nz : "0 < n" using 1 by (auto simp add:farray_value_valid_aux_def)

        show ?thesis using  1 True Vhenc  Vh_dyn Vt_tailenc Vt_headenc Code
            "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
            "15.IH"(2)[OF refl Vtenc' Vt_valid]
            Enc32 abi_dynamic_size_bound_nonneg[of vh] N_nz
            Vt_heads_small_eq Vt_tails_small_eq
            sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
          unfolding list_sum_def
          by(auto simp add:encode_def simp del: abi_dynamic_size_bound.simps)
      qed 
    qed
  next
    (* Vtuple *)
    case (2 ts vs)
    then obtain th tt where Ts : "ts = th # tt"
      by(auto simp add:tuple_value_valid_aux_def)

    show ?case
    proof(cases "abi_type_isdynamic (Ttuple ts)")
      case False
      then obtain vhenc where Vhenc : "encode_static vh = Ok vhenc"
        using 2
        by(cases "encode_static vh"; auto simp add:encode_def)

      have Vh_static : "\<not> abi_type_isdynamic (abi_get_type vh)"
        using 2 False
        by(auto simp add:list_all_iff tuple_value_valid_aux_def)

      hence Vhenc' : "encode vh = Ok vhenc" using 2 False Vhenc
        by(auto simp add:encode_def list_all_iff tuple_value_valid_aux_def)

      have Vt_static : "list_all (abi_type_isstatic \<circ> abi_get_type) vt "
        using 2 False
        by(auto simp add:list_all_iff list_ex_iff tuple_value_valid_aux_def)

      have Vh_valid : "abi_value_valid (vh)"
        using 2 by(auto simp add:tuple_value_valid_aux_def)

      obtain vtenc where Vtenc : "those_err (map encode_static vt) = Ok vtenc"
        using 2 Vhenc False
        by(cases "those_err (map encode_static vt)"; auto simp add:encode_def)

      have Vtenc' : "encode (Vtuple tt vt) = Ok (concat vtenc)"
        using 2 False Vhenc' Vtenc Ts
        by(auto simp add:encode_def tuple_value_valid_aux_def split:sum.splits)

      have Vt_valid : "abi_value_valid (Vtuple tt vt)"
        using 2 False Ts
        by(auto simp add:encode_def tuple_value_valid_aux_def split:sum.splits)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_static_size (abi_get_type vh)))"
        using abi_dynamic_size_bound_static[of vh] Vh_static
              abi_static_size_nonneg[of "abi_get_type vh"] by(auto)

      have Code : "code = vhenc @ concat vtenc"
        using Vtenc Vhenc 2 False by(auto simp add:encode_def)

      show ?thesis using 2 False Vhenc Vtenc Code 
                              "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
                              "15.IH"(3)[OF refl Vtenc' Vt_valid]
                              abi_dynamic_size_bound_static[of vh] Vh_static
                              abi_dynamic_size_bound_static_list[of vt, OF refl] Vt_static
                              length_concat_list_sum[of vtenc]
                              abi_static_size_nonneg[of "abi_get_type vh"]
                              sym[OF foldl_plus[of "(abi_static_size (abi_get_type vh))" 0]]
          by(auto simp add:encode_def list_sum_def 
                     simp del:abi_dynamic_size_bound.simps)
    next
      case True
      show ?thesis
      proof(cases "abi_type_isstatic (abi_get_type vh)")
        assume True' : "abi_type_isstatic (abi_get_type vh)"

        obtain vt_tailenc where Vt_tailenc :
          "encode'_tuple_tails vt 0 (abi_static_size (abi_get_type vh) + heads_length vt) =
           Ok vt_tailenc" using 2 True True' Ts
          by(cases "encode'_tuple_tails vt 0 (abi_static_size (abi_get_type vh) + heads_length vt)";
             auto simp add:encode_def)

        then obtain vhenc where Vhenc : "encode_static vh = Ok vhenc"
          using 2 True True' Ts
          by(cases "encode_static vh"; auto simp add:encode_def)

        hence Vhenc' : "encode vh = Ok vhenc" using 2 True'
          by(auto simp add:encode_def list_all_iff tuple_value_valid_aux_def)

        have Vh_valid : "abi_value_valid vh" using 2
          by(auto simp add:encode_def tuple_value_valid_aux_def)
  
        have Vt_dyn : "list_ex (abi_type_isdynamic \<circ> abi_get_type) vt"
          using 2 True True' Ts
          by(auto simp add:list_all_iff list_ex_iff tuple_value_valid_aux_def)
  
        have Vt_valid : "abi_value_valid (Vtuple tt vt)"
          using 2 True True' Ts
          by(auto simp add:list_all_iff list_ex_iff tuple_value_valid_aux_def)

        obtain vt_tailenc where
          Vt_tailenc : "encode'_tuple_tails vt 0 
                        (abi_static_size (abi_get_type vh) + heads_length vt) = 
                        Ok vt_tailenc" using 2 True True' Vhenc' Vh_valid
          by(cases "encode'_tuple_tails vt 0 
                        (abi_static_size (abi_get_type vh) + heads_length vt)";
                auto simp add:encode_def)

        obtain vt_heads vt_tails where
          Vt_headenc : "encode'_tuple_heads vt vt_tailenc = Ok (vt_heads, vt_tails)"
          using 2 True True' Vhenc Vt_tailenc
          by(cases "encode'_tuple_heads vt vt_tailenc";
              auto simp add:encode_def)

        have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_static_size (abi_get_type vh)))"
          using abi_dynamic_size_bound_static[of vh] True'
                abi_static_size_nonneg[of "abi_get_type vh"] by(auto)

        obtain vt_tailenc_small where
          Vt_tailenc_small :
          "encode'_tuple_tails vt 0 (heads_length vt) = Ok (vt_tailenc_small)"
          using encode'_tuple_tails_dyn_offset[OF Vt_tailenc, of "heads_length vt"]
          heads_length_nonneg[of vt]
          abi_static_size_nonneg[of "abi_get_type vh"]
          by(auto)

        have Tailenc_len_eq :
          "length vt = length vt_tailenc_small"
          using encode'_tuple_tails_len[OF Vt_tailenc_small]
          by auto
  
        then show ?thesis
        proof(cases "encode'_tuple_heads vt vt_tailenc_small")
          case (Inr err)
          obtain vbad vbad_err where Vbad_in : "vbad \<in> set vt" and 
                                     Vbad_bad : "encode' vbad = Err vbad_err"
            using encode'_tuple_heads_fail[OF Inr Tailenc_len_eq]
            by auto
  
          thus ?thesis
          proof(cases "abi_type_isdynamic (abi_get_type vbad)")
            case False
  
            have False using encode'_tuple_heads_static_success[OF Vt_headenc Vbad_in]
              False Vbad_bad by auto
            
            then show ?thesis by auto
          next
            case True
            have False using encode'_tuple_tails_dyn_success[OF Vt_tailenc_small Vbad_in]
              True Vbad_bad by auto

            thus ?thesis by auto
          qed
        next
          case (Inl vtht_small)
          
          then obtain vt_heads_small vt_tails_small
          where Vtht_small : "vtht_small = (vt_heads_small, vt_tails_small)" 
          by (cases vtht_small; auto)
        
          hence Vtenc' : "encode (Vtuple tt vt) = Ok (vt_heads_small @ vt_tails_small )"
            using 2 True True' Ts Vt_tailenc_small Vt_dyn Vhenc Vt_tailenc Vt_headenc Inl
            by(auto simp add:encode_def tuple_value_valid_aux_def )
  
          have Enc32 : "length (encode_int (32 + heads_length vt)) = 32"
            by(auto simp add: word_rsplit_def bin_rsplit_len)
  
  
          have Vt_valid' : "list_all abi_value_valid vt"
            using Vt_valid unfolding abi_value_valid.simps
            by(auto simp add:tuple_value_valid_aux_def list_all_iff)
  
          have Vt_heads_small_eq : "length (vt_heads) = length (vt_heads_small)"
            using encode'_tuple_heads_headslength[of vt vt_tailenc_small vt_heads_small
                                                     vt_tails_small] Inl Vtht_small
                  encode'_tuple_heads_headslength[OF Vt_headenc]
                  Vt_valid'
            by(auto simp add:farray_value_valid_aux_def)
  
  
          have Vt_tails_small_eq : "length (vt_tails) = length (vt_tails_small)"
            using encode'_tuple_heads_len2[of vt vt_tailenc_small vt_heads_small
                                              vt_tails_small] 
                  encode'_tuple_heads_len2[OF Vt_headenc] Inl Vtht_small
                  encode'_tuple_tails_lengths[OF Vt_tailenc_small Vt_tailenc]
            by(auto)
            
          show ?thesis using  2 True True' Vhenc Vt_tailenc Vt_headenc 
              "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
              "15.IH"(3)[OF refl Vtenc' Vt_valid]
              Enc32 abi_dynamic_size_bound_nonneg[of vh] 
              abi_dynamic_size_bound_static[of vh]
              Vt_heads_small_eq Vt_tails_small_eq
              sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
            unfolding list_sum_def
            by(auto simp add:encode_def simp del: abi_dynamic_size_bound.simps)
        qed 
      next
        assume False' : "\<not> abi_type_isstatic (abi_get_type vh)"

        show ?thesis
        proof(cases "abi_type_isstatic (Ttuple tt)")
          assume True'' : "abi_type_isstatic (Ttuple tt)"

          obtain vhenc where Vhenc : "encode' vh = Ok vhenc" using 2 True False' True''
            by(cases "encode' vh"; auto simp add:encode_def )
    
          hence Vhenc' : "encode vh = Ok vhenc" using True'' 2
            by(auto simp add:encode_def tuple_value_valid_aux_def)
    
          have Vh_valid : "abi_value_valid vh" using 2
            by(auto simp add:encode_def tuple_value_valid_aux_def)
   
          have Vt_static : "list_all (abi_type_isstatic \<circ> abi_get_type) vt "
            using 2 True'' Ts
            by(auto simp add:list_all_iff list_ex_iff tuple_value_valid_aux_def)

          have Vt_valid : "abi_value_valid (Vtuple tt vt)"
            using 2 True False' True'' Ts
            by(auto simp add:encode_def tuple_value_valid_aux_def split:sum.splits)

          obtain vtenc where Vtenc : "encode'_tuple_tails vt 0 
                                        (32 + heads_length vt + int (length vhenc))
                                          = Ok vtenc"

            using 2 Vhenc False' Ts
            by(cases "encode'_tuple_tails vt 0 
                                        (32 + heads_length vt + int (length vhenc))";
                auto simp add:encode_def tuple_value_valid_aux_def)


          have Heads_len_valid : "sint_value_valid 256 (32 + heads_length vt)"
            using 2 Vhenc Vtenc False' Ts
            by(cases "sint_value_valid 256 (32 + heads_length vt)";
                      auto simp add:encode_def tuple_value_valid_aux_def)

          obtain vt_heads vt_tails where Vt_headenc :
            "encode'_tuple_heads vt vtenc = Ok (vt_heads, vt_tails)"
            using 2 Vhenc Vtenc False' Ts Heads_len_valid
            by(cases "encode'_tuple_heads vt vtenc";
                      auto simp add:encode_def tuple_value_valid_aux_def)

          have Enc32 : "length (encode_int (32 + heads_length vt)) = 32"
            by(auto simp add: word_rsplit_def bin_rsplit_len)

          have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
            using abi_dynamic_size_bound_nonneg[of "vh"] by(auto)

          obtain vtenc_static where Vtenc_static : 
                       "those_err (map encode_static vt) = Ok vtenc_static"
                       and Vtenc_concat : "concat vtenc_static = vt_heads"
            using encode'_tuple_heads_static[OF Vt_headenc Vt_static]
            by(auto)

          hence Vtenc' : "encode (Vtuple tt vt) = Ok (concat vtenc_static)"
            using Vt_static Vt_valid 2
            by(auto simp add: tuple_value_valid_aux_def encode_def list_all_iff list_ex_iff)


          have "list_all (\<lambda>x. x = 0) (map int (map (\<lambda>(i, y). length y) vtenc))"
            using encode'_tuple_tails_static[OF Vtenc Vt_static]
            by(auto simp add:list_all_iff)

          hence Vt_tails_empty : "length vt_tails = 0"
            using encode'_tuple_heads_len2[OF Vt_headenc]
                  list_sum_zero[of "(map int (map (\<lambda>(i, y). length y) vtenc))"]
              by(auto simp add:list_all_iff split:prod.splits)
          
          show ?thesis using 2 True False' True'' 
                              Vtenc Vhenc Heads_len_valid Vt_headenc
                              Enc32 Vtenc_concat Vt_tails_empty
                              "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
                              "15.IH"(3)[OF refl Vtenc' Vt_valid]
                              abi_dynamic_size_bound_nonneg[of vh]
                              sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
            by(auto simp add:encode_def list_sum_def simp del: abi_dynamic_size_bound.simps)
        next
          assume False'' : "\<not> abi_type_isstatic (Ttuple tt)"

          obtain vhenc where Vhenc : "encode' vh = Ok vhenc" using 2 True False'
            by(cases "encode' vh"; auto simp add:encode_def )
    
          hence Vhenc' : "encode vh = Ok vhenc" using 2 False'
            by(auto simp add:encode_def tuple_value_valid_aux_def)
    
          have Vh_valid : "abi_value_valid vh" using 2
            by(auto simp add:encode_def tuple_value_valid_aux_def)
    
          have Vt_dyn : "list_ex (abi_type_isdynamic \<circ> abi_get_type) vt"
            using 2 False'' Ts
            by(auto simp add:list_all_iff list_ex_iff tuple_value_valid_aux_def)
    
          have Vt_valid : "abi_value_valid (Vtuple tt vt)"
            using 2 Ts
            by(auto simp add:list_all_iff tuple_value_valid_aux_def)
    
          obtain vt_tailenc where
            Vt_tailenc : "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc)) = 
                          Ok vt_tailenc" using 2 False' False'' Vhenc Ts
            by(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc))";
                auto simp add:encode_def)
            
          have Len_valid : "sint_value_valid 256 (32 + heads_length vt)"
            using 2 True False' Vhenc Vt_tailenc
            by(cases "sint_value_valid 256 (32 + heads_length vt)";
                auto simp add:encode_def)
    
          obtain vt_heads vt_tails where
            Vt_headenc : "encode'_tuple_heads vt vt_tailenc = Ok (vt_heads, vt_tails)"
            using 2 True False' Vhenc Vt_tailenc Len_valid
            by(cases "encode'_tuple_heads vt vt_tailenc";
                auto simp add:encode_def)
    
          have Code :
            "code = encode_int (32 + heads_length vt) @ vt_heads @ vhenc @ vt_tails"
            using 2 True False' Vhenc Vt_tailenc Len_valid Vt_headenc 
            by(auto simp add:encode_def)
    
          have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
            using abi_dynamic_size_bound_nonneg[of vh] by(auto)
    
          obtain vt_tailenc_small where
            Vt_tailenc_small :
            "encode'_tuple_tails vt 0 (heads_length vt) = Ok (vt_tailenc_small)"
            using encode'_tuple_tails_dyn_offset[OF Vt_tailenc, of "heads_length vt"]
            heads_length_nonneg[of vt]
            by auto
    
          have Tailenc_len_eq :
            "length vt = length vt_tailenc_small"
            using encode'_tuple_tails_len[OF Vt_tailenc_small]
            by auto
    
          then show ?thesis
          proof(cases "encode'_tuple_heads vt vt_tailenc_small")
            case (Inr err)
            obtain vbad vbad_err where Vbad_in : "vbad \<in> set vt" and 
                                       Vbad_bad : "encode' vbad = Err vbad_err"
              using encode'_tuple_heads_fail[OF Inr Tailenc_len_eq]
              by auto

            show ?thesis
            proof(cases "abi_type_isstatic (abi_get_type vbad)")
              assume True''' : "abi_type_isstatic (abi_get_type vbad)"

              hence False
                using encode'_tuple_heads_static_success[OF Vt_headenc Vbad_in]
                               Vbad_bad by auto
              thus ?thesis by auto
            next
              assume False''' : "\<not> abi_type_isstatic (abi_get_type vbad)"

              hence False
                using encode'_tuple_tails_dyn_success[OF Vt_tailenc_small Vbad_in ]
                               Vbad_bad by auto
              thus ?thesis by auto
            qed
          next
            case (Inl vtht_small)
            then obtain vt_heads_small vt_tails_small
              where Vtht_small : "vtht_small = (vt_heads_small, vt_tails_small)" 
              by (cases vtht_small; auto)
            
            hence Vtenc' : "encode (Vtuple tt vt) = Ok (vt_heads_small @ vt_tails_small )"
              using 2 True False' False'' Ts Vt_tailenc_small Vhenc'
                    Vt_tailenc Vt_headenc Len_valid Inl
              by(auto simp add:encode_def tuple_value_valid_aux_def )
    
            have Enc32 : "length (encode_int (32 + heads_length vt)) = 32"
              by(auto simp add: word_rsplit_def bin_rsplit_len)
    
            have Vt_valid' : "list_all abi_value_valid vt"
              using Vt_valid unfolding abi_value_valid.simps
              by(auto simp add:tuple_value_valid_aux_def list_all_iff)
    
            have Vt_heads_small_eq : "length (vt_heads) = length (vt_heads_small)"
              using encode'_tuple_heads_headslength[of vt vt_tailenc_small vt_heads_small
                                                       vt_tails_small] Inl Vtht_small
                    encode'_tuple_heads_headslength[OF Vt_headenc]
                    Vt_valid'
              by(auto simp add:farray_value_valid_aux_def)
    
    
            have Vt_tails_small_eq : "length (vt_tails) = length (vt_tails_small)"
              using encode'_tuple_heads_len2[of vt vt_tailenc_small vt_heads_small
                                                vt_tails_small] 
                    encode'_tuple_heads_len2[OF Vt_headenc] Inl Vtht_small
                    encode'_tuple_tails_lengths[OF Vt_tailenc_small Vt_tailenc]
              by(auto)
                
            show ?thesis using 2 True False' False'' Vhenc 
                Vt_tailenc Vt_headenc Len_valid Code
                "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
                "15.IH"(3)[OF refl Vtenc' Vt_valid]
                Enc32 abi_dynamic_size_bound_nonneg[of vh]
                Vt_heads_small_eq Vt_tails_small_eq
                sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
              unfolding list_sum_def
              by(auto simp add:encode_def simp del: abi_dynamic_size_bound.simps)
          qed 
        qed
      qed
    qed
  next
    (* Varray *)
    case 3
    then show ?case
    proof(cases "abi_type_isdynamic t")
      case False

      hence Vh_static : "\<not> abi_type_isdynamic (abi_get_type vh)"
        using 3 False
        by(auto simp add:list_all_iff array_value_valid_aux_def)

      then obtain vt_tailenc where
        Vt_tailenc : 
          "encode'_tuple_tails vt 0 (abi_static_size (abi_get_type vh) + heads_length vt) =
            Ok vt_tailenc" using 3 False
        by(cases "encode'_tuple_tails vt 0 (abi_static_size (abi_get_type vh) + heads_length vt)";
                auto simp add:encode_def)

      then obtain vhenc where Vhenc : "encode_static vh = Ok vhenc"
        using 3 Vh_static
        by(cases "encode_static vh"; auto simp add:encode_def)

      hence Vhenc' : "encode vh = Ok vhenc" using 3 False Vhenc
        by(auto simp add:encode_def list_all_iff array_value_valid_aux_def)

      have Vt_static : "list_all (abi_type_isstatic \<circ> abi_get_type) vt "
        using 3 False
        by(auto simp add:list_all_iff array_value_valid_aux_def)

      have Vt_valid : "abi_value_valid (Varray t vt)"
        using 3 False
        by(auto simp add:list_all_iff array_value_valid_aux_def uint_value_valid_def)

      have Vh_valid : "abi_value_valid (vh)"
        using 3 by(auto simp add:array_value_valid_aux_def)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
        using abi_dynamic_size_bound_nonneg[of vh] by(auto)

      obtain vt_heads vt_tails where
        Vt_headenc : "encode'_tuple_heads vt vt_tailenc = Ok (vt_heads, vt_tails)"
        using 3 False Vh_static Vhenc Vt_tailenc 
        by(cases "encode'_tuple_heads vt vt_tailenc";
            auto simp add:encode_def)

      have Enc32 : "length (encode_int (1 + int (length vt))) = 32"
        by(auto simp add: word_rsplit_def bin_rsplit_len)

      have Enc32' : "length (encode_int (int (length vt))) = 32"
        by(auto simp add: word_rsplit_def bin_rsplit_len)

      have Code :
        "code = encode_int (1 + length vt) @ vhenc @ vt_heads @ vt_tails"
        using 3 False Vh_static Vhenc Vt_tailenc Vt_headenc 
        by(auto simp add:encode_def)

      obtain vt_tailenc_small where
        Vt_tailenc_small :
        "encode'_tuple_tails vt 0 (heads_length vt) = Ok (vt_tailenc_small)"
        using encode'_tuple_tails_dyn_offset[OF Vt_tailenc, of "heads_length vt"]
        abi_static_size_nonneg[of "abi_get_type vh"]
        heads_length_nonneg[of vt]
        by( auto)

      have Len_valid : "uint_value_valid 256 (int (length vt))"
        using 3 by(auto simp add:array_value_valid_aux_def uint_value_valid_def)

      have Tailenc_len_eq :
        "length vt = length vt_tailenc_small"
        using encode'_tuple_tails_len[OF Vt_tailenc_small]
        by auto

      then show ?thesis
      proof(cases "encode'_tuple_heads vt vt_tailenc_small")
        case (Inr err)
        obtain vbad vbad_err where Vbad_in : "vbad \<in> set vt" and 
                                   Vbad_bad : "encode' vbad = Err vbad_err"
          using encode'_tuple_heads_fail[OF Inr Tailenc_len_eq]
          by auto

        show ?thesis
        proof(cases "abi_type_isstatic (abi_get_type vbad)")
          assume True' : "abi_type_isstatic (abi_get_type vbad)"

          hence False
            using encode'_tuple_heads_static_success[OF Vt_headenc Vbad_in]
                           Vbad_bad by auto
          thus ?thesis by auto
        next
          assume False' : "\<not> abi_type_isstatic (abi_get_type vbad)"

          hence False
            using encode'_tuple_tails_dyn_success[OF Vt_tailenc_small Vbad_in ]
                           Vbad_bad by auto
          thus ?thesis by auto
        qed
      next
        case (Inl vtht_small)
        then obtain vt_heads_small vt_tails_small
          where Vtht_small : "vtht_small = (vt_heads_small, vt_tails_small)" 
          by (cases vtht_small; auto)
        
        hence Vtenc' : "encode (Varray t vt) = 
          Ok (encode_int (int (length vt)) @ vt_heads_small @ vt_tails_small )"
          using 3 False Vt_tailenc_small Vhenc' Vt_tailenc Vt_headenc Inl Len_valid
          by(auto simp add:encode_def array_value_valid_aux_def)

        have Vt_valid' : "list_all abi_value_valid vt"
          using Vt_valid unfolding abi_value_valid.simps
          by(auto simp add:array_value_valid_aux_def list_all_iff)

        have Vt_heads_small_eq : "length (vt_heads) = length (vt_heads_small)"
          using encode'_tuple_heads_headslength[of vt vt_tailenc_small vt_heads_small
                                                   vt_tails_small] Inl Vtht_small
                encode'_tuple_heads_headslength[OF Vt_headenc]
                Vt_valid'
          by(auto simp add:farray_value_valid_aux_def)


        have Vt_tails_small_eq : "length (vt_tails) = length (vt_tails_small)"
          using encode'_tuple_heads_len2[of vt vt_tailenc_small vt_heads_small
                                            vt_tails_small] 
                encode'_tuple_heads_len2[OF Vt_headenc] Inl Vtht_small
                encode'_tuple_tails_lengths[OF Vt_tailenc_small Vt_tailenc]
          by(auto)
        
        show ?thesis using  3 False Vhenc Vt_tailenc Vt_headenc
            "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
            "15.IH"(4)[OF refl Vtenc' Vt_valid] Enc32
            Enc32' abi_dynamic_size_bound_nonneg[of vh]
            Vt_heads_small_eq Vt_tails_small_eq Code
            sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
          unfolding list_sum_def
          by(auto simp add:encode_def simp del: abi_dynamic_size_bound.simps)
      qed 
    next
      case True

      have Vh_dyn : "abi_type_isdynamic (abi_get_type vh)"
        using 3 True
        by(auto simp add:list_all_iff array_value_valid_aux_def)

      obtain vhenc where Vhenc : "encode' vh = Ok vhenc" using 3 True Vh_dyn
        by(cases "encode' vh"; auto simp add:encode_def )

      hence Vhenc' : "encode vh = Ok vhenc" using Vh_dyn 3
        by(auto simp add:encode_def array_value_valid_aux_def)

      have Vh_valid : "abi_value_valid vh" using 3
        by(auto simp add:encode_def array_value_valid_aux_def)

      have Vt_dyn : "list_all (abi_type_isdynamic \<circ> abi_get_type) vt"
        using 3 True
        by(auto simp add:list_all_iff array_value_valid_aux_def)

      have Len_valid : "uint_value_valid 256 (int (length vt))"
        using 3 by(auto simp add:array_value_valid_aux_def uint_value_valid_def)

      have Vt_valid : "abi_value_valid (Varray t vt)"
        using 3 True Len_valid
        by(auto simp add:list_all_iff array_value_valid_aux_def)

      obtain vt_tailenc where
        Vt_tailenc : "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc)) = 
                      Ok vt_tailenc" using 3 True Vh_dyn Vhenc
        by(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vhenc))";
            auto simp add:encode_def)
        
      have Len_valid_body : "sint_value_valid 256 (32 + heads_length vt)"
        using 3 True Vh_dyn Vhenc Vt_tailenc
        by(cases "sint_value_valid 256 (32 + heads_length vt)";
            auto simp add:encode_def)

      obtain vt_heads vt_tails where
        Vt_headenc : "encode'_tuple_heads vt vt_tailenc = Ok (vt_heads, vt_tails)"
        using 3 True Vh_dyn Vhenc Vt_tailenc Len_valid_body
        by(cases "encode'_tuple_heads vt vt_tailenc";
            auto simp add:encode_def)

      have Heads_len_valid :
        "sint_value_valid 256 (32 + heads_length vt)"
        using 3 True Vh_dyn Vhenc Vt_tailenc Len_valid Vt_headenc
        by(cases "sint_value_valid 256 (32 + heads_length vt)";
           auto simp add:encode_def)

      have Code :
        "code = encode_int (1 + int (length vt)) @ encode_int (32 + heads_length vt) @ 
                vt_heads @ vhenc @ vt_tails"
        using 3 True Vh_dyn Vhenc Vt_tailenc Len_valid Vt_headenc Heads_len_valid
        by(auto simp add:encode_def)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
        using abi_dynamic_size_bound_nonneg[of vh] by(auto)

      obtain vt_tailenc_small where
        Vt_tailenc_small :
        "encode'_tuple_tails vt 0 (heads_length vt) = Ok (vt_tailenc_small)"
        using encode'_tuple_tails_dyn_offset[OF Vt_tailenc, of "heads_length vt"]
        heads_length_nonneg[of vt]
        by auto

      have Tailenc_len_eq :
        "length vt = length vt_tailenc_small"
        using encode'_tuple_tails_len[OF Vt_tailenc_small]
        by auto

      then show ?thesis
      proof(cases "encode'_tuple_heads vt vt_tailenc_small")
        case (Inr err)
        obtain vbad vbad_err where Vbad_in : "vbad \<in> set vt" and 
                                   Vbad_bad : "encode' vbad = Err vbad_err"
          using encode'_tuple_heads_fail[OF Inr Tailenc_len_eq]
          by auto
        hence Vbad_dyn : "abi_type_isdynamic (abi_get_type vbad)"
          using 3 True
          by(auto simp add:list_all_iff array_value_valid_aux_def)

        hence False using encode'_tuple_tails_dyn_success[OF Vt_tailenc_small Vbad_in Vbad_dyn]
                         Vbad_bad by auto

        thus ?thesis by auto
      next
        case (Inl vtht_small)
        then obtain vt_heads_small vt_tails_small
          where Vtht_small : "vtht_small = (vt_heads_small, vt_tails_small)" 
          by (cases vtht_small; auto)
        
        hence Vtenc' : "encode (Varray t vt) =
          Ok (encode_int (length vt) @ vt_heads_small @ vt_tails_small )"
          using 3 True Vt_tailenc_small Vhenc' Vt_tailenc Vt_headenc Len_valid Heads_len_valid Inl
          by(auto simp add:encode_def array_value_valid_aux_def )

        have Heads_len_enc32 : "length (encode_int (32 + heads_length vt)) = 32"
          by(auto simp add: word_rsplit_def bin_rsplit_len)

        have Enc32 : "length (encode_int (1 + int (length vt))) = 32"
          by(auto simp add: word_rsplit_def bin_rsplit_len)

        have Enc32' : "length (encode_int (int (length vt))) = 32"
          by(auto simp add: word_rsplit_def bin_rsplit_len)

        have Vt_valid' : "list_all abi_value_valid vt"
          using Vt_valid unfolding abi_value_valid.simps
          by(auto simp add:array_value_valid_aux_def list_all_iff)

        have Vt_heads_small_eq : "length (vt_heads) = length (vt_heads_small)"
          using encode'_tuple_heads_headslength[of vt vt_tailenc_small vt_heads_small
                                                   vt_tails_small] Inl Vtht_small
                encode'_tuple_heads_headslength[OF Vt_headenc]
                Vt_valid'
          by(auto simp add:array_value_valid_aux_def)

        have Vt_tails_small_eq : "length (vt_tails) = length (vt_tails_small)"
          using encode'_tuple_heads_len2[of vt vt_tailenc_small vt_heads_small
                                            vt_tails_small] 
                encode'_tuple_heads_len2[OF Vt_headenc] Inl Vtht_small
                encode'_tuple_tails_lengths[OF Vt_tailenc_small Vt_tailenc]
          by(auto)
        
        show ?thesis using  3 True Vhenc  Vh_dyn Vt_tailenc Vt_headenc Heads_len_valid Code
            "15.IH"(1)[OF Vhenc' Vh_bound Vh_valid]
            "15.IH"(4)[OF refl Vtenc' Vt_valid]
            Enc32 Enc32' Heads_len_enc32
            abi_dynamic_size_bound_nonneg[of vh] 
            Vt_heads_small_eq Vt_tails_small_eq
            sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
          unfolding list_sum_def
          by(auto simp add:encode_def simp del: abi_dynamic_size_bound.simps)
      qed 
    qed
  }
qed


lemma abi_dynamic_size_bound_correct:
"encode v = Ok code \<Longrightarrow>
 abi_dynamic_size_bound v = bound \<Longrightarrow>
 abi_value_valid v \<Longrightarrow>
 length code \<le> bound"
  using abi_dynamic_size_bound_correct'(1)
  by auto 

(* relating size bound to heads-length calculation *)
lemma abi_dynamic_size_bound_headslength :
"heads_length vs \<le> 32 * int (length vs) + foldl (+) (0::int) (map abi_dynamic_size_bound vs)"
proof(induction vs)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
  proof(cases "abi_type_isdynamic (abi_get_type a)")
    case False
    then show ?thesis using Cons
            abi_dynamic_size_bound_nonneg[of a]
            sym[OF foldl_plus[of "(abi_dynamic_size_bound a)" 0]]
            abi_dynamic_size_bound_static[of a] False
      by(auto simp del:abi_dynamic_size_bound.simps)
  next
    case True
    then show ?thesis using Cons
          abi_dynamic_size_bound_nonneg[of a]
          sym[OF foldl_plus[of "(abi_dynamic_size_bound a)" 0]]
          True
      by(auto)
  qed
qed

(* helper lemma for proving list_nonneg *)
lemma list_nonneg_map :
  "(\<And> x . 0 \<le> f x) \<Longrightarrow>
   list_nonneg (map f l)"
  unfolding list_nonneg_def list_all_iff
proof
  fix elem
  assume Hf : "(\<And>x. 0 \<le> f x)"
  assume Helem : "elem \<in> set (map f l)"

  show "0 \<le> elem" using Hf Helem by auto
qed

(* if encode'_tuple_tails fails, but all values are encodable individually,
   this must be because the given values are too long to be serialized *)
lemma encode'_tuple_tails_overflow_fail'  :
"encode'_tuple_tails (vs) 0 (headlen) = Err err \<Longrightarrow>
 list_all abi_value_valid vs \<Longrightarrow>
 (\<And> v . v \<in> set vs \<Longrightarrow> abi_type_isdynamic (abi_get_type v) \<Longrightarrow> (\<exists> code . encode' v = Ok code)) \<Longrightarrow>
 heads_length vs \<le> headlen \<Longrightarrow>
 \<not> sint_value_valid 256 (int (length vs) * (32::int) + 
    list_sum (map abi_dynamic_size_bound vs) + (headlen - heads_length vs))"
proof(induction vs arbitrary: err headlen)
  case Nil
  then show ?case by auto
next
  case (Cons a vs)
  then show ?case
  proof(cases "abi_type_isstatic (abi_get_type a)")
    case True

    obtain vterr where Vterr : "encode'_tuple_tails vs 0 headlen = Inr vterr"
      using Cons True
      by(cases "encode'_tuple_tails vs 0 headlen"; auto)

    have Valid' : "list_all abi_value_valid vs" using Cons
      by (auto simp add:list_all_iff)

    have Encodable' :
      "(\<And>v. v \<in> set vs \<Longrightarrow> abi_type_isdynamic (abi_get_type v) \<Longrightarrow> \<exists>code. encode' v = Ok code)"
      using Cons by auto

    have Len' : "heads_length vs \<le> headlen" 
      using Cons True abi_static_size_nonneg[of "(abi_get_type a)"]
      by(auto simp add:Let_def)

    have Vs_nonneg : "list_nonneg (map abi_dynamic_size_bound vs)"
      using list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vs] 
      unfolding id_def by assumption

    hence Vs_nonneg' : "0 \<le> list_sum (map abi_dynamic_size_bound vs)"
      using list_nonneg_sum[OF Vs_nonneg] by auto

    then show ?thesis using True Cons.IH[OF Vterr Valid' Encodable' Len'] Cons.prems
      sym[OF foldl_plus[of "abi_dynamic_size_bound a" 0]]
      abi_dynamic_size_bound_nonneg[of a]
      abi_dynamic_size_bound_static[OF True]
      heads_length_nonneg[of vs]
      by(auto simp del:abi_dynamic_size_bound.simps
            simp add:Let_def list_sum_def sint_value_valid_def)
  next
    case False
    have Ain : "a \<in> set (a#vs)" by auto

    obtain aenc where Aenc : "encode' a = Ok aenc"
      using Cons.prems(3)[OF Ain] False
      by (cases "encode' a"; 
          auto simp del: abi_dynamic_size_bound.simps encode'.simps)

    have Vs_nonneg : "list_nonneg (map abi_dynamic_size_bound vs)"
      using list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vs] 
      unfolding id_def by assumption

    hence Vs_nonneg' : "0 \<le> list_sum (map abi_dynamic_size_bound vs)"
      using list_nonneg_sum[OF Vs_nonneg] by auto

    have Aenc' : "encode a = Ok aenc"
      using Cons.prems Aenc False by(auto simp add:encode_def)

    have Avalid : "abi_value_valid a"
      using Cons.prems by(auto simp add:encode_def)

    have Abound : "abi_dynamic_size_bound a = int (nat (abi_dynamic_size_bound a))"
      using abi_dynamic_size_bound_nonneg[of a] by auto

    show ?thesis
    proof(cases "encode'_tuple_tails vs 0 (headlen + int (length aenc))")
      case (Inr vserr)
      show ?thesis using Cons.prems Cons.IH[OF Inr] False Aenc Inr
                         sym[OF foldl_plus[of "(abi_dynamic_size_bound a)" 0]]
                         abi_dynamic_size_bound_nonneg[of a] Vs_nonneg'
                         heads_length_nonneg[of vs]
                         abi_dynamic_size_bound_correct[OF Aenc' Abound Avalid]
        by(auto simp add:list_sum_def sint_value_valid_def
                   simp del: abi_dynamic_size_bound.simps encode'.simps) 
    next
      case (Inl vs_tailenc)
      show ?thesis
      proof(cases "sint_value_valid 256 headlen")
        assume True' : "sint_value_valid 256 headlen"
        then show ?thesis using Cons.prems Aenc False Inl
          by(auto simp del: abi_dynamic_size_bound.simps)
      next
        assume False' : "\<not> sint_value_valid 256 headlen"
        then show ?thesis using False Cons.prems Aenc Inl
                                sym[OF foldl_plus[of "(abi_dynamic_size_bound a)" 0]]
                               abi_dynamic_size_bound_nonneg[of a] Vs_nonneg'
                               heads_length_nonneg[of vs]
                               abi_dynamic_size_bound_headslength[of vs]
          by(auto simp add:list_sum_def sint_value_valid_def
                   simp del: abi_dynamic_size_bound.simps encode'.simps)
      qed
    qed
  qed
qed

lemma those_err_exists :
    "those_err l = Err err \<Longrightarrow>
    (\<exists> x err' . x \<in> set l \<and> x = Err err')"
proof(induction l arbitrary: err)
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case
  proof(cases a)
    case (Inr aerr)
    then show ?thesis by(auto)
  next
    case (Inl a')
    hence Err' : "those_err l = Err err" using Cons
      by(cases "those_err l"; auto)

    then show ?thesis using Cons.prems Cons.IH[OF Err'] by auto
  qed
qed

lemma can_encode_as_start_nonneg :
  "can_encode_as v full_code offset \<Longrightarrow> 0 \<le> offset"
proof(induction rule:can_encode_as.induct; auto)
qed

(* 
  main theroem 2:
  if can_encode_as predicate holds, and our bound for the value's size
  is small enough to be representable as an s256,
  then encoder will return an encoding for it.
*)
theorem encode_correct_converse :
  "can_encode_as v code start \<Longrightarrow>
   sint_value_valid 256 (abi_dynamic_size_bound v) \<Longrightarrow>
    (\<exists> code' . encode v = Ok code')"
proof(induction v arbitrary: code start)
case (Vuint x1 x2)
  then show ?case 
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vsint x1 x2)
  then show ?case
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vaddr x)
  then show ?case 
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vbool x)
  then show ?case
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vfixed x1 x2 x3a)
  then show ?case
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vufixed x1 x2 x3a)
  then show ?case
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vfbytes x1 x2)
  then show ?case 
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vfunction x1 x2)
  then show ?case 
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vfarray t n vs)
  show ?case using Vfarray.prems Vfarray.IH
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code')
    then show ?thesis 
      by(auto simp add:encode_def)
  next
    case (Efarray_dyn heads head_types tails)
    then show ?thesis
    proof(cases vs)
      case Nil
      then show ?thesis using Efarray_dyn by(auto simp add:encode_def)
    next
      case (Cons v vt)
      have Dyn : "abi_type_isdynamic t"
        using Efarray_dyn
        by(auto simp add:farray_value_valid_aux_def)

      hence V_dyn : "abi_type_isdynamic (abi_get_type v)"
        using Efarray_dyn Cons
        by(auto simp add:farray_value_valid_aux_def)

      have V_valid : "abi_value_valid v"
        using Cons Efarray_dyn
        by(auto simp add:farray_value_valid_aux_def)

      obtain n' where N' : "n = Suc n'"
        using Efarray_dyn Cons
        by(auto simp add:farray_value_valid_aux_def)

      have Bound_unfold :
        "abi_dynamic_size_bound (Vfarray t n vs) =
          int (n * 32) + list_sum (map abi_dynamic_size_bound vs)" using Dyn
        by auto

      have Vt_nonneg : "0 \<le> list_sum (map abi_dynamic_size_bound vt)"
        using 
        list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
        unfolding id_def
        by(assumption)

      have Encode_lemma :
        "\<And> x . x \<in> set vs \<Longrightarrow>
               \<exists> code . encode x = Ok code"
      proof-
        fix x
        assume Hx : "x \<in> set vs"

        hence X_dyn : "abi_type_isdynamic (abi_get_type x)"
          using Vfarray Efarray_dyn Dyn
          by(auto simp add:farray_value_valid_aux_def list_all_iff)

        obtain ofs where Ofs : "(ofs, x) \<in> set tails"
                   and Ofs_in_heads : "Vsint 256 ofs \<in> set heads"
          using  Cons is_head_and_tail_vs_elem[OF Efarray_dyn(3) Hx X_dyn] by auto


        have X_bound_leq : "abi_dynamic_size_bound x \<le> list_sum (map abi_dynamic_size_bound vs)"
          using elem_lt_list_sum Hx X_dyn
                list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of _ vs]
          unfolding id_def by(auto simp del:abi_dynamic_size_bound.simps)

        hence X_size : "sint_value_valid 256 (abi_dynamic_size_bound x)"
          using Vfarray.prems Cons Dyn X_dyn Bound_unfold
                sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
                abi_dynamic_size_bound_nonneg[of v]
                abi_dynamic_size_bound_nonneg[of x]
                Vt_nonneg
          by(auto simp add:list_sum_def sint_value_valid_def
                simp del: abi_dynamic_size_bound.simps)
  
        then obtain x_code where X_code :
          "encode x = Ok x_code" using 
            Vfarray.IH[OF Hx Efarray_dyn(5)[OF Ofs]]
          by auto

        thus "\<exists>code. encode x = Ok code" by auto
      qed

      obtain v_code where V_code :
        "encode v = Ok v_code" using Encode_lemma Cons by auto

      hence V_code' : "encode' v = Ok v_code" using V_valid
        by(auto simp add:encode_def)

      obtain n' where Nnz : "n = Suc n'" and N'_vt : "n' = length vt" 
        using Vfarray Efarray_dyn Cons
        by(cases n; auto simp add: farray_value_valid_aux_def)

      show ?thesis
      proof(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length v_code))")
        case (Inr err)

        have Toobig :
          "\<not> sint_value_valid 256 (int (length vt) * 32 + 
                list_sum (map abi_dynamic_size_bound vt) + 
                ((32 + heads_length vt + int (length v_code)) - heads_length vt))"
        proof(rule encode'_tuple_tails_overflow_fail'[OF Inr])
          show "list_all abi_value_valid vt" using Cons Efarray_dyn 
            by(auto simp add: farray_value_valid_aux_def list_all_iff)
        next
          fix v'
          assume Hv' : "v' \<in> set vt"
          assume Hv'_dyn : "abi_type_isdynamic (abi_get_type v')"

          have Hv'' : "v' \<in> set vs" using Cons Hv' by auto

          have V'_valid : "abi_value_valid v'"
            using Cons Efarray_dyn Hv'
            by(auto simp add:farray_value_valid_aux_def list_all_iff)

          show "\<exists>code. encode' v' = Ok code"
            using Encode_lemma[OF Hv''] V'_valid
            by(auto simp add:encode_def)
        next
          show "heads_length vt \<le> 32 + heads_length vt + int (length v_code)"
            by auto
        qed

        have V_bound : "abi_dynamic_size_bound v = int (nat (abi_dynamic_size_bound v))"
          using abi_dynamic_size_bound_nonneg[of v] by auto

        have False using Vfarray(3) Bound_unfold Dyn Nnz N'_vt Toobig
          list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
          abi_dynamic_size_bound_headslength[of vt]
          heads_length_nonneg[of vt] Cons 
          abi_dynamic_size_bound_nonneg[of v]
          abi_dynamic_size_bound_correct[OF V_code V_bound V_valid]
          sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
          unfolding id_def 
          by(auto simp add: sint_value_valid_def list_sum_def
                     simp del:abi_dynamic_size_bound.simps)

        thus ?thesis by auto

      next
        case (Inl vt_code)

        show ?thesis 
        proof(cases "encode'_tuple_heads vt vt_code")
          fix err
          assume Inr' : "encode'_tuple_heads vt vt_code = Err err"
          have Lens : "length vt = length vt_code"
            using encode'_tuple_tails_len[OF Inl] by auto

          obtain vbad err' where Vbad_in : "vbad \<in> set vt" and Vbad_bad :  "encode' vbad = Err err'"
            using encode'_tuple_heads_fail[OF Inr' Lens] by auto

          have Vbad_valid : "abi_value_valid vbad"
            using Cons Efarray_dyn Vbad_in
            by(auto simp add:farray_value_valid_aux_def list_all_iff)

          have Vbad_in' : "vbad \<in> set vs" using Cons Vbad_in by auto

          obtain vbad_enc where "encode vbad = Ok vbad_enc"
            using Encode_lemma[OF Vbad_in'] by auto

          hence Vbad_enc' : "encode' vbad = Ok vbad_enc"
            using Vbad_valid by(auto simp add:encode_def)

          have False using Vbad_bad Vbad_enc' by auto

          thus "\<exists>code'. encode (Vfarray t n vs) = Ok code'" by auto
        next
          fix vt_headenc
          assume Inl' : "encode'_tuple_heads vt vt_code = Ok vt_headenc"
          obtain vth vtt where Vt_ht : "vt_headenc = (vth, vtt)"
            by(cases vt_headenc;  auto)

          have Vt_smallenough : "sint_value_valid 256 (32 + heads_length vt)"
            using Vfarray(3) Bound_unfold V_dyn
                  list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
                  abi_dynamic_size_bound_headslength[of vt]
                  heads_length_nonneg[of vt] Cons Nnz N'_vt
                  abi_dynamic_size_bound_nonneg[of v]
                  sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
            unfolding id_def 
            by(auto simp add: sint_value_valid_def list_sum_def
                       simp del:abi_dynamic_size_bound.simps)

          then show ?thesis using Inl Cons Efarray_dyn V_dyn V_code' Inl' Vt_ht
            by(auto simp add:encode_def)
        qed
      qed
    qed
  qed
next
  case (Vtuple ts vs)
  show ?case using Vtuple.prems Vtuple.IH
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code')
    then show ?thesis 
      by(auto simp add:encode_def)
  next
    case (Etuple_dyn t heads head_types tails)
    then obtain th tt where Ts : "ts = th # tt"
      by(cases ts; auto)
    then obtain vh vt where Vs : "vs = vh # vt" using Etuple_dyn
      by(cases vs; auto simp add:tuple_value_valid_aux_def)

    have Bound_unfold :
      "abi_dynamic_size_bound (Vtuple ts vs) =
       (length vs * 32) + list_sum (map abi_dynamic_size_bound vs)"
      using Etuple_dyn
      by(auto simp add:list_ex_iff)

    have Encode_lemma :
    "\<And> x . x \<in> set vs \<Longrightarrow>
           \<exists> code . encode x = Ok code"
    proof-
      fix x
      assume Hx : "x \<in> set vs"

      have Bound_nn : "list_nonneg (map abi_dynamic_size_bound vs)"
        unfolding list_nonneg_def
        using abi_dynamic_size_bound_nonneg
        by(auto simp add:list_all_iff simp del:abi_dynamic_size_bound.simps)

      have X_bound : "(abi_dynamic_size_bound x) \<le> abi_dynamic_size_bound (Vtuple ts vs)"
        using Hx  Etuple_dyn 
              elem_lt_list_sum[OF _ Bound_nn, of "abi_dynamic_size_bound x"]
        by(auto simp add:list_ex_iff list_sum_def)

      hence X_bound_valid : "sint_value_valid 256 (abi_dynamic_size_bound x)"
        using Vtuple.prems abi_dynamic_size_bound_nonneg[of x]
        by(auto simp add:sint_value_valid_def)

      show "\<exists>code. encode x = Ok code"
      proof(cases "abi_type_isdynamic (abi_get_type x)")
        case False
        have X_in_heads : "x \<in> set heads"
          using is_head_and_tail_vs_elem_static[OF Etuple_dyn(4) Hx] False
          by auto

        obtain x_full_code x_offset where X_can_encode : "can_encode_as x x_full_code x_offset"
          using can_encode_as_tuple_split[OF Etuple_dyn(5) refl X_in_heads] by auto

        show ?thesis using Etuple_dyn Vtuple.IH[OF Hx X_can_encode X_bound_valid] by auto
      next
        case True
        obtain ofs where X_in_tails : "(ofs, x) \<in> set tails" 
                   and Ofs_heads : "Vsint 256 ofs \<in> set heads"
          using is_head_and_tail_vs_elem[OF Etuple_dyn(4) Hx True] by auto

        have X_can_encode : "can_encode_as x code (ofs + start)"
          using Etuple_dyn(6)[OF X_in_tails]
          by auto

        show ?thesis using Vtuple.IH[OF Hx X_can_encode X_bound_valid] by auto
      qed
    qed

    show ?thesis
    proof(cases "abi_type_isdynamic th")
      case False
      have Vt_dyn : "list_ex abi_type_isdynamic tt"
        using Etuple_dyn Ts Vs False
        by(auto simp add:tuple_value_valid_aux_def list_ex_iff)

      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
        using abi_dynamic_size_bound_nonneg[of vh] by auto
  
      have Vh_valid : "abi_value_valid vh"
        using Etuple_dyn Vs
        by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)
  
      have False_vh : "abi_type_isstatic (abi_get_type vh)"
        using Etuple_dyn Vs Ts False
        by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

      obtain vh_code where Vh_code : "encode vh = Ok vh_code"
        using Encode_lemma[of vh] Ts Vs 
        by(auto simp del:encode'.simps simp add:encode_def split:if_splits)

      hence Vh_code' : "encode_static vh = Ok vh_code"
        using False_vh 
        by(auto simp add:encode_def split:if_splits)
        
      show ?thesis
      proof(cases "encode'_tuple_tails vt 0 (abi_static_size (abi_get_type vh) + heads_length vt) ")
        case (Inr err)
        have Toobig :
          "\<not> sint_value_valid 256 (int (length vt) * 32 + 
                list_sum (map abi_dynamic_size_bound vt) + 
                (abi_static_size (abi_get_type vh) + heads_length vt - heads_length vt))"
        proof(rule encode'_tuple_tails_overflow_fail'[OF Inr])
          show "list_all abi_value_valid vt" using Cons Etuple_dyn Ts Vs
            by(auto simp add: tuple_value_valid_aux_def list_all_iff)
        next
          fix v'
          assume Hv' : "v' \<in> set vt"
          assume Hv'_dyn : "abi_type_isdynamic (abi_get_type v')"

          have Hv'' : "v' \<in> set vs" using Ts Vs Hv' by auto

          have V'_valid : "abi_value_valid v'"
            using Cons Etuple_dyn Hv''
            by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

          show "\<exists>code. encode' v' = Ok code"
            using Encode_lemma[OF Hv''] V'_valid
            by(auto simp add:encode_def)
        next
          show "heads_length vt \<le> abi_static_size (abi_get_type vh) + heads_length vt"
            using abi_static_size_nonneg[of "abi_get_type vh"]
            by auto
        qed

        have False using Vtuple(3)  Toobig Ts Vs Bound_unfold
          list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
          abi_dynamic_size_bound_headslength[of vt]
          heads_length_nonneg[of vt] Cons
          abi_dynamic_size_bound_nonneg[of vh]
          abi_static_size_nonneg[of "abi_get_type vh"]
          abi_dynamic_size_bound_correct[OF Vh_code Vh_bound Vh_valid]
          abi_dynamic_size_bound_static[OF False_vh]
          sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
          unfolding id_def 
          by(auto simp add: sint_value_valid_def list_sum_def
                     simp del:abi_dynamic_size_bound.simps)

        thus ?thesis by auto      
      next
        case (Inl vt_code)
        show ?thesis 
        proof(cases "encode'_tuple_heads vt vt_code")
          fix err
          assume Inr' : "encode'_tuple_heads vt vt_code = Err err"
          have Lens : "length vt = length vt_code"
            using encode'_tuple_tails_len[OF Inl] by auto

          obtain vbad err' where Vbad_in : "vbad \<in> set vt" and Vbad_bad :  "encode' vbad = Err err'"
            using encode'_tuple_heads_fail[OF Inr' Lens] by auto

          have Vbad_valid : "abi_value_valid vbad"
            using Etuple_dyn Vbad_in Vs
            by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

          have Vbad_in' : "vbad \<in> set vs" using Cons Vbad_in Vs by auto

          obtain vbad_enc where "encode vbad = Ok vbad_enc"
            using Encode_lemma[OF Vbad_in'] by auto

          hence Vbad_enc' : "encode' vbad = Ok vbad_enc"
            using Vbad_valid by(auto simp add:encode_def)

          have False using Vbad_bad Vbad_enc' by auto

          thus "\<exists>code'. encode (Vtuple ts vs) = Ok code'" by auto
        next
          fix vt_headenc
          assume Inl' : "encode'_tuple_heads vt vt_code = Ok vt_headenc"
          obtain vth vtt where Vt_ht : "vt_headenc = (vth, vtt)"
            by(cases vt_headenc;  auto)

          have Vt_smallenough : "sint_value_valid 256 (32 + heads_length vt)"
            using Vtuple(3) Bound_unfold False Vs
                  list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
                  abi_dynamic_size_bound_headslength[of vt]
                  heads_length_nonneg[of vt] Cons 
                  abi_dynamic_size_bound_nonneg[of vh]
                  abi_static_size_nonneg[of "abi_get_type vh"]
                  abi_dynamic_size_bound_static[OF False_vh]
                  sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
            unfolding id_def 
            by(auto simp add: sint_value_valid_def list_sum_def
                    simp del:abi_dynamic_size_bound.simps)

          then show ?thesis using Inl Inl' Etuple_dyn False_vh Vt_dyn Vs Ts Vh_code' Vt_ht
            by(auto simp add:encode_def)
        qed
      qed
    next
      case True
      have Vh_bound : "abi_dynamic_size_bound vh = int (nat (abi_dynamic_size_bound vh))"
        using abi_dynamic_size_bound_nonneg[of vh] by auto
  
      have Vh_valid : "abi_value_valid vh"
        using Etuple_dyn Vs
        by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)
  
      have True_vh : "abi_type_isdynamic (abi_get_type vh)"
        using Etuple_dyn Vs Ts True
        by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

      obtain vh_code where Vh_code : "encode vh = Ok vh_code"
        using Encode_lemma[of vh] Ts Vs 
        by(auto simp del:encode'.simps simp add:encode_def split:if_splits)

      hence Vh_code' : "encode' vh = Ok vh_code"
        using True_vh 
        by(auto simp add:encode_def split:if_splits)
      have Vt_valid : "list_all abi_value_valid vt"
        using Etuple_dyn Vs by(auto simp add:tuple_value_valid_aux_def list_all_iff)

      show ?thesis
      proof(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length vh_code))")
        case (Inr err)
        have Toobig :
          "\<not> sint_value_valid 256 (int (length vt) * 32 + 
                list_sum (map abi_dynamic_size_bound vt) + 
                (32 + heads_length vt + int (length vh_code) - heads_length vt))"
        proof(rule encode'_tuple_tails_overflow_fail'[OF Inr])
          show "list_all abi_value_valid vt" using Cons Etuple_dyn Ts Vs
            by(auto simp add: tuple_value_valid_aux_def list_all_iff)
        next
          fix v'
          assume Hv' : "v' \<in> set vt"
          assume Hv'_dyn : "abi_type_isdynamic (abi_get_type v')"

          have Hv'' : "v' \<in> set vs" using Ts Vs Hv' by auto

          have V'_valid : "abi_value_valid v'"
            using Cons Etuple_dyn Hv''
            by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

          show "\<exists>code. encode' v' = Ok code"
            using Encode_lemma[OF Hv''] V'_valid
            by(auto simp add:encode_def)
        next
          show "heads_length vt \<le> 32 + heads_length vt + int (length vh_code)"
            using abi_static_size_nonneg[of "abi_get_type vh"]
            by auto
        qed

        have False using Vtuple(3)  Toobig Ts Vs Bound_unfold
          list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
          abi_dynamic_size_bound_headslength[of vt]
          heads_length_nonneg[of vt] Cons
          abi_dynamic_size_bound_nonneg[of vh]
          abi_static_size_nonneg[of "abi_get_type vh"]
          abi_dynamic_size_bound_correct[OF Vh_code Vh_bound Vh_valid]
          sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
          unfolding id_def 
          by(auto simp add: sint_value_valid_def list_sum_def
                     simp del:abi_dynamic_size_bound.simps)

        thus ?thesis by auto      
      next
        case (Inl vt_code)
        show ?thesis 
        proof(cases "encode'_tuple_heads vt vt_code")
          fix err
          assume Inr' : "encode'_tuple_heads vt vt_code = Err err"
          have Lens : "length vt = length vt_code"
            using encode'_tuple_tails_len[OF Inl] by auto

          obtain vbad err' where Vbad_in : "vbad \<in> set vt" and Vbad_bad :  "encode' vbad = Err err'"
            using encode'_tuple_heads_fail[OF Inr' Lens] by auto

          have Vbad_valid : "abi_value_valid vbad"
            using Etuple_dyn Vbad_in Vs
            by(auto simp add:tuple_value_valid_aux_def list_all_iff list_ex_iff)

          have Vbad_in' : "vbad \<in> set vs" using Cons Vbad_in Vs by auto

          obtain vbad_enc where "encode vbad = Ok vbad_enc"
            using Encode_lemma[OF Vbad_in'] by auto

          hence Vbad_enc' : "encode' vbad = Ok vbad_enc"
            using Vbad_valid by(auto simp add:encode_def)

          have False using Vbad_bad Vbad_enc' by auto

          thus "\<exists>code'. encode (Vtuple ts vs) = Ok code'" by auto
        next
          fix vt_headenc
          assume Inl' : "encode'_tuple_heads vt vt_code = Ok vt_headenc"
          obtain vth vtt where Vt_ht : "vt_headenc = (vth, vtt)"
            by(cases vt_headenc;  auto)

          have Vt_smallenough : "sint_value_valid 256 (32 + heads_length vt)"
            using Vtuple(3) Bound_unfold True Vs
                  list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
                  abi_dynamic_size_bound_headslength[of vt]
                  heads_length_nonneg[of vt] Cons 
                  abi_dynamic_size_bound_nonneg[of vh]
                  abi_static_size_nonneg[of "abi_get_type vh"]
                  sym[OF foldl_plus[of "(abi_dynamic_size_bound vh)" 0]]
            unfolding id_def 
            by(auto simp add: sint_value_valid_def list_sum_def
                    simp del:abi_dynamic_size_bound.simps)

          then show ?thesis using Inl Inl' Etuple_dyn True  Vs Ts Vh_code' Vt_ht
            by(auto simp add:encode_def tuple_value_valid_aux_def)
        qed
      qed
    qed
  qed
next
  case (Vbytes bs)
  show ?case using Vbytes.prems(1)
    by(cases rule: can_encode_as.cases; auto simp add:encode_def)
next
  case (Vstring s)
  show ?case using Vstring.prems(1)
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre' post' code')
    hence False using Vstring by auto
    thus ?thesis by auto
  next
    case (Estring l)
    show ?thesis using Estring(3)
    proof(cases rule:can_encode_as.cases)
      case (Estatic pre' post' code')
      hence False using Vstring by auto
      thus ?thesis by auto
    next
      case (Ebytes pre post count code)
      thus ?thesis using Vstring Estring
        by(auto simp add:encode_def Let_def)
    qed
  qed
next
  case (Varray t vs)
  show ?case using Varray.prems Varray.IH
  proof(cases rule: can_encode_as.cases)
    case (Estatic pre post code)
    then show ?thesis by auto
  next
    case (Earray heads head_types tails)

    have Bound_unfold :
      "abi_dynamic_size_bound (Varray t vs) =
       32 + (length vs * 32) + list_sum (map abi_dynamic_size_bound vs)"
      using Earray
      by(auto)

    show ?thesis
    proof(cases vs)
      case Nil
      then show ?thesis using Earray by(auto simp add:encode_def)
    next
      case (Cons v vt)

      have V_valid : "abi_value_valid v"
        using Cons Earray
        by(auto simp add:array_value_valid_aux_def)

      have Encode_lemma :
      "\<And> x . x \<in> set vs \<Longrightarrow>
             \<exists> code . encode x = Ok code"
      proof-
        fix x
        assume Hx : "x \<in> set vs"
  
        have Bound_nn : "list_nonneg (map abi_dynamic_size_bound vs)"
          unfolding list_nonneg_def
          using abi_dynamic_size_bound_nonneg
          by(auto simp add:list_all_iff simp del:abi_dynamic_size_bound.simps)
  
        have X_bound : "(abi_dynamic_size_bound x) \<le> abi_dynamic_size_bound (Varray t vs)"
          using Hx  Etuple_dyn 
                elem_lt_list_sum[OF _ Bound_nn, of "abi_dynamic_size_bound x"]
          by(auto simp add:list_ex_iff list_sum_def)
  
        hence X_bound_valid : "sint_value_valid 256 (abi_dynamic_size_bound x)"
          using Varray.prems abi_dynamic_size_bound_nonneg[of x]
          by(auto simp add:sint_value_valid_def)
  
        show "\<exists>code. encode x = Ok code"
        proof(cases "abi_type_isdynamic (abi_get_type x)")
          case False
          have X_in_heads : "x \<in> set heads"
            using is_head_and_tail_vs_elem_static[OF Earray(2) Hx] False 
            by auto
  
          obtain x_full_code x_offset where X_can_encode : "can_encode_as x x_full_code x_offset"
            using can_encode_as_tuple_split[OF Earray(4) refl X_in_heads] by auto
  
          show ?thesis using Etuple_dyn Varray.IH[OF Hx X_can_encode X_bound_valid] by auto
        next
          case True
          obtain ofs where X_in_tails : "(ofs, x) \<in> set tails" 
                     and Ofs_heads : "Vsint 256 ofs \<in> set heads"
            using is_head_and_tail_vs_elem[OF Earray(2) Hx True] by auto
  
          have X_can_encode : "can_encode_as x code (ofs + start + 32)"
            using Earray(5)[OF X_in_tails]
            by auto
  
          show ?thesis using Varray.IH[OF Hx X_can_encode X_bound_valid] by auto
        qed
      qed

      show ?thesis
      proof(cases "abi_type_isdynamic t")
        case False
        have V_static : "abi_type_isstatic (abi_get_type v)"
          using Earray Cons False
          by(auto simp add:array_value_valid_aux_def)

        obtain v_code where V_code :
          "encode v = Ok v_code" using Cons Encode_lemma[of v] by auto

        hence V_code' : "encode_static v = Ok v_code" using V_valid V_static
          by(auto simp add:encode_def)

        show ?thesis using Cons V_static
        proof(cases "encode'_tuple_tails vt 0
                   (abi_static_size (abi_get_type v) + heads_length vt)")
          case (Inr err)
          have Toobig :
            "\<not> sint_value_valid 256
               (int (length vt) * 32 + list_sum (map abi_dynamic_size_bound vt) +
               (abi_static_size (abi_get_type v) + heads_length vt - heads_length vt))"
          proof(rule encode'_tuple_tails_overflow_fail'[OF Inr])
            show "list_all abi_value_valid vt" using Cons Earray 
              by(auto simp add: array_value_valid_aux_def list_all_iff)
          next
            fix v'
            assume Hv' : "v' \<in> set vt"
            assume Hv'_dyn : "abi_type_isdynamic (abi_get_type v')"

            have Hv'_typ : "abi_get_type v' = t" using  Earray Hv' Hv'_dyn Cons
              by(auto simp add:array_value_valid_aux_def list_all_iff)

            have False using Earray Hv'_typ Hv'_dyn False
              by(auto simp add:array_value_valid_aux_def list_all_iff)

            thus "\<exists>code. encode' v' = Ok code" by auto
          next
            show "heads_length vt \<le> abi_static_size (abi_get_type v) + heads_length vt"
              using heads_length_nonneg[of vt]
                    abi_static_size_nonneg[of "abi_get_type v"] by auto
          qed
  
          have False using Varray(3)  Toobig Cons Bound_unfold
            list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
            abi_dynamic_size_bound_headslength[of vt]
            heads_length_nonneg[of vt] Cons
            abi_dynamic_size_bound_nonneg[of v]
            abi_static_size_nonneg[of "abi_get_type v"]
            abi_dynamic_size_bound_static[of v] V_static
            sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
            unfolding id_def 
            by(auto simp add: sint_value_valid_def list_sum_def
                       simp del:abi_dynamic_size_bound.simps)
  
          thus ?thesis by auto
        next
          case (Inl vt_code)
          show ?thesis
          proof(cases "encode'_tuple_heads vt vt_code")
            fix err
            assume Inr' : "encode'_tuple_heads vt vt_code = Err err"
            have Lens : "length vt = length vt_code"
              using encode'_tuple_tails_len[OF Inl] by auto
  
            obtain vbad err' where Vbad_in : "vbad \<in> set vt" and Vbad_bad :  "encode' vbad = Err err'"
              using encode'_tuple_heads_fail[OF Inr' Lens] by auto
  
            have Vbad_valid : "abi_value_valid vbad"
              using Cons Earray Vbad_in
              by(auto simp add:array_value_valid_aux_def list_all_iff)
  
            have Vbad_in' : "vbad \<in> set vs" using Cons Vbad_in by auto
  
            obtain vbad_enc where "encode vbad = Ok vbad_enc"
              using Encode_lemma[OF Vbad_in'] by auto
  
            hence Vbad_enc' : "encode' vbad = Ok vbad_enc"
              using Vbad_valid by(auto simp add:encode_def)
  
            have False using Vbad_bad Vbad_enc' by auto
  
            thus "\<exists>code'. encode (Varray t vs) = Ok code'" by auto
          next
            fix vt_headenc
            assume Inl' : "encode'_tuple_heads vt vt_code = Ok vt_headenc"
            obtain vth vtt where Vt_ht : "vt_headenc = (vth, vtt)"
            by(cases vt_headenc;  auto)

            have Vt_smallenough : "sint_value_valid 256 (32 + heads_length vt)"
              using Varray(3) Bound_unfold 
                    list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
                    abi_dynamic_size_bound_headslength[of vt]
                    heads_length_nonneg[of vt] Cons
                    abi_dynamic_size_bound_nonneg[of v]
                    sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
              unfolding id_def 
              by(auto simp add: sint_value_valid_def list_sum_def
                         simp del:abi_dynamic_size_bound.simps)
  
            then show ?thesis using Inl Cons Earray V_static V_code' V_valid Inl' Vt_ht
              by(auto simp add:encode_def)
          qed
        qed
      next
        case True

        have V_dyn : "abi_type_isdynamic (abi_get_type v)"
          using Earray Cons True
          by(auto simp add:array_value_valid_aux_def)

        obtain v_code where V_code :
          "encode v = Ok v_code" using Cons Encode_lemma[of v] by auto

        hence V_code' : "encode' v = Ok v_code" using V_valid True
          by(auto simp add:encode_def)

        show ?thesis using Cons True V_valid V_dyn 
        proof(cases "encode'_tuple_tails vt 0 (32 + heads_length vt + int (length v_code))")
          case (Inr err)

          have Toobig :
            "\<not> sint_value_valid 256 (int (length vt) * 32 + 
                  list_sum (map abi_dynamic_size_bound vt) + 
                  ((32 + heads_length vt + int (length v_code)) - heads_length vt))"
          proof(rule encode'_tuple_tails_overflow_fail'[OF Inr])
            show "list_all abi_value_valid vt" using Cons Earray
              by(auto simp add: array_value_valid_aux_def list_all_iff)
          next
            fix v'
            assume Hv' : "v' \<in> set vt"
            assume Hv'_dyn : "abi_type_isdynamic (abi_get_type v')"
  
            have Hv'' : "v' \<in> set vs" using Cons Hv' by auto
  
            have V'_valid : "abi_value_valid v'"
              using Cons Earray Hv'
              by(auto simp add:array_value_valid_aux_def list_all_iff)
  
            show "\<exists>code. encode' v' = Ok code"
              using Encode_lemma[OF Hv''] V'_valid
              by(auto simp add:encode_def)
          next
            show "heads_length vt \<le> 32 + heads_length vt + int (length v_code)"
              by auto
          qed

          have V_bound : "abi_dynamic_size_bound v = int (nat (abi_dynamic_size_bound v))"
            using abi_dynamic_size_bound_nonneg[of v] by auto
  
          have False using Varray(3) Bound_unfold V_dyn Toobig
            list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
            abi_dynamic_size_bound_headslength[of vt]
            heads_length_nonneg[of vt] Cons
            abi_dynamic_size_bound_nonneg[of v]
            abi_dynamic_size_bound_correct[OF V_code V_bound V_valid]
            sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
            unfolding id_def 
            by(auto simp add: sint_value_valid_def list_sum_def
                       simp del:abi_dynamic_size_bound.simps)
  
          thus ?thesis by auto
        next
          case (Inl vt_code)

          show ?thesis
          proof(cases "encode'_tuple_heads vt vt_code")
            fix err
            assume Inr' : "encode'_tuple_heads vt vt_code = Err err"
            have Lens : "length vt = length vt_code"
              using encode'_tuple_tails_len[OF Inl] by auto
  
            obtain vbad err' where Vbad_in : "vbad \<in> set vt" and Vbad_bad :  "encode' vbad = Err err'"
              using encode'_tuple_heads_fail[OF Inr' Lens] by auto
  
            have Vbad_valid : "abi_value_valid vbad"
              using Cons Earray Vbad_in
              by(auto simp add:array_value_valid_aux_def list_all_iff)
  
            have Vbad_in' : "vbad \<in> set vs" using Cons Vbad_in by auto
  
            obtain vbad_enc where "encode vbad = Ok vbad_enc"
              using Encode_lemma[OF Vbad_in'] by auto
  
            hence Vbad_enc' : "encode' vbad = Ok vbad_enc"
              using Vbad_valid by(auto simp add:encode_def)
  
            have False using Vbad_bad Vbad_enc' by auto
  
            thus "\<exists>code'. encode (Varray t vs) = Ok code'" by auto
          next
            fix vt_headenc
            assume Inl' : "encode'_tuple_heads vt vt_code = Ok vt_headenc"
            obtain vth vtt where Vt_ht : "vt_headenc = (vth, vtt)"
            by(cases vt_headenc;  auto)

            have Vt_smallenough : "sint_value_valid 256 (32 + heads_length vt)"
              using Varray(3) Bound_unfold 
                    list_nonneg_sum[OF list_nonneg_map[OF abi_dynamic_size_bound_nonneg, of id vt]]
                    abi_dynamic_size_bound_headslength[of vt]
                    heads_length_nonneg[of vt] Cons
                    abi_dynamic_size_bound_nonneg[of v]
                    sym[OF foldl_plus[of "(abi_dynamic_size_bound v)" 0]]
              unfolding id_def 
              by(auto simp add: sint_value_valid_def list_sum_def
                         simp del:abi_dynamic_size_bound.simps)
  
            then show ?thesis using Inl Cons Earray V_dyn V_code' V_valid Inl' Vt_ht
              by(auto simp add:encode_def)
          qed
        qed
      qed
    qed
  qed
qed

end
