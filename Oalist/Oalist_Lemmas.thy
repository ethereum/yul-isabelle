theory Oalist_Lemmas
  imports Oalist
begin

lemma empty_get :
  "get empty k = None"
  by(transfer; auto)

lemma str_ord_update_str_ord_update :
  assumes H: "strict_order (map fst l)"
  shows "str_ord_update k v' (str_ord_update k v l) = str_ord_update k v' l"
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons lh lt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  show ?case using Cons Lh
    by(auto)
qed

lemma update_update :
  "update k v' (update k v l) = update k v' l"
  by(transfer; auto simp add: str_ord_update_str_ord_update)


lemma alist_all_val_get :
  assumes H : "alist_all_val P l"
  assumes K : "map_of l k = Some r"
  shows "P r" using assms
proof(induction l arbitrary: k)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh :  "lh = (lhk, lhv)"
    by(cases lh; auto)

  show ?case 
  proof(cases "lhk = k")
    case True
    then show ?thesis using Cons Lh
      by(auto simp add: alist_all_val_def)
  next
    case False

    have Ind : "alist_all_val P lt" using Cons
      by(auto simp add: alist_all_val_def)

    show ?thesis using Cons.prems Cons.IH[OF Ind] Lh False
      by(auto)
  qed
qed

lemma oalist_all_val_get :
  assumes H : "oalist_all_val P l"
  assumes K : "get l k = Some r"
  shows "P r"
  using assms
proof(transfer)
  fix P l k r
  show "strict_order (map fst l) \<Longrightarrow> alist_all_val P l \<Longrightarrow> map_of l k = Some r \<Longrightarrow> P r"
    using assms alist_all_val_get[of P l k r]
    by auto
qed

lemma alist_all_val_get_conv :
  assumes H0 : "strict_order (map fst l)"
  assumes H : "\<And> k r . map_of l k = Some r \<Longrightarrow> P r"
  shows "alist_all_val P l"
  using assms
proof(induction l)
  case Nil
  then show ?case by (auto simp add: alist_all_val_def)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh :  "lh = (lhk, lhv)"
    by(cases lh; auto)

  show ?case 
  proof(cases "P lhv")
    case True

    have Ord_tl : "strict_order (map fst lt)"
      using strict_order_tl[of lhk "map fst lt"] Cons.prems Lh
      by auto

    have Hyp : "(\<And>k r. map_of lt k = Some r \<Longrightarrow> P r)"
    proof-
      fix k r
      assume M : "map_of lt k = Some r"

      then have Neq : "k \<noteq> lhk"
      proof(cases "k = lhk")
        case True' : True

        then have In : "k \<in> set (map fst lt)" using imageI[OF map_of_SomeD[OF M], of fst]
          by auto

        then have  False
          using strict_order_distinct[OF Cons.prems(1)] Lh True'
          by(auto)

        thus ?thesis by auto
      next
        case False' : False
        then show ?thesis by auto
      qed

      then have Conc' : "map_of (lh # lt) k = Some r"
        using Lh M
        by(auto)

      show "P r" using Cons.prems(2)[OF Conc']
        by(auto)
    qed

    show ?thesis using Cons.IH[OF Ord_tl Hyp] True Lh
      by(auto simp add: alist_all_val_def)
  next
    case False

    have "P lhv"
      using Lh Cons.prems(2)[of lhk lhv]
      by auto

    hence False using False by auto

    thus ?thesis by auto
  qed
qed

lemma oalist_all_val_get_eq :
  "oalist_all_val P l = (\<forall> k r . get l k = Some r \<longrightarrow> P r)"
proof(transfer)
  fix P l
  assume Ord : "strict_order (map fst l)"
  show "alist_all_val P l = (\<forall>k r. map_of l k = Some r \<longrightarrow> P r)"
  proof
    assume "alist_all_val P l"
    then show "\<forall>k r. map_of l k = Some r \<longrightarrow> P r"
      using alist_all_val_get
      by auto
  next
    assume " \<forall>k r. map_of l k = Some r \<longrightarrow> P r"
    then show "alist_all_val P l"
      using alist_all_val_get_conv[OF Ord]
      by auto
  qed
qed
    
lemma str_ord_zip_get :
  assumes "strict_order (map fst l1)"
  assumes "strict_order (map fst l2)"
  shows "map_of (str_ord_zip flr fl fr l1 l2) k =
    (case (map_of l1 k, map_of l2 k) of (None, None) \<Rightarrow> None | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl) | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
  using assms str_ord_zip_get' by blast

lemma oalist_zip_get :
  shows "get (oalist_zip flr fl fr l1 l2) k =
    (case (get l1 k, get l2 k) of (None, None) \<Rightarrow> None | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl) | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
proof(transfer)
  fix flr fl fr l1 l2 k
  show "strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow>
       map_of (str_ord_zip flr fl fr l1 l2) k =
       (case (map_of l1 k, map_of l2 k) of
        (None, None) \<Rightarrow> None
        | (None, Some vr) \<Rightarrow> Some (fr k vr)
        | (Some vl, None) \<Rightarrow> Some (fl k vl)
        | (Some vl, Some vr) \<Rightarrow>
            Some (flr k vl vr))"
    using str_ord_zip_get
    by blast
qed

lemma strict_order_cons' :
  assumes H1 : "strict_order (hk#t)"
  assumes H2 : "k' \<in> set t"
  shows "hk < k'"
proof-
  obtain k'_idx where "t ! k'_idx = k'" "k'_idx < length t"
    using H2
    unfolding in_set_conv_nth 
    by(blast)

  then show ?thesis
    using strict_order_unfold[OF H1, of "1 + k'_idx" 0]
    by auto
qed

lemma str_ord_eq1 :
  assumes "l1 = l2"
  shows
    "map_of l1 k = map_of l2 k"
  using assms
  by auto

lemma str_ord_eq2 :
  assumes H1 : "strict_order (map fst l1)"
  assumes H2 : "strict_order (map fst l2)"
  assumes H : "\<And> k . map_of l1 k = map_of l2 k"
  shows "l1 = l2" using assms
proof(induction l1 arbitrary: l2)
  case Nil
  show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis using Nil by auto
  next
    case Cons' : (Cons l2h l2t)

    obtain l2hk l2hv where L2h : "l2h = (l2hk, l2hv)"
      by(cases l2h; auto)

    have False using Nil(3)[of l2hk] L2h Cons'
      by(auto)

    then show ?thesis by auto
  qed
next
  case (Cons l1h l1t)

  obtain l1hk l1hv where L1h : "l1h = (l1hk, l1hv)"
    by(cases l1h; auto)

  show ?case
  proof(cases l2)
    case Nil' : Nil
    then show ?thesis using Cons.prems(3)[of "l1hk"] L1h
      by auto
  next
    case Cons' : (Cons l2h l2t)

    obtain l2hk l2hv where L2h : "l2h = (l2hk, l2hv)"
      by(cases l2h; auto)

    consider (1) "l1hk < l2hk" |
             (2) "l2hk < l1hk" |
             (3) "l1hk = l2hk"
      using linorder_class.less_linear
      by auto

    then show ?thesis
    proof cases
      case 1

      have L1hv : "map_of (l1h # l1t) l1hk = Some l1hv"
        using L1h
        by auto

      hence L2v : "map_of l2t l1hk = Some l1hv"
        using Cons.prems(3)[of l1hk] 1 L2h Cons' by auto

      hence L2v' : "l1hk \<in> set (map fst l2t)"
        using imageI[OF map_of_SomeD[OF L2v], of fst]
        by auto

      then have False using strict_order_cons'[of l2hk "map fst l2t" "l1hk"] 1
        Cons.prems(2) Cons' L2h
        by auto

      then show ?thesis
        by auto
    next
      case 2

      have L2hv : "map_of l2 l2hk = Some l2hv"
        using L2h Cons'
        by auto

      hence L1v : "map_of (l1h # l1t) l2hk = Some l2hv"
        using Cons.prems(3)[of l2hk]
        by auto

      hence L1v' : "map_of l1t l2hk = Some l2hv"
        using 2 L1h
        by(auto split: if_split_asm)

      hence L1v'' : "l2hk \<in> set (map fst (l1t))"
        using imageI[OF map_of_SomeD[OF L1v'], of fst]
        by auto

      then have False using strict_order_cons'[of l1hk "map fst (l1t)" "l2hk"] 2
        Cons.prems(1) Cons' L1h
        by auto

      then show ?thesis
        by auto
    next
      case 3

      have Ord1' : "strict_order (map fst l1t)"
        using strict_order_tl Cons.prems(1) L1h
        by auto

      have Ord2' : "strict_order (map fst l2t)"
        using strict_order_tl Cons.prems(2) L2h Cons'
        by auto

      have Ind_Arg : " (\<And>k. map_of l1t k = map_of l2t k)"
      proof-
        fix k

        show "map_of l1t k = map_of l2t k"
        proof(cases "k = l1hk")
          case True

          have C1 : "map_of l1t k = None"
          proof(cases "map_of l1t k")
            case None
            then show ?thesis by simp
          next
            case (Some bad)

            have Bad1 :  "(k, bad) \<in> set l1t"
              using map_of_SomeD[OF Some] by simp

            hence Bad2 : "k \<in> set (map fst l1t)"
              using imageI[OF Bad1, of fst]
              by simp

            then have False 
              using strict_order_cons'[of l1hk "map fst l1t", of k] Cons.prems(1) L1h True
              by auto

            thus ?thesis by auto
          qed

          have C2 : "map_of l2t k = None"
          proof(cases "map_of l2t k")
            case None
            then show ?thesis by simp
          next
            case (Some bad)

            have Bad1 :  "(k, bad) \<in> set l2t"
              using map_of_SomeD[OF Some] by simp

            hence Bad2 : "k \<in> set (map fst l2t)"
              using imageI[OF Bad1, of fst]
              by simp

            then have False 
              using strict_order_cons'[of l2hk "map fst l2t", of k] Cons.prems(2) True 3 L2h Cons'
              by auto

            thus ?thesis by auto
          qed

          show "map_of l1t k = map_of l2t k"
            using C1 C2
            by auto
        next
          case False

          then show "map_of l1t k = map_of l2t k"
            using Cons.prems(3)[of k] 3 L2h L1h Cons'
            by(simp)
        qed
      qed

      have Vs : "l1hv = l2hv"
        using Cons.prems(3)[of l1hk] 3 L1h L2h Cons'
        by auto

      show ?thesis 
        using Cons.IH[OF Ord1' Ord2' Ind_Arg] Cons.prems 3 L1h L2h Cons' Vs
        by auto
    qed
  qed
qed

lemma oalist_eq2 :
  assumes H : "\<And> k . get l1 k = get l2 k"
  shows "l1 = l2" using assms
proof(transfer)
  show "\<And>l1 l2.
       strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow>
       (\<And>k. map_of l1 k = map_of l2 k) \<Longrightarrow> l1 = l2"
    using str_ord_eq2
    by blast
qed

lemma oalist_get_eq :
  shows "(l1 = l2) = (\<forall> k . get l1 k = get l2 k)"
  using oalist_eq2
  by blast

lemma alist_map_val_get :
  shows
  "map_of (alist_map_val f l) k =
      (case map_of l k of
        None \<Rightarrow> None
        | Some v \<Rightarrow> Some (f v))"
proof(induction l arbitrary: f k)
  case Nil
  then show ?case by auto
next
  case (Cons lh lt)
  then show ?case 
    by(auto)
qed

lemma oalist_map_val_get :
  shows "get (oalist_map_val f l) k =
    (case get l k of
      None \<Rightarrow> None
      | Some v \<Rightarrow> Some (f v))"
proof(transfer)
  fix f l k
  show "strict_order (map fst l) \<Longrightarrow>
        map_of (alist_map_val f l) k =
        (case map_of l k of None \<Rightarrow> None | Some v \<Rightarrow> Some (f v))"
    using alist_map_val_get[of f l k]
    by auto
qed

lemma oalist_keys_update_hit :
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "get l k = Some v"
  shows "oalist_keys (update k v' l) = oalist_keys l"
  using assms
proof(transfer)
  fix l :: "('k * 'v) list"
  show "\<And> k v v'.
       strict_order (map fst l) \<Longrightarrow>
       map_of l k = Some v \<Longrightarrow>
       map fst (str_ord_update k v' l) = map fst l"
  proof(induction l)
    case Nil
    then show ?case
      by(auto)
  next
    case (Cons h t)

    obtain hk hv where H: "h = (hk, hv)"
      by(cases h; auto)

    have Ord_tl : "strict_order (map fst t)"
      using Cons.prems strict_order_tl
      by auto

    show ?case
    proof(cases "k = hk")
      case Eq : True
      then show ?thesis using Cons H
        by(auto)
    next
      case False

      show ?thesis
      proof(cases "hk < k")
        case Lt : True
        then show ?thesis 
          using Cons.prems H Cons.IH[OF Ord_tl]
          by(auto)
      next
        case Bad : False

        have Map_tl : "map_of (t) k = Some v"
          using Cons.prems False H
          by(auto)

        then have "(k, v) \<in> set t"
          using map_of_SomeD[OF Map_tl]
          by auto

        then obtain ix where Ix :
          "t ! ix = (k, v)" "ix < length t"
          unfolding in_set_conv_nth
          by auto

        then show ?thesis
          using False Bad H strict_order_unfold[OF Cons.prems(1), of "1 + ix" 0]
          by(auto)
      qed
    qed
  qed
qed

lemma str_ord_update_get_eq :
  assumes "strict_order (map fst l)"
  shows "map_of (str_ord_update k v l) k = Some v"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons h t)

  obtain hk hv where H : "h = (hk, hv)"
    by(cases h; auto)

  show ?case using Cons H strict_order_tl
    by(auto)
qed

lemma oalist_update_get_eq :
  fixes l :: "('k :: linorder, 'v) oalist"
  shows "get (update k v l) k = Some v"
proof(transfer)
  fix k v
  fix l :: "('k * 'v) list"
  assume H : "strict_order (map fst l)"
  show "map_of (str_ord_update k v l)
        k =
       Some v"
    using str_ord_update_get_eq[OF H]
    by auto
qed

lemma str_ord_update_get_neq :
  assumes "strict_order (map fst l)"
  assumes "k1 \<noteq> k"
  shows "map_of (str_ord_update k1 v l) k =
         map_of l k"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons h t)

  obtain hk hv where H : "h = (hk, hv)"
    by(cases h; auto)

  show ?case using Cons H strict_order_tl
    by(auto)
qed

lemma oalist_update_get_neq :
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "k1 \<noteq> k"
  shows "get (update k1 v l) k = get l k"
  using assms
proof(transfer)
  fix k1 k :: 'k
  fix v
  fix l :: "('k * 'v) list"
  assume Neq : "k1 \<noteq> k"
  assume H : "strict_order (map fst l)"
  show "map_of (str_ord_update k1 v l)
        k =
       map_of l k"
    using str_ord_update_get_neq[OF H Neq]
    by auto
qed

lemma oalist'_one_one_tl :
  assumes "distinct (map snd (h#t))"
  shows "distinct (map snd t)"
  using assms
  by(auto)

lemma oalist_flip'_get :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  assumes "distinct (map snd l)"
  assumes "map_of l k = Some v"
  shows "map_of (oalist_flip' l) v = Some k"
  using assms
proof-
  fix l :: "('k * 'k) list"
  show "\<And> k v.
       strict_order (map fst l) \<Longrightarrow>
       distinct (map snd l) \<Longrightarrow>
       map_of l k = Some v \<Longrightarrow>
       map_of (oalist_flip' l) v = Some k"
  proof(induction l)
    case Nil
    then show ?case by auto
  next
    case (Cons h t)

    obtain hk hv where H : "h = (hk, hv)"
      by(cases h; auto)

    have Ord_tl : "strict_order (map fst t)"
      using Cons.prems H strict_order_tl
      by auto

    have Ord_flip : "strict_order (map fst (oalist_flip' t))"
      using Ord_tl oalist_flip'_correct
      by auto

    show ?case
    proof(cases "k = hk")
      case True

      then show ?thesis
        using Cons.prems Cons.IH H str_ord_update_get_eq[OF Ord_flip, of v hk]
        by(auto)
    next
      case False

      have Map_tl : "map_of t k = Some v"
        using Cons.prems H False
        by(auto)

      have Vin : "v \<in> snd ` set t"
        using imageI[OF map_of_SomeD[OF Map_tl], of snd]
        by(auto)

      have Hv_notin : "hv \<notin> snd ` set t"
        using Cons.prems False H
        by(auto)

      have Neq : "hv \<noteq> v"
        using Vin Hv_notin
        by auto

      show ?thesis
        using Cons.prems Cons.IH[OF Ord_tl, of k v] H str_ord_update_get_neq[OF Ord_flip Neq] False
        by(auto)
    qed
  qed
qed

lemma oalist_flip_get :
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  assumes "get l k = Some v"
  shows "get (oalist_flip l) v = Some k"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "\<And> k v.
       strict_order (map fst l) \<Longrightarrow>
       distinct (map snd l) \<Longrightarrow>
       map_of l k = Some v \<Longrightarrow>
       map_of (oalist_flip' l) v = Some k"
    using oalist_flip'_get
    by auto
qed

lemma strict_order_update_swap :
  assumes "strict_order (map fst l)"
  assumes "k1 \<noteq> k2"
  shows "str_ord_update k1 v1 (str_ord_update k2 v2 l) =
         str_ord_update k2 v2 (str_ord_update k1 v1 l)"
  using assms
proof(induction l arbitrary: k1 v1 k2 v2)
  case Nil
  then show ?case
    using less_linear[of k1 k2]
    by(auto)
next
  case (Cons h t)

  obtain hk hv where H : "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using strict_order_tl Cons.prems
    by fastforce

  show ?case using Cons.prems Cons.IH[OF Ord_tl] H
    by(auto)
qed

lemma oalist_update_swap :
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "k1 \<noteq> k2"
  shows "update k1 v1 (update k2 v2 l) =
    update k2 v2 (update k1 v1 l)"
  using assms
proof(transfer)
  fix k1 k2 :: 'k
  fix v1 v2 
  fix l :: "('k * 'v) list"
  assume Neq : 
    "k1 \<noteq> k2"
  assume Ord :
    "strict_order (map fst l)"

  show "str_ord_update k1 v1 (str_ord_update k2 v2 l) =
       str_ord_update k2 v2 (str_ord_update k1 v1 l)"
    using strict_order_update_swap[OF Ord Neq]
    by auto
qed

lemma oalist_flip'_update :
  assumes H : "strict_order (map fst l)"
  assumes Hdist : "distinct (map snd l)"
  assumes "k \<notin> fst ` set l"
  assumes "v \<notin> snd ` set l"
  shows "oalist_flip' (str_ord_update k v l) =
         str_ord_update v k (oalist_flip' l)"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case
    by auto
next
  case (Cons h t)

  obtain hk hv where H : "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using strict_order_tl Cons.prems
    by fastforce

  show ?case
  proof(cases "k = hk")
    case True

    show ?thesis
      using Cons.prems H True
      by(auto)
  next
    case False
    then show ?thesis 
      using Cons.prems H Cons.IH[OF Ord_tl, of k]
      using strict_order_update_swap[OF oalist_flip'_correct[OF Ord_tl]]
      by(auto)
  qed
qed

lemma str_ord_update_set :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  shows "set (str_ord_update k v l) =
    ((set l - {x . fst x = k}) \<union> {(k, v)})"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case by auto
next
  case (Cons h t)

  obtain hk hv where H: "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using Cons.prems H strict_order_tl
    by auto

  show ?case
  proof(cases "hk = k")
    case True

    then show ?thesis
      using Cons.prems Cons.IH[OF Ord_tl] H
      using strict_order_distinct[OF Cons.prems(1)]
      by(auto)
  next
    case False1 : False

    show ?thesis
    proof(cases "hk < k")
      case True2 : True

      then show ?thesis
        using Cons.prems Cons.IH[OF Ord_tl] H
        using strict_order_distinct[OF Cons.prems(1)]
        by(auto)

    next

      case False2 : False

      have Lt : "k < hk"
        using False1 False2
        by auto

      show ?thesis
      proof
        show "set (str_ord_update k v (h # t))
          \<subseteq> set (h # t) - {x. fst x = k} \<union> {(k, v)}"
        proof
          fix x

          assume X : "x \<in> set (str_ord_update k v (h # t))"

          obtain xk xv where Xkv : "x = (xk, xv)"
            by(cases x; auto)

          show "x \<in> set (h # t) - {x. fst x = k} \<union> {(k, v)}"
          proof(cases "xk = k")
            case True3 : True

            show ?thesis
            proof(cases "(k, xv) \<in> set t")
              case True4 : True

              then obtain ix where Ix : "t ! ix = (k, xv)" "ix < length t"
                unfolding in_set_conv_nth
                by auto

              have False
                using strict_order_unfold[OF Cons.prems(1), of "1 + ix" "0"]
                using H Lt X Xkv Ix
                by(auto)

              then show ?thesis by auto
            next
              case False4 : False
              then show ?thesis
                using Cons.prems Cons.IH[OF Ord_tl] H Lt X Xkv
                using strict_order_distinct[OF Cons.prems(1)]
                by(auto)
            qed
          next
            case False3 : False
            then show ?thesis
              using Cons.prems Cons.IH[OF Ord_tl] H Lt X Xkv
              using strict_order_distinct[OF Cons.prems(1)]
              by(auto)
          qed
        qed
      next
        show "set (h # t) - {x. fst x = k} \<union> {(k, v)}
          \<subseteq> set (str_ord_update k v (h # t))"
        using Cons.prems Cons.IH[OF Ord_tl] H
        using strict_order_distinct[OF Cons.prems(1)]
          by(auto)
      qed
    qed
  qed
qed

lemma oalist_flip'_set :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  assumes "distinct (map snd l)"
  shows "set (oalist_flip' l) = (\<lambda> (x, y) . (y, x)) ` set l"
  using assms
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons h t )

  obtain hk hv where H: "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using Cons.prems H strict_order_tl
    by auto

  show ?case
  proof
    show "set (oalist_flip' (h # t)) \<subseteq> (\<lambda>a. case a of (x, y) \<Rightarrow> (y, x)) ` set (h # t)"
    proof
      fix x
      assume Hx : "x \<in> set (oalist_flip' (h # t)) "

      obtain xk xv where Xkv : "x = (xv, xk)"
        by(cases x; auto)

      have In_upd : "(xv, xk) \<in> set (str_ord_update hv hk (oalist_flip' t))"
        using Cons.prems Cons.IH[OF Ord_tl] H Hx Xkv
        by(auto)

      have In_upd' : "(xv, xk) \<in> set (oalist_flip' (t)) - {x. fst x = hv} \<union> {(hv, hk)}"
        using In_upd
        unfolding Xkv str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of hv hk]
          In_upd Xkv
        by simp

      show "x \<in> (\<lambda>a. case a of (x, y) \<Rightarrow> (y, x)) ` set (h # t)"
      proof(cases "hv \<in> snd ` set t")
        case True
        then show ?thesis
          using Cons.prems Cons.IH[OF Ord_tl] H Hx Xkv
          using str_ord_update_get_eq[OF oalist_flip'_correct[OF Ord_tl]]
          by(auto)
      next
        case False
        then show ?thesis 
          using Cons.prems Cons.IH[OF Ord_tl] H Hx Xkv In_upd'
          by(auto)
      qed
    qed
  next
    show "(\<lambda>a. case a of (x, y) \<Rightarrow> (y, x)) ` set (h # t) \<subseteq> set (oalist_flip' (h # t))"
    proof
      fix x
      assume Hx : "x \<in> (\<lambda>a. case a of (x, y) \<Rightarrow> (y, x)) ` set (h # t)"

      obtain xk xv where Xkv : "x = (xv, xk)"
        by(cases x; auto)

      show "x \<in> set (oalist_flip' (h # t))"
      proof(cases "xk = hk")
        case True

        show ?thesis
          using Cons.prems H  Hx Xkv True Cons.IH[OF Ord_tl]
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
          by(auto)
      next
        case False
        show ?thesis
        proof(cases "xv = hv")
          case True2 : True

          have In_t' : "(xk, hv) \<in> set t"
            using Cons.prems H  Hx Xkv False True2 Cons.IH[OF Ord_tl]
            using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
            by(auto)

          have "hv \<in> snd ` set t"
            using imageI[OF In_t', of snd]
            by auto

          then show ?thesis
            using Cons.prems H  Hx Xkv False True2 Cons.IH[OF Ord_tl]
            using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
            by(auto)
        next
          case False2 : False
          show ?thesis
            using Cons.prems H  Hx Xkv False False2 Cons.IH[OF Ord_tl]
            using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
            by(auto)
        qed
      qed
    qed
  qed
qed

lemma str_ord_update_concat :
  fixes l :: "('k :: linorder * 'v) list"
  assumes "strict_order (map fst l)"
  assumes "k \<notin> fst ` set l"
  shows "\<exists> pre post .
    str_ord_update k v l =
      pre @ [(k, v)] @ post \<and>
    l = pre @ post"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case by auto
next
  case (Cons h t )

  obtain hk hv where H: "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using Cons.prems H strict_order_tl
    by auto

  show ?case
  proof(cases "hk < k")
    case True

    have Notin' : "k \<notin> fst ` set t"
      using Cons.prems
      by auto

    obtain pre0 post0 where Ind :
      "str_ord_update k v t = pre0 @ (k, v) # post0" "t = pre0 @ post0"
      using Cons.prems H Cons.IH[OF Ord_tl Notin', of v]
      by auto

    have Conc' : "str_ord_update k v (h # t) = (h # pre0) @ [(k, v)] @ post0 \<and> h # t = (h # pre0) @ post0"
      using Ind H True
      by(auto)

    then show ?thesis
      by blast
  next
    case False
    then show ?thesis
      using Cons.prems H
      by(auto)
  qed
qed

lemma oalist_flip'_map_snd :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  assumes "distinct (map snd l)"
  shows "distinct (map snd (oalist_flip' l))"
  using assms
proof(induction l)
  case Nil
  then show ?case by auto
next
  case (Cons h t )

  obtain hk hv where H: "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using Cons.prems H strict_order_tl
    by auto

  have Dist_tl : "distinct (map snd t)"
    using Cons.prems H
    by auto

  have Hk_notin : "hk \<notin> fst ` set t"
    using strict_order_distinct[OF Cons.prems(1)] H
    by(auto)

  have Hv_notin : "hv \<notin> fst ` set (oalist_flip' t)"
    using oalist_flip'_set[OF Ord_tl Dist_tl] H Cons.prems
    apply(auto)
    apply(drule_tac f = snd in imageI)
    apply(auto)
    done

  have Hk_notin' : "hk \<notin> snd ` set (oalist_flip' t)"
    using oalist_flip'_set[OF Ord_tl Dist_tl] H Cons.prems Hk_notin
    apply(auto)
    apply(drule_tac f = fst in imageI)
    apply(auto)
    done

  obtain pre post where Split : 
    "(str_ord_update hv hk (oalist_flip' t)) =
     pre @ [(hv, hk)] @ post" "oalist_flip' t = pre @ post"
    using str_ord_update_concat[OF oalist_flip'_correct[OF Ord_tl] Hv_notin]
    by blast

  have Conc' : "distinct (map snd (pre @ [(hv, hk)] @ post))"
    unfolding map_append distinct_append 
    using Cons.prems Split(2) Cons.IH[OF Ord_tl Dist_tl] H
    using oalist_flip'_set[OF Ord_tl Dist_tl] Hk_notin'
    by(auto)

  have Conc'' : "distinct
     (map snd
       (str_ord_update hv hk (oalist_flip' t)))"
    using Conc'
    unfolding Split(1)
    by auto

  show ?case
    using Cons.prems Cons.IH[OF Ord_tl] H
    using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of hv hk]
    using Conc''
    by(auto)
qed

lemma oacons'_cons :
  assumes Cons' : "oacons' kh vh l = Some l'"
  shows "l' = ((kh, vh)#l)"
proof(cases l)
  case Nil
  then show ?thesis using Cons'
    by(auto)
next
  case (Cons a list)
  then show ?thesis 
    using Cons'
    by(cases a; auto split: if_splits)
qed

lemma get_cons :
  fixes l l' :: "('k :: linorder, 'v) oalist"
  assumes "oacons kh vh l = Some l'"
  assumes "get l k = Some v"
  shows "get l' k = Some v"
  using assms
proof(transfer)
  fix l :: "('k :: linorder * 'v) list"
  show "\<And>kh vh l' k v.
       strict_order (map fst l) \<Longrightarrow>
       strict_order (map fst l') \<Longrightarrow>
       oacons' kh vh l = Some l' \<Longrightarrow>
       map_of l k = Some v \<Longrightarrow> map_of l' k = Some v"
  proof(induction l)
    case Nil
    then show ?case 
      by(auto)
  next
    case (Cons h' t')

    obtain kh' vh' where H' : "h' = (kh', vh')"
      by(cases h'; auto)

    have Ord' : "strict_order (map fst t')"
      using Cons.prems strict_order_tl H'
      by(fastforce)

    have Oacons' : "oacons' kh' vh' t' = Some (h' # t')"
      using oacons'_destruct Cons.prems unfolding H'
      by(fastforce)

    have L' : "l' = ((kh,  vh) # (kh', vh') # t')"
      using Cons.prems oacons'_cons H'
      by(fastforce)

    have Lt : "kh < kh'"
      using strict_order_unfold[OF Cons.prems(2), of 1 0] L'
      by(auto)

    have Notin : "map_of t' kh = None"
    proof(cases "map_of t' kh")
      case None
      then show ?thesis by auto
    next
      case (Some vbad)
      then have In_bad : "(kh, vbad) \<in> set t'"
        using map_of_SomeD
        by fastforce

      have In_bad2 : "kh \<in> fst ` set t'"
        using imageI[OF In_bad, of fst]
        by auto

      then have False
        using strict_order_distinct[OF Cons.prems(2)] H'
        unfolding L'
        by(auto)

      then show ?thesis by auto

    qed

    show ?case
      using Cons.prems H' L' Lt Notin
      by(cases "kh = kh'"; auto)
  qed
qed
  

lemma get_tl :
  fixes l l' :: "('k :: linorder, 'v) oalist"
  assumes "oacons kh vh l = Some l'"
  assumes "get l' k = Some v"
  assumes "k \<noteq> kh"
  shows "get l k = Some v"
  using assms
proof(transfer)
  fix l :: "('k :: linorder * 'v) list"
  show "\<And>kh vh l l' k v .
       strict_order (map fst l) \<Longrightarrow>
       strict_order (map fst l') \<Longrightarrow>
       oacons' kh vh l = Some l' \<Longrightarrow>
       map_of l' k = Some v \<Longrightarrow> k \<noteq> kh \<Longrightarrow> map_of l k = Some v"
  proof(induction l)
    case Nil
    have L' : "l' = ((kh, vh)#l)"
      using Nil oacons'_cons
      by fastforce

    then show ?case using Nil
      by(auto)
  next
    case (Cons h' t')

    have L' : "l' = ((kh, vh)#l)"
      using Cons.prems oacons'_cons
      by fastforce

    show ?case using Cons.prems unfolding L'
      by(auto)
  qed
qed

lemma get_hd :
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "oacons kh vh l = Some l'"
  shows "get l' kh = Some vh"
  using assms
proof(transfer)
  fix l :: "('k * 'v) list"
  show "\<And>kh vh l'.
       strict_order (map fst l) \<Longrightarrow>
       strict_order (map fst l') \<Longrightarrow>
       oacons' kh vh l = Some l' \<Longrightarrow>
       map_of l' kh = Some vh"
  proof(induction l)
    case Nil
    then show ?case
      by(auto)
  next
    case (Cons lh lt)
    then show ?case 
      by(cases lh; auto split: if_splits)
  qed
qed


lemma oalist_keys_get_Some :
  fixes l1 :: "('k :: linorder, 'v) oalist"
  assumes "oalist_keys l1 = oalist_keys l2"
  assumes "get l1 k = Some v"
  shows "\<exists> v' . get l2 k = Some v'"
  using assms
proof(transfer)
  fix l1 :: "('k * 'v) list"
  show "\<And>l2 k v.
       strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow>
       map fst l1 = map fst l2 \<Longrightarrow>
       map_of l1 k = Some v \<Longrightarrow>
       \<exists>v'. map_of l2 k = Some v'"
  proof(induction l1)
    case Nil
    then show ?case
      by(auto)
  next
    case Cons1 : (Cons h1 t1)

    obtain h1k h1v
      where H1 : "h1 = (h1k, h1v)"
      by(cases h1; auto)

    obtain h2 t2
      where Cons2 : "l2 = h2 # t2"
      using Cons1.prems
      by(auto)

    obtain h2k h2v where
      H2 : "(h2 = (h2k, h2v))"
      by(cases h2; auto)

    show ?case 
    proof(cases "k = h1k")
      case True
      then show ?thesis 
        using Cons1.prems Cons2 H1 H2 
        by(auto)
    next
      case False

      have Get_t1 : "map_of t1 k = Some v"
        using Cons1.prems H1 Cons2 H2 False
        by(auto)

      have Ord_tl1 : "strict_order (map fst t1)"
        using strict_order_tl Cons1.prems H1 False
        by(fastforce)

      then show ?thesis
        using Cons1.prems H1 Cons2 H2
        using Cons1.IH
        by(auto)
    qed

  qed
qed

lemma oalist_keys_get_None :
  fixes l1 :: "('k :: linorder, 'v) oalist"
  assumes "oalist_keys l1 = oalist_keys l2"
  assumes "get l1 k = None"
  shows "get l2 k = None"
  using assms
proof(transfer)
  fix l1 :: "('k * 'v) list"
  show "\<And>l2 k.
       strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow>
       map fst l1 = map fst l2 \<Longrightarrow>
       map_of l1 k = None \<Longrightarrow> map_of l2 k = None"
  proof(induction l1)
    case Nil
    then show ?case by auto
  next
    case Cons1 : (Cons h1 t1)

    obtain h1k h1v
      where H1 : "h1 = (h1k, h1v)"
      by(cases h1; auto)

    obtain h2 t2
      where Cons2 : "l2 = h2 # t2"
      using Cons1.prems
      by(auto)

    obtain h2k h2v where
      H2 : "(h2 = (h2k, h2v))"
      by(cases h2; auto)

    show ?case 
    proof(cases "k = h1k")
      case True
      then show ?thesis 
        using Cons1.prems Cons2 H1 H2 
        by(auto)
    next
      case False

      have Get_t1 : "map_of t1 k = None"
        using Cons1.prems H1 Cons2 H2 False
        by(auto)

      have Ord_tl1 : "strict_order (map fst t1)"
        using strict_order_tl Cons1.prems H1 False
        by(fastforce)

      then show ?thesis
        using Cons1.prems H1 Cons2 H2
        using Cons1.IH
        by(auto)
    qed
  qed
qed

lemma get_to_oalist :
  fixes l :: "('k :: linorder * 'v) list"
  assumes "distinct (map fst l)"
  shows "get (to_oalist l) k = map_of l k"
  using assms
proof(induction l arbitrary: k)
  case Nil
  then show ?case using empty_get
    by(auto)
next
  case (Cons h t)

  obtain hk hv where H : "h = (hk, hv)"
    by(cases h; auto)

  show ?case
  proof(cases "k = hk")
    case True
    then show ?thesis using Cons H oalist_update_get_eq[of hk hv "to_oalist t"]
      by(auto)
  next
    case False
    then show ?thesis using Cons H oalist_update_get_neq[of hk k hv]
      by(auto)
  qed
qed

lemma oalist_keys_update_eq :
  fixes l1 :: "('k :: linorder, 'v1) oalist"
  fixes l2 :: "('k :: linorder, 'v2) oalist"
  assumes "oalist_keys l1 = oalist_keys l2"
  shows "oalist_keys (update n v1 l1) = oalist_keys (update n v2 l2)"
  using assms
proof(transfer)
  fix l1 :: "('k :: linorder * 'v1) list"
  show "\<And> (l2 :: ('k :: linorder * 'v2) list) n v1 v2 .
       strict_order (map fst l1) \<Longrightarrow>
       strict_order (map fst l2) \<Longrightarrow>
       map fst l1 = map fst l2 \<Longrightarrow>
       map fst (str_ord_update n v1 l1) = map fst (str_ord_update n v2 l2)"
  proof(induction l1)
    case Nil
    then show ?case 
      by(auto)
  next
    case (Cons l1h l1t)

    obtain hk l1hv where L1h : "l1h = (hk, l1hv)"
      by(cases l1h; auto)

    obtain l2h l2t where Cons' : "l2 = l2h # l2t"
      using Cons.prems
      by(cases l2; auto)

    obtain l2hv where L2h : "l2h = (hk, l2hv)"
      using Cons.prems L1h Cons'
      by(cases l2h; auto)

    show ?case
    proof(cases "hk < n")
      case True

      have Ord_tl1 : "strict_order (map fst l1t)"
        using strict_order_tl Cons.prems
        by auto

      have Ord_tl2 : "strict_order (map fst l2t)"
        using strict_order_tl Cons.prems Cons'
        by auto

      show ?thesis 
        using Cons.prems L1h Cons' L2h True
        using Cons.IH[OF Ord_tl1 Ord_tl2]
        by(auto)
    next
      case False
      then show ?thesis using Cons.prems L1h Cons' L2h
        by(auto)
    qed
  qed
qed

lemma oalist_flip_update : 
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  assumes "k \<notin> set (oalist_keys l)"
  assumes "v \<notin> set (oalist_keys (oalist_flip l))"
  shows "oalist_flip (update k v l) = update v k (oalist_flip l)"
  using assms
proof(transfer)
  fix l :: "('k :: linorder * 'k) list"
  fix k v
  assume Ord : "strict_order (map fst l)"
  assume Dist : "distinct (map snd l)"
  assume Notin1 : "k \<notin> set (map fst l)"
  assume Notin2 : "v \<notin> set (map fst (oalist_flip' l))"

  have Notin1' : "k \<notin> fst ` set l"
    using Notin1 by auto

  have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
  proof
    fix w
    show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
      by(cases w; auto)
  qed


  have Notin2_alt : "v \<notin> fst ` set (oalist_flip' l)"
    using Notin2
    by auto

  hence "v \<notin> fst ` (\<lambda>(x, y). (y, x)) ` set l"
    using oalist_flip'_set[OF Ord Dist]
    by auto

  hence "v \<notin> (fst o (\<lambda>(x, y). (y, x))) ` set l"
    by auto

  hence Notin2' : "v \<notin> snd ` set l"
    unfolding Fst_flip by auto

  show "oalist_flip' (str_ord_update k v l) = str_ord_update v k (oalist_flip' l)"
    using oalist_flip'_update[OF Ord Dist Notin1' Notin2']
    by auto
qed

lemma oalist_one_one_update : 
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  assumes "k \<notin> set (oalist_keys l)"
  assumes "v \<notin> set (oalist_keys (oalist_flip l))"
  shows "oalist_one_one (update k v l)"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "\<And> v k.
       strict_order (map fst l) \<Longrightarrow>
       distinct (map snd l) \<Longrightarrow>
       k \<notin> set (map fst l) \<Longrightarrow>
       v \<notin> set (map fst (oalist_flip' l)) \<Longrightarrow> distinct (map snd (str_ord_update k v l))"
  proof(induction l)
    case Nil
    then show ?case
      by(auto)
  next
    case (Cons lh lt)

    obtain lhk lhv where Lh : "lh = (lhk, lhv)"
      by(cases lh; auto)

    have Ord_tl : "strict_order (map fst lt)"
      using strict_order_tl Cons.prems
      by auto

    show ?case
    proof(cases "k < lhk")
      case K_lt : True

      show ?thesis
      proof(cases "v = lhv")
        case V_eq : True

        have Lhv_notin : "lhv \<notin> fst ` set (str_ord_update lhv lhk (oalist_flip' lt))"
          using Cons Lh K_lt V_eq
          by(auto)

        then have Lhv_notin' : "lhv \<notin> fst ` (set (oalist_flip' lt) - {x. fst x = lhv} \<union> {(lhv, lhk)})"
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of lhv lhk]
          by auto

        then have False
          by auto

        then show ?thesis by auto
      next
        case V_neq : False

        have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
        proof
          fix w
          show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
            by(cases w; auto)
        qed

        have V_notin : "v \<notin> fst ` set (str_ord_update lhv lhk (oalist_flip' lt))"
          using Cons.prems Lh K_lt V_neq
          by auto

        then have V_notin' : "v \<notin> fst ` (set (oalist_flip' lt) - {x. fst x = lhv} \<union> {(lhv, lhk)})"
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of lhv lhk]
          by auto

        then have V_notin_tl : "v \<notin> fst ` set (oalist_flip' lt)"
          by auto

        then have "v \<notin> fst ` (\<lambda>(x, y). (y, x)) ` set lt"
          using oalist_flip'_set[OF Ord_tl] Cons.prems
          by auto

        then have "v \<notin> (fst o (\<lambda>(x, y). (y, x))) ` set lt"
          by auto

        then have "v \<notin> snd ` set lt"
          unfolding Fst_flip
          by auto

        then show ?thesis
          using Cons.prems Lh K_lt V_neq V_notin_tl
          by(auto)
      qed
    next
      case K_nlt : False

      show ?thesis
      proof(cases "k = lhk")
        case K_eq : True

        then have False
          using Cons.prems Lh
          by auto

        then show ?thesis by auto
      next
        case K_gt' : False

        have K_gt : "lhk < k"
          using K_nlt K_gt'
          by auto

        show ?thesis
        proof(cases "v = lhv")
          case V_eq : True
  
          have Lhv_notin : "lhv \<notin> fst ` set (str_ord_update lhv lhk (oalist_flip' lt))"
            using Cons Lh V_eq
            by(auto)
  
          then have Lhv_notin' : "lhv \<notin> fst ` (set (oalist_flip' lt) - {x. fst x = lhv} \<union> {(lhv, lhk)})"
            using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of lhv lhk]
            by auto
  
          then have False
            by auto
  
          then show ?thesis by auto
        next
          case V_neq : False

          have Lhv_notin : "lhv \<notin> snd ` set lt"
            using Cons.prems Lh V_neq
            by(auto)

          hence "lhv \<notin> snd ` (set lt - {x. fst x = k} \<union> {(k, v)})"
            using V_neq
            by auto

          hence Lhv_notin' : "lhv \<notin> snd ` set (str_ord_update k v lt)"
            using str_ord_update_set[OF Ord_tl]
            by auto

          have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
          proof
            fix w
            show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
              by(cases w; auto)
          qed
  
          have V_notin : "v \<notin> fst ` set (str_ord_update lhv lhk (oalist_flip' lt))"
            using Cons.prems Lh V_neq
            by auto
  
          then have V_notin' : "v \<notin> fst ` (set (oalist_flip' lt) - {x. fst x = lhv} \<union> {(lhv, lhk)})"
            using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl], of lhv lhk]
            by auto
  
          then have V_notin_tl : "v \<notin> fst ` set (oalist_flip' lt)"
            by auto
  
  
          show ?thesis
            using Cons.prems Lh K_gt V_neq Lhv_notin'
            using Cons.IH[OF Ord_tl, of k v] V_notin_tl
            by(auto)
        qed
      qed
    qed
  qed
qed

lemma oalist_keys_update_set :
  fixes l :: "('k :: linorder, 'v) oalist"
  shows "set (oalist_keys (update k v l)) = {k} \<union> set (oalist_keys l)"
proof(transfer)
  fix l :: "('k * 'v) list"
  show "\<And>k v .
       strict_order (map fst l) \<Longrightarrow>
       set (map fst (str_ord_update k v l)) = {k} \<union> set (map fst l)"
  proof(induction l)
    case Nil
    then show ?case by auto
  next
    case (Cons lh lt)

    obtain lhk lhv where Lh : "lh = (lhk, lhv)"
      by(cases lh; auto)

    show ?case
    proof(cases "k < lhk")
      case K_lt : True

      show ?thesis using Cons Lh K_lt
        by(auto)
    next
      case K_nlt : False

      show ?thesis
      proof(cases "k = lhk")
        case K_eq : True

        show ?thesis using Cons Lh K_eq
          by(auto)
      next
        case K_neq : False

        have K_gt : "lhk < k"
          using K_nlt K_neq
          by auto

        have Ord_tl : "strict_order (map fst lt)"
          using strict_order_tl Cons.prems
          by auto

        show ?thesis
          using Cons.prems Lh K_gt
          using Cons.IH[OF Ord_tl]
          by(auto)
      qed
    qed
  qed
qed

lemma str_ord_update_snd_distinct :
  fixes l :: "('k :: linorder * 'k) list" 
  assumes "strict_order (map fst l)"
  assumes "distinct (map snd l)"
  assumes "k \<notin> set (map fst l)"
  assumes "v \<notin> set (map snd l)"
  shows "distinct (map snd (str_ord_update k v l))"
  using assms
proof(induction l arbitrary: k v)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh :
    "lh = (lhk, lhv)"
    by(cases lh; auto)

  have Ord_tl : "strict_order (map fst lt)"
    using Cons.prems strict_order_tl
    by auto

  have Notin2' : "lhv \<notin> snd ` set (str_ord_update k v lt)"
    using Cons.prems Lh
    using str_ord_update_set[OF Ord_tl]
    by(auto)

  have Dist_tl : "distinct (map snd (str_ord_update k v lt))"
    using Cons.prems Lh Cons.IH[OF Ord_tl, of k v]
    by auto

  show ?case using Cons Lh Notin2' Dist_tl
    by(auto)
qed

lemma oalist_one_one_flip : 
  fixes l :: "('k :: linorder, 'k) oalist" 
  assumes "oalist_one_one l"
  shows "oalist_one_one (oalist_flip l)"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "strict_order (map fst l) \<Longrightarrow>
         distinct (map snd l) \<Longrightarrow> distinct (map snd (oalist_flip' l))"
    using oalist_flip'_map_snd
    by auto
qed

lemma oalist_flip_flip : 
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  shows "oalist_flip (oalist_flip l) = l"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "strict_order (map fst l) \<Longrightarrow>
         distinct (map snd l) \<Longrightarrow> oalist_flip' (oalist_flip' l) = l"
  proof(induction l)
    case Nil
    then show ?case by auto
  next
    case (Cons lh lt)

    obtain lhk lhv where Lh :
      "lh = (lhk, lhv)"
      by(cases lh; auto)

    have Ord_tl : "strict_order (map fst lt)"
      using strict_order_tl Cons.prems
      by auto

    have Flip_distinct_tl : " distinct (map snd (oalist_flip' lt))"
      using oalist_flip'_map_snd[OF Ord_tl] Cons.prems Lh
      by auto

    have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
    proof
      fix w
      show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
        by(cases w; auto)
    qed

    have Snd_flip : "snd o (\<lambda>(x, y). (y, x)) = fst"
    proof
      fix w
      show "(snd \<circ> (\<lambda>(x, y). (y, x))) w = fst w"
        by(cases w; auto)
    qed

    have Flip_set : "set (oalist_flip' lt) = (\<lambda>(x, y). (y, x)) ` set lt"
      using oalist_flip'_set[OF Ord_tl] Cons.prems Lh
      by auto

    have Notin1 : "lhv \<notin> snd ` set (lt)"
      using Cons.prems Lh by auto

    hence "lhv \<notin> (fst o (\<lambda>(x, y). (y, x))) ` set lt"
      unfolding sym[OF Fst_flip]
      by auto

    hence "lhv \<notin> fst ` (\<lambda>(x, y). (y, x)) ` set lt"
      unfolding image_comp
      by auto

    hence Notin1' : "lhv \<notin> fst ` set (oalist_flip' lt)"
      using Cons.prems Lh unfolding Flip_set
      by(auto)

    have Notin2 : "lhk \<notin> fst ` set lt"
      using strict_order_distinct[OF Cons.prems(1)] Cons.prems Lh
      by auto

    hence "lhk \<notin> (snd o (\<lambda>(x, y). (y, x))) ` set lt"
      unfolding sym[OF Snd_flip]
      by auto

    hence "lhk \<notin> snd ` (\<lambda>(x, y). (y, x)) ` set lt"
      unfolding image_comp
      by auto

    hence Notin2' : "lhk \<notin> snd ` set (oalist_flip' lt)"
      using Cons.prems Lh unfolding Flip_set
      by(auto)

    have Flip_update : "oalist_flip' (str_ord_update lhv lhk (oalist_flip' lt)) =
      str_ord_update lhk lhv (oalist_flip' (oalist_flip' lt))"
      using oalist_flip'_update[OF oalist_flip'_correct[OF Ord_tl] Flip_distinct_tl Notin1' Notin2']
      using Cons.prems Lh
      by(auto)

    have Conc' : "str_ord_update lhk lhv lt = (lhk, lhv) # lt"
    proof(cases lt)
      case Nil' : Nil
      then show ?thesis by auto
    next
      case Cons' : (Cons lh' lt')

      obtain lh'k lh'v where Lh' : "lh' = (lh'k, lh'v)"
        by(cases lh'; auto)

      have Lt : "lhk < lh'k"
        using strict_order_unfold[OF Cons.prems(1), of 1 0]
        using Lh Cons' Lh'
        by(auto)

      show ?thesis
        using Cons' Lh' Lt
        by(auto)
    qed

    show ?case using Cons.prems Lh Cons.IH[OF Ord_tl] Flip_update Conc'
      by(auto)
  qed
qed

lemma strict_order_oalist_keys :
  fixes l :: "('k :: linorder, 'v) oalist"
  shows "strict_order (oalist_keys l)"
  by(transfer; auto)

lemma strict_order_unique_set :
  assumes "strict_order l1"
  assumes "strict_order l2"
  assumes "set l1 = set l2"
  shows "l1 = l2"
  using assms
proof(induction l1 arbitrary: l2)
  case Nil
  then show ?case
    by(auto)
next
  case Cons1 : (Cons h1 t1)

  obtain h2 t2 where Cons2 : "l2 = h2 # t2"
    using Cons1
    by(cases l2; auto)

  have Ord_tl1 : "strict_order t1"
    using strict_order_tl Cons1.prems
    by auto

  have Ord_tl2 : "strict_order t2"
    using strict_order_tl Cons1.prems Cons2
    by auto

  have Dist1 : "distinct (h1 # t1)"
    using strict_order_distinct[of "h1 # t1"] Cons1.prems
    by auto

  have Dist2 : "distinct (h2 # t2)"
    using strict_order_distinct[of "h2 # t2"] Cons1.prems Cons2
    by auto

  show ?case
  proof(cases "h1 = h2")
    case True

    have Set_eq_tl : "set t1 = set t2"
      using Cons1.prems Cons2 True Dist1 Dist2
      by(auto)

    show ?thesis 
      using Cons1.prems Cons2 True
      using Cons1.IH[OF Ord_tl1 Ord_tl2 Set_eq_tl]
      by(simp)
  next
    case Neq : False

    have Sets_eq : "insert h1 (set t1) = insert h2 (set t2)"
      using Cons1.prems Cons2
      by(simp)

    have H1_in2 : "h1 \<in> set t2"
      using Sets_eq Neq Dist1
      by(auto)

    have H2_in1 : "h2 \<in> set t1"
      using Sets_eq Neq Dist2
      by(auto)

    show ?thesis
    proof(cases "h1 < h2")
      case Lt : True

      obtain ix where Ix : "t2 ! ix = h1" "ix < length t2"
        using H1_in2
        unfolding in_set_conv_nth
        by auto

      have Bad : "h2 < h1"
        using strict_order_unfold[OF Cons1.prems(2), of "1 + ix" 0]
          Ix Cons1.prems Cons2
        by(auto)

      then have False using Lt by auto

      then show ?thesis by auto
    next

      case Gt' : False

      have Gt : "h2 < h1"
        using Neq Gt'
        by auto

      obtain ix where Ix : "t1 ! ix = h2" "ix < length t1"
        using H2_in1
        unfolding in_set_conv_nth
        by auto

      have Bad : "h1 < h2"
        using strict_order_unfold[OF Cons1.prems(1), of "1 + ix" 0]
          Ix Cons1.prems Cons2
        by(auto)

      then have False using Gt by auto

      then show ?thesis by auto
    qed
  qed
qed

lemma oacons_impl_of : 
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "oacons hk hv t = Some l"
  shows "impl_of l = (hk, hv) # (impl_of t)"
  using assms
proof(transfer)
  fix t :: "('k * 'v) list"
  fix hk hv l
  show "strict_order (map fst t) \<Longrightarrow>
       strict_order (map fst l) \<Longrightarrow>
       oacons' hk hv t = Some l \<Longrightarrow>
       l = (hk, hv) # t"
    by(cases t; auto split: if_splits)
qed

lemma oacons_update :
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "oacons hk hv t = Some l"
  shows "update hk hv t = l"
  using assms
proof(transfer)
  fix hk hv
  fix t l :: "('k * 'v) list"

  assume Ord1 : "strict_order (map fst t)"
  assume Ord2 : "strict_order (map fst l)"
  assume Oacons : "oacons' hk hv t = Some l"
  show "str_ord_update hk hv t = l"
  proof(cases t)
    case Nil
    then show ?thesis 
      using Oacons
      by auto
  next
    case (Cons lh' lt)

    obtain lh'k lh'v where Lh' :
      "lh' = (lh'k, lh'v)"
      by(cases lh'; auto)

    show ?thesis using Cons Oacons Lh'
      by(auto)
  qed
qed

lemma to_oalist_impl_of : 
  fixes l :: "('k :: linorder, 'v) oalist"
  assumes "l' = impl_of l"
  shows "to_oalist l' = l"
  using assms
proof(induction l' arbitrary: l)
  case Nil
  then show ?case 
    by(clarsimp;transfer; auto)
next
  case (Cons l'h l't)

  obtain l'hk l'hv where L'h :
    "l'h = (l'hk, l'hv)"
    by(cases l'h; auto)

  consider (1) "l = empty"
    | (2) lhk lhv lt where
      "oacons lhk lhv lt = Some l"
    using oalist_cases[of l]
    by auto
  then show ?case
  proof cases
    case 1

    have "l'h # l't = impl_of Oalist.empty"
      using Cons 1 by auto

    then have False
      by (transfer; auto)

    then show ?thesis by auto
  next
    case 2

    have Eqs :
      "l'hk = lhk" "l'hv = lhv" "l't = impl_of lt"
      using oacons_impl_of[OF 2] Cons.prems L'h
      by(auto)

    have L_unfold : "(lhk, lhv) # impl_of lt = impl_of l"
      using Cons.prems L'h Cons.IH[OF Eqs(3)] Eqs
      by(auto)

    have Conc' : "update lhk lhv lt = l"
      using oacons_update[OF 2]
      by auto

    show ?thesis using Cons.prems L'h Cons.IH[OF Eqs(3)]
        sym[OF L_unfold] Conc'
      by(auto)
  qed
qed


end