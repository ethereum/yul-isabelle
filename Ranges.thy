theory Ranges imports Main
begin

(* representation of (disjunctions of) ranges of natural numbers, inclusive *)
type_synonym ranges' = "(nat * nat) list"

fun ranges'_valid_sub :: "nat \<Rightarrow> ranges' \<Rightarrow> bool" where
"ranges'_valid_sub _ [] = True"
| "ranges'_valid_sub x ((n1, n2)#t) =
   (x \<le> n1 \<and> n1 < n2 \<and> ranges'_valid_sub n2 t)"

(*
fun ranges'_valid :: "ranges' \<Rightarrow> bool" where
"ranges'_valid [] = True"
| "ranges'_valid [(n1, n2)] = (n1 < n2)"
| "ranges'_valid ((n1, n2)#(m1, m2)#t) =
   (n1 < n2 \<and> n1 \<le> m1 \<and> ranges'_valid ((m1, m2)#t))"
*)

fun ranges'_valid :: "ranges' \<Rightarrow> bool" where
"ranges'_valid rg = (ranges'_valid_sub 0 rg)"

typedef ranges =
  "{l :: ranges' . ranges'_valid l}"
proof
  show "[] \<in> {l. ranges'_valid l}" by auto
qed
setup_lifting type_definition_ranges

lift_definition rg_empty :: ranges is "[]" by auto

fun range_ranges' :: "nat \<Rightarrow> nat \<Rightarrow> ranges'" where
"range_ranges' n1 n2 =
  (if n1 < n2 then [(n1, n2)] else [])"

fun mk_ranges'_sub :: "nat \<Rightarrow> ranges' \<Rightarrow> ranges'" where
"mk_ranges'_sub _ [] = []"
| "mk_ranges'_sub x ((n1, n2)#t) =
   (if (x \<le> n1) then
    (if (n1 < n2) then (n1, n2)#mk_ranges'_sub n2 t 
     else mk_ranges'_sub x t)
    else mk_ranges'_sub x t)"

fun mk_ranges' :: "ranges' \<Rightarrow> ranges'" where
"mk_ranges' l = mk_ranges'_sub 0 l"

(*
lemma mk_ranges'_tl :
  assumes H : "ranges'_valid (h#t)"
  shows "ranges'_valid t" using assms
proof(induction t arbitrary: h)
  case Nil
  then show ?case by auto
next
  case (Cons n t)
  obtain h1 h2 where Hh : "h = (h1, h2)" by(cases h; auto)
  obtain n1 n2 where N : "n = (n1, n2)" by(cases n; auto)
  then show ?case  using Cons Hh
    by(auto)
qed
*)
lemma ranges'_sub_valid_tl :
  assumes H : "ranges'_valid_sub x ((n1, n2)#t)"
  shows "ranges'_valid_sub n2 t" using H
  by(auto)

lemma mk_ranges'_sub_valid :
  "ranges'_valid_sub x (mk_ranges'_sub x l)"
proof(induction l arbitrary: x)
case Nil
then show ?case by auto
next
  case (Cons n t)
  obtain n1 n2 where N: "n = (n1, n2)" by (cases n; auto)
  show ?case 
  proof(cases t)
  case Nil' : Nil
    then show ?thesis using Cons Nil' N by auto
  next
    case Cons' : (Cons m t')
    obtain m1 m2 where M : "m = (m1, m2)" by(cases m; auto)
    show ?thesis using Cons Cons' N M by(auto)
  qed
qed

lemma mk_ranges'_valid : "ranges'_valid (mk_ranges' l)"
  using mk_ranges'_sub_valid by auto

lift_definition mk_ranges :: "ranges' \<Rightarrow> ranges" is mk_ranges'
  using mk_ranges'_valid by auto

fun set_of_ranges' :: "ranges' \<Rightarrow> nat set" where
"set_of_ranges' [] = {}"
| "set_of_ranges' ((n1, n2)#m) = 
   {n1..<n2} \<union> set_of_ranges' m"

(* TODO: are we handling the no overlap cases correctly? *)
fun union_ranges' :: "ranges' \<Rightarrow> ranges' \<Rightarrow> ranges'"
  where
"union_ranges' [] [] = []"
| "union_ranges' ((l1, l2)#lt) [] = ((l1, l2)#lt)"
| "union_ranges' [] ((r1, r2)#rt) = ((r1, r2)#rt)"
| "union_ranges' ((l1, l2)#lt) ((r1, r2)#rt) =
   (if l1 < r1
    then
      (if l2 < r1
       then \<comment> \<open>no overlap, l2 < r1\<close>
         (l1, l2) # union_ranges' lt ((r1, r2)#rt)
       else (if l2 < r2
             then \<comment> \<open>merge, l2 < r2\<close>
               union_ranges' lt ((l1, r2) # rt)
             else \<comment> \<open>l subsumes r\<close>
               union_ranges' ((l1, l2)#lt) rt))
    else
      (if r2 < l1
       then \<comment> \<open>no overlap, r2 < l1\<close>
         (r1, r2) # union_ranges' ((l1, l2)#lt) rt
       else (if r2 < l2
             then \<comment> \<open>merge, r2 < l2\<close>
               union_ranges' ((r1, l2)#lt) rt
             else \<comment> \<open>r subsumes l\<close>
               union_ranges' lt ((r1, r2)#rt))))"

(* TODO: make sure we are handling edge cases correctly. *)

fun diff_ranges' :: "ranges' \<Rightarrow> ranges' \<Rightarrow> ranges'" where
"diff_ranges' [] _ = []"
| "diff_ranges' ((l1, l2)#lt) [] = ((l1, l2)#lt)"
| "diff_ranges' ((l1, l2)#lt) ((r1, r2)#rt) = 
   (if l1 < r1 
    then
      (if l2 < r1
       then \<comment> \<open>no overlap, l2 < r1\<close>
         (l1, l2) # diff_ranges' lt ((r1, r2)#rt)
       else (if l2 < r2
             then \<comment> \<open>clip between r1 and l2\<close>
               (l1, r1) # diff_ranges' lt ((r1, r2) # rt)
             else \<comment> \<open>l subsumes r, clip between r1 and r2\<close>
               (if l2 > r2 then (l1, r1) # diff_ranges' ((r2, l2)#lt) rt
                           else (l1, r1) # diff_ranges' lt rt)))
    else
      (if r2 < l1
       then \<comment> \<open>no overlap, r2 < l1\<close>
         diff_ranges' ((l1, l2)#lt) rt
       else (if r2 < l2
             then \<comment> \<open>clip between, l1 and r2\<close>
                diff_ranges' ((r2, l2)#lt) (rt)
             else \<comment> \<open>r subsumes l, complete deletion\<close>
                diff_ranges' lt ((r1, r2)#rt))))
    "

lift_definition set_of_ranges :: "ranges \<Rightarrow> nat set" is set_of_ranges' .

fun member_ranges' :: "nat \<Rightarrow> ranges' \<Rightarrow> bool" where
"member_ranges' x [] = False"
| "member_ranges' x ((n1, n2)#t) =
   (if x < n2
    then
      (if x < n1 then False else True)
    else
      member_ranges' x t)"

lift_definition member_ranges :: "nat \<Rightarrow> ranges \<Rightarrow> bool" is member_ranges' . 

lemma member_ranges'_spec :
  assumes H : "ranges'_valid r"
  shows "member_ranges' x r = ( x \<in> set_of_ranges' r)" using assms
proof(induction r arbitrary: x)
  case Nil
  then show ?case by auto
next
  case (Cons n r)
  obtain n1 n2 where N: "n = (n1, n2)" by(cases n; auto)
  show ?case
  proof(cases r)
    case Nil' : Nil
    then show ?thesis using Cons N
      by(auto)
    next
      case Cons' : (Cons m r')
      obtain m1 m2 where M: "m = (m1, m2)" by(cases m; auto)
      show ?thesis  using Cons.prems Cons.IH[of x] Cons' N M
        by(auto)
    qed
qed

lemma member_ranges_spec :
  "member_ranges x r = (x \<in> set_of_ranges r)" 
proof(transfer)
  show "\<And>x r. ranges'_valid r \<Longrightarrow> member_ranges' x r = (x \<in> set_of_ranges' r)"
    using member_ranges'_spec by auto
qed
(*
lemma ranges'_valid_sub_alt1 :
  "ranges'_valid_sub x r \<Longrightarrow>
   (\<exists>! 
*)

(*
lemma union_ranges'_valid'  :
  assumes H1 : "ranges'_valid_sub x l"
  assumes H2 : "ranges'_valid_sub x' r"
  assumes H3 : "u = union_ranges' l r"
  shows "ranges'_valid_sub (min x x') u" using assms
proof(induction u arbitrary: x x' l r)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons ua u)
  obtain ua1 ua2 where Ua : "ua = (ua1, ua2)" by(cases ua; auto)
  show ?case
  proof(cases l)
    case Nil_l : Nil
    then show ?thesis 
    proof(cases r)
      case Nil_r : Nil
      then show ?thesis
        using Cons Nil_l by(auto)
    next
      case Cons_r : (Cons ra r')
      obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)
      show ?thesis using Cons Nil_l Cons_r Ra by(auto)
    qed
  next
    case Cons_l : (Cons la l')
    obtain la1 la2 where La : "la = (la1, la2)" by(cases la; auto)
    show ?thesis
    proof(cases r)
      case Nil_r : Nil
      then show ?thesis
        using Cons Cons_l La by auto
    next
      case Cons_r : (Cons ra r')
      obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)
      show ?thesis
      proof(cases "la1 < ra1")
        case T : True
        then show ?thesis 
        proof(cases "la2 < ra1")
          case TT : True
          then show ?thesis
            using Cons.prems Cons_l Cons_r La Ra T TT Cons.IH[of la2 l' ra1 "(ra1, ra2) # r'"]
            by(auto simp add: min_def)
        next
          case TF : False
          then show ?thesis
          proof(cases "la2 < ra2")
            case TFT : True
            then show ?thesis using Cons.prems  Ua Cons_l Cons_r La Ra T TF
                 Cons.IH
              apply(auto)
          next
            case TFF : False
            then show ?thesis using Cons.prems Cons' La Ra T TF Cons.IH
              apply(auto)
          qed
        qed
      next
        case F : False
        then show ?thesis 
        proof(cases "ra2 < la1")
          case FT : True
          then show ?thesis sorry
        next
          case FF : False
          then show ?thesis
          proof(cases "ra2 < la2")
          case FFT : True
            then show ?thesis sorry
          next
            case FFF : False
            then show ?thesis 
            using Cons.prems  Cons' La Ra F FF Cons.IH[OF Vl, of "min x x'" r]
              by(auto simp add: min_def)
          qed
        qed
      qed
    qed

        
    qed

  qed

  show ?case using Cons
    apply(cases l; auto)

qed
*)

(*
lemma either_list_induct :
  assumes N : "P [] []"
  assumes C1 : "\<And> v l r . P l r \<Longrightarrow> P (v#l) r"
  assumes C2 : "\<And> v l r . P l r \<Longrightarrow> P l (v#r)"
  assumes C3 : "\<And> vl vr l r . P l r \<Longrightarrow> P (vl#l) (vr#r)"
  shows "P l1 l2" using assms
proof(induction l1 arbitrary: P l2)
  case Nil1 : Nil
  then show ?case
  proof(induction x )
    case Nil2 : Nil
    then show ?case by auto
  next
    case Cons2 : (Cons a2 l2)
    then show ?case using Nil1
      by(auto)
  qed
next
  case Cons1 : (Cons a1 l1)
  show ?case using Cons1.prems
  proof(induction x )
    case Nil2 : Nil
    show ?case using Cons1.IH[of P] Cons1.prems
      by(auto)
  next
    case Cons2 : (Cons a2 l2)
    then show ?case by(auto)
  qed
qed
*)
(*
lemma either_list_induct :
  assumes N : "P [] []"
  assumes C1 : "\<And> vl vr l r . P l r \<Longrightarrow> P (vl#l) r \<and> P l (vr#r) \<and> P (vl#l) (vr#r)"
  shows "P l1 l2" using assms
proof(induction l1 arbitrary: P l2)
  case Nil1 : Nil
  then show ?case
  proof(induction x )
    case Nil2 : Nil
    then show ?case by auto
  next
    case Cons2 : (Cons vr r)
    then show ?case using Nil1
      by(auto)
  qed
next
  case Cons1 : (Cons a1 l1)
  show ?case using Cons1.prems
  proof(induction x )
    case Nil2 : Nil
    show ?case using Cons1.IH[of P] Cons1.prems
      by(auto)
  next
    case Cons2 : (Cons a2 l2)
    then show ?case by(auto)
  qed
qed



lemma union_ranges'_valid :
  assumes H1 : "ranges'_valid_sub x l"
  assumes H2 : "ranges'_valid_sub x' r"
  shows "ranges'_valid_sub (min x x') (union_ranges' l r)" using assms
proof(induction l r arbitrary: x x'  rule: either_list_induct)
  case 1
  then show ?case by auto
next
  case (2 la ra l r)
  obtain la1 la2 where La : "la = (la1, la2)" by(cases la; auto)
  obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)
  show ?case
  proof(cases "la1 < ra1")
    case T : True
    show ?thesis 
    proof(cases "la2 < ra1")
      case TT : True
      show ?thesis
      proof(step+)
        fix x xa
        assume Vl : "ranges'_valid_sub x (la # l)"
        assume Vr : "ranges'_valid_sub xa r"
        show "ranges'_valid_sub (min x xa) (union_ranges' (la # l) r)"
          using Vl Vr T TT La Ra "2.prems" "2.IH"[of la2 xa]
          apply(auto)
      next
        case TF : False
        then show ?thesis
        proof(cases "la2 < ra2")
          case TFT : True
          then show ?thesis sorry
        next
          case TFF : False
          then show ?thesis using "2.prems" Cons La Ra T TF "2.IH"[of la2]
            apply(auto)
        qed
      qed
    next
      case F : False
      then show ?thesis 
      proof(cases "ra2 < la1")
        case FT : True
        then show ?thesis sorry
      next
        case FF : False
        then show ?thesis
        proof(cases "ra2 < la2")
        case FFT : True
          then show ?thesis sorry
        next
          case FFF : False
          then show ?thesis 
          using Cons.prems  Cons' La Ra F FF Cons.IH[OF Vl, of "min x x'" r]
            by(auto simp add: min_def)
        qed
      qed
    qed
  qed
qed
  

  proof(cases r)
    case Nil
    then show ?thesis using 2 La by(auto)
  next
    case (Cons ra ra')
    obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)
    show ?thesis
    proof(cases "la1 < ra1")
      case T : True
      then show ?thesis 
      proof(cases "la2 < ra1")
        case TT : True
        show ?thesis
          using "2.prems" Cons La Ra T TT "2.IH"[of la2 ra1]
          by(auto simp add: min_def)
      next
        case TF : False
        then show ?thesis
        proof(cases "la2 < ra2")
          case TFT : True
          then show ?thesis sorry
        next
          case TFF : False
          then show ?thesis using "2.prems" Cons La Ra T TF "2.IH"[of la2]
            apply(auto)
        qed
      qed
    next
      case F : False
      then show ?thesis 
      proof(cases "ra2 < la1")
        case FT : True
        then show ?thesis sorry
      next
        case FF : False
        then show ?thesis
        proof(cases "ra2 < la2")
        case FFT : True
          then show ?thesis sorry
        next
          case FFF : False
          then show ?thesis 
          using Cons.prems  Cons' La Ra F FF Cons.IH[OF Vl, of "min x x'" r]
            by(auto simp add: min_def)
        qed
      qed
    qed
  qed
qed
    
    qed
    apply(auto)
next
  case (3 ra r)
  obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)
  then show ?case using 3 Ra by auto
next
  case (4 la l ra r)
  obtain la1 la2 where La : "la = (la1, la2)" by(cases la; auto)
  obtain ra1 ra2 where Ra : "ra = (ra1, ra2)" by(cases ra; auto)

  then show ?case using 4
  qed
*)

(*
ranges'_valid_sub z (union_ranges' l r)
ranges'_valid_sub (min x x') (union_ranges' ((la1, la2) # l) r')
*)

(*
lemma union_ranges'_valid :
  assumes H1 : "ranges'_valid_sub x (l)"
  assumes H2 : "ranges'_valid_sub x' r"
  shows "ranges'_valid_sub (min x x') (union_ranges' (lp@l) r)" using assms
proof(induction l arbitrary: lp r x x')
*)

lemma ranges'_valid_sub_weaken :
  assumes H : "ranges'_valid_sub x l"
  assumes Hleq : "x' \<le> x"
  shows "ranges'_valid_sub x' l" using assms
proof(induction l arbitrary: x x')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  obtain a1 a2 where A: "a = (a1, a2)" by (cases a; auto)
  show ?case using Cons A
    by(auto)
qed

lemma union_ranges'_valid :
  assumes H1 : "ranges'_valid_sub x l"
  assumes H2 : "ranges'_valid_sub x' r"
  shows "ranges'_valid_sub (min x x') (union_ranges' l r)" using assms
proof(induction l r arbitrary: x x' rule: union_ranges'.induct)
  case 1
  then show ?case by auto
next
  case (2 l1 l2 lt)
  then show ?case
    by(auto)
next
  case (3 r1 r2 rt)
  then show ?case 
    by(auto)
next
  case (4 l1 l2 lt r1 r2 rt)
  show ?case
  proof(cases "l1 < r1")
    case T : True
    then show ?thesis 
    proof(cases "l2 < r1")
      case TT : True
      then show ?thesis
        using "4.prems" "4.IH"(1)[OF T TT, of l2 r1]
        by(auto simp add: min_def)
    next
      case TF : False
      then show ?thesis
      proof(cases "l2 < r2")
        case TFT : True
        show ?thesis using T TF TFT "4.prems" "4.IH"(2)[of l2 "min x x'"]
          by(auto simp add: min_def)
      next
        case TFF : False

        have "x' \<le> r2" using T TF TFF "4.prems" by auto
        hence "ranges'_valid_sub x' rt"
          using T TF TFF "4.prems" ranges'_valid_sub_weaken
          by(auto)

        then show ?thesis using T TF TFF "4.prems" "4.IH"(3)[of x x']
          by(auto)
      qed
    qed
  next
    case F : False
    then show ?thesis 
    proof(cases "r2 < l1")
      case FT : True
      then show ?thesis using F FT "4.prems" "4.IH"(4)[of l1 r2]
        by(auto simp add: min_def )
    next
      case FF : False
      then show ?thesis
      proof(cases "r2 < l2")
      case FFT : True
        then show ?thesis
        using F FF "4.prems" "4.IH"(5)[of "min x x'" r2] by(auto simp add: min_def)
      next
        case FFF : False

        have "x \<le> l2" using F FF FFF "4.prems" by auto
        hence "ranges'_valid_sub x lt"
          using F FF FFF "4.prems" ranges'_valid_sub_weaken
          by(auto)

        then show ?thesis using F FF FFF "4.prems" "4.IH"(6)[of x x']
          by(auto)
      qed
    qed
  qed
qed



lift_definition union_ranges :: "ranges \<Rightarrow> ranges \<Rightarrow> ranges" is union_ranges' 
  using union_ranges'_valid[of 0 _ 0] by auto

(* maybe we can do without induction? *)
lemma union_ranges'_spec :
  assumes Vl : "ranges'_valid_sub x l"
  assumes Vr : "ranges'_valid_sub x' r"
  shows "set_of_ranges' (union_ranges' l r) =
         set_of_ranges' l \<union> set_of_ranges' r" using assms
proof(induction l r arbitrary: x x' rule: union_ranges'.induct)
  case 1
  then show ?case by auto
next
  case (2 l1 l2 lt)
  then show ?case by auto
next
  case (3 r1 r2 rt)
  then show ?case by auto
next
  case (4 l1 l2 lt r1 r2 rt)
  then show ?case 
    by(auto)
qed

lemma union_ranges_spec : 
  "set_of_ranges (union_ranges l r) =
   set_of_ranges l \<union> set_of_ranges r"
  using union_ranges'_spec
  by(transfer; auto)

lemma ranges'_valid_sub_set :
  assumes H : "ranges'_valid_sub x r"
  assumes Helm : "n \<in> set_of_ranges' r"
  shows "x \<le> n" using assms
proof(induction r arbitrary: n x)
  case Nil
  then show ?case by auto
next
  case (Cons a r)
  obtain a1 a2 where A: "a = (a1, a2)" by(cases a; auto)
  then show ?case using Cons.prems Cons.IH[of a2 n]
    by(auto)
qed

lemma set_diff_fact1 :
  assumes H : "A \<inter> C = {}"
  shows "A \<union> (B - C) = (A \<union> B) - C" using assms
  by(blast)

lemma diff_ranges'_valid :
  assumes H1 : "ranges'_valid_sub x l"
  assumes H2 : "ranges'_valid_sub x' r"
  shows "ranges'_valid_sub x (diff_ranges' l r)" using assms
proof(induction l r arbitrary: x x' rule: diff_ranges'.induct)
  case (1 uu)
  then show ?case by auto
next
  case (2 l1 l2 lt)
  then show ?case by auto
next
  case (3 l1 l2 lt r1 r2 rt)
  then show ?case 
  proof(cases "l1 < r1")
    case T : True
    show ?thesis
    proof(cases "l2 < r1")
      case TT : True
      show ?thesis using T TT "3.prems" "3.IH"(1) 
        by(auto)
    next
      case TF : False
      show ?thesis
      proof(cases "l2 < r2")
        case TFT : True
        show ?thesis using T TF TFT "3.prems" "3.IH"(2)[of r1 x']
            ranges'_valid_sub_weaken
          by(auto)
      next
        case TFF : False
        show ?thesis 
        proof(cases "l2 > r2")
          case TFFT : True
          then show ?thesis using T TF TFF TFFT 
              "3.prems" "3.IH"(3) ranges'_valid_sub_weaken
            by(auto)
        next
          case TFFF: False
          show ?thesis using T TF TFF TFFF "3.prems" "3.IH"(4)
              ranges'_valid_sub_weaken
            by(auto)
        qed
      qed
    qed
  next
    case F :False
    show ?thesis
    proof(cases "r2 < l1")
      case FT : True
      show ?thesis using F FT "3.prems" "3.IH"(5) 
        by(fastforce)
    next
      case FF : False
      then show ?thesis
      proof(cases "r2 < l2")
        case FFT : True
        show ?thesis using F FF FFT "3.prems" "3.IH"(6) ranges'_valid_sub_weaken
          by(auto)
      next
        case FFF: False
        show ?thesis using F FF FFF "3.prems" "3.IH"(7) ranges'_valid_sub_weaken
          by(auto)
      qed
    qed
  qed
qed



lift_definition diff_ranges :: "ranges \<Rightarrow> ranges \<Rightarrow> ranges" is diff_ranges' 
  using diff_ranges'_valid ranges'_valid_sub_weaken[of _ _ 0]
  by auto

lemma diff_ranges'_spec :
  assumes Vl : "ranges'_valid_sub x l"
  assumes Vr : "ranges'_valid_sub x' r"
  shows "set_of_ranges' (diff_ranges' l r) =
         (set_of_ranges' l - set_of_ranges' r)" using assms
proof(induction l r arbitrary: x x' rule: diff_ranges'.induct)
  case 1
  then show ?case by auto
next
  case (2 l1 l2 lt)
  then show ?case by auto
next
  case (3 l1 l2 lt r1 r2 rt)
  show ?case
  proof(cases "l1 < r1")
    case T : True
    show ?thesis
    proof(cases "l2 < r1")
      case TT : True

      show ?thesis using T TT "3.prems" "3.IH"(1) ranges'_valid_sub_set[of r2 rt]
        by(fastforce)
    next
      case TF : False
      show ?thesis
      proof(cases "l2 < r2")
        case TFT : True
        show ?thesis using T TF TFT "3.prems" "3.IH"(2) ranges'_valid_sub_set[of r2 rt]
          by(fastforce)
      next
        case TFF : False
        show ?thesis 
        proof(cases "l2 > r2")
          case TFFT : True
          then show ?thesis using T TF TFF TFFT 
              "3.prems" "3.IH"(3) ranges'_valid_sub_set
            by(fastforce)
        next
          case TFFF: False
          show ?thesis using T TF TFF TFFF "3.prems" "3.IH"(4)
              ranges'_valid_sub_set[of r2 lt] ranges'_valid_sub_set[of r2 rt]
            by(fastforce)
        qed
      qed
    qed
  next
    case F :False
    show ?thesis
    proof(cases "r2 < l1")
      case FT : True
      show ?thesis using F FT "3.prems" "3.IH"(5) ranges'_valid_sub_set[of l2 lt]
        by(fastforce)
    next
      case FF : False
      then show ?thesis
      proof(cases "r2 < l2")
        case FFT : True
        show ?thesis using F FF FFT "3.prems" "3.IH"(6) ranges'_valid_sub_set
          by(fastforce)
      next
        case FFF: False
        show ?thesis using F FF FFF "3.prems" "3.IH"(7) ranges'_valid_sub_set
          by(fastforce)
      qed
    qed
  qed
qed

end