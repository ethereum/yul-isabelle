theory Oalist imports Main
begin

(* Implementation of association lists with ordered keys
 * This is based somewhat on the implementation of association lists from
 * HOL/Library/AList.thy and HOL/Library/DAlist.thy, with the twist that
 * keys are required to be in strictly increasing order.
 * This gives us the property that all sets of (key, value) pairs have a canonical representation,
 * which is necessary to satisfy the ordering laws used by Gazelle
 * (see Mergeable/Pord.thy, Mergeable/Mergeable.thy)
 *
 * TODO: Implementations given here are not necessarily as efficient as they could be
 *)

definition strict_order ::
  "('a :: linorder) list \<Rightarrow> bool" where
"strict_order l =
  (\<forall> i j . j < length l \<longrightarrow> i < j \<longrightarrow>
     (l ! i) < (l ! j))"

lemma strict_order_unfold :
  fixes l :: "('a :: linorder) list"
  fixes i j :: nat
  assumes H  : "strict_order l"
  assumes Hln : "j < length l"
  assumes Hij : "i < j"
  shows "l ! i < l ! j" using H Hln Hij
  by(auto simp add:strict_order_def)

lemma strict_order_intro :
  fixes l :: "('a :: linorder) list"
  assumes H : "\<And> i j . j < length l \<Longrightarrow> i < j \<Longrightarrow> (l ! i) < (l ! j)"
  shows "strict_order l" using H
  by(auto simp add:strict_order_def)

(* inspired by HOL-Library.DAList *)

lemma strict_order_tl :
  fixes l :: "('a :: linorder) list"
  fixes x :: "'a"
  assumes H : "strict_order (x#l)"
  shows "strict_order l"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hlen : "j < length l"
  assume Hij : "i < j"
  show "l ! i < l ! j"
    using strict_order_unfold[OF H, of "1 + j" "1 + i"] Hlen Hij
    by(auto)
qed

lemma strict_order_distinct :
  fixes l :: "('a :: linorder) list"
  assumes Hs : "strict_order l"
  shows "distinct l" using Hs
proof(induction l)
  case Nil
  then show ?case by(auto simp add:strict_order_def)
next
  case (Cons a l)
  then show ?case
  proof(cases "a \<in> set l")
    assume Hin1 : "(strict_order l \<Longrightarrow> distinct l)"
    assume Hin2 : "strict_order (a#l)"
    assume Hin3 : "a \<in> set l"
    then obtain i where Hi: "l ! i = a" and Hil : "1 + i < length (a#l)" by(auto simp add:in_set_conv_nth)
    hence Hfound : "(a # l)!(1 + i) = a" by(auto)
    have "(a#l)! 0 < (a#l) ! (1 + i)"
      using strict_order_unfold[OF Hin2 Hil, of 0] by auto
    hence "a < a" using Hfound by auto
    hence False using less_le by auto
    then show ?thesis by auto
  next
    assume Hin1 : "(strict_order l \<Longrightarrow> distinct l)"
    assume Hin2 : "strict_order (a#l)"
    assume Hin3 : "a \<notin> set l"
    then show ?thesis using Hin1 strict_order_tl[OF Hin2] Hin3
      by auto
  qed
qed

lemma strict_order_cons :
  fixes h1 h2 :: "('a :: linorder)"
  fixes l :: "'a list"
  assumes Hleq : "h1 < h2"
  assumes Hs : "strict_order (h2 # l)"
  shows "strict_order (h1 # h2 # l)"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hj : "j < length (h1 # h2 # l)"
  assume Hij : "i < j"
  
  show "(h1 # h2 # l) ! i < (h1 # h2 # l) ! j"
  proof(cases i)
    case 0
    have H0' : "1 \<le> j" using Hij by(cases j; auto)
    then show ?thesis (*using strict_order_unfold[OF Hs] 0 *)
    proof(cases "j = 1")
      case True
      then show ?thesis using Hleq 0 by auto
    next
      case False
      hence Hfalse' : "2 \<le> j" using H0' by auto
      then obtain j' where "j = Suc j'" by(cases j; auto)
      then show ?thesis using 0 Hfalse' Hj Hleq strict_order_unfold[OF Hs, of j', of 0]
        by(auto)
    qed
  next
    case (Suc i')
    hence Hsuc' : "2 \<le> j" using Hij by auto
    then obtain j' where "j = Suc j'" by(cases j; auto)
    then show ?thesis using Suc Hsuc' Hj Hij Hleq strict_order_unfold[OF Hs, of j', of i']
      by(auto)
  qed
qed

typedef (overloaded) ('key, 'value) oalist =
  "{xs :: (('key :: linorder) * 'value) list .
       strict_order (map fst xs)}"
  morphisms impl_of Oalist
proof
  show "[] \<in> {xs :: ('key * 'value) list . strict_order (map fst xs)}"
    by(auto simp add:strict_order_def)
qed

setup_lifting type_definition_oalist

type_synonym ('key) kmap =
  "('key, unit) oalist"

lemma alist_ext: "impl_of xs = impl_of ys \<Longrightarrow> xs = ys"
  by (simp add: impl_of_inject)

lemma alist_eq_iff: "xs = ys \<longleftrightarrow> impl_of xs = impl_of ys"
  by (simp add: impl_of_inject)

lemma impl_of_distinct [simp, intro]: "distinct (map fst (impl_of xs))"
  using impl_of[of xs] strict_order_distinct[of "map fst (impl_of xs)"] by simp

lemma Alist_impl_of [code abstype]: "Oalist (impl_of xs) = xs"
  by (rule impl_of_inverse)

(* primitives *)

fun str_ord_update :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list" where
"str_ord_update k v [] = [(k, v)]"
| "str_ord_update k v ((k', v')#t) =
    (if k < k'
     then (k, v) # (k', v') # t
     else (if k = k'
           then (k, v) # t
           else (k', v') # (str_ord_update k v t)))"

lemma str_ord_update_head :
  fixes l :: "(('key :: linorder) * 'value) list"
  shows "(hd (str_ord_update k v ((hk, hv)#l)) = (k, v) \<and> k \<le> hk) \<or>
         (hd (str_ord_update k v ((hk, hv)#l)) = (hk, hv) \<and> hk \<le> k)"
proof(-)
  consider (1) "k < hk" |
           (2) "k = hk" |
           (3) "hk < k"
    using less_linear[of k hk] by auto
  then show "(hd (str_ord_update k v ((hk, hv) # l)) = (k, v) \<and> (k \<le> hk)) \<or> (hd (str_ord_update k v ((hk, hv) # l)) = (hk, hv) \<and> hk \<le> k)"
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2 thus ?thesis by auto
  next
    case 3 thus ?thesis by auto
  qed
qed


lemma str_ord_update_correct :
  fixes l :: "(('key :: linorder) * 'value) list"
  fixes k :: 'key
  fixes v :: 'value
  assumes H : "strict_order (map fst l)"
  shows "strict_order (map fst (str_ord_update k v l))" using H
proof(induction l arbitrary: k v)
  case Nil
  then show ?case by(auto simp add:strict_order_def)
next
  fix a :: "'key * 'value"
  fix l' :: "('key * 'value) list"
  fix k :: 'key
  fix v :: 'value
  obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
  assume Hin1 : "\<And> k v .(strict_order (map fst l') \<Longrightarrow>
                  strict_order (map fst (str_ord_update k v l')))"
  assume Hin2: "strict_order (map fst (a # l'))"
  hence Hin2' : "strict_order (ak # map fst l')" using Ha by auto
  have Hord_l' : "strict_order (map fst l')" using strict_order_tl[OF Hin2'] by auto
  have Hin1': "strict_order (map fst (str_ord_update k v l'))" using Hin1[OF Hord_l'] by auto

  consider (1) "k < ak" |
           (2) "k = ak" |
           (3) "ak < k"
    using Ha less_linear[of k ak] by auto

  then show "strict_order (map fst (str_ord_update k v (a # l')))"
  proof cases
    case 1
    then show ?thesis using Ha Hin2' strict_order_cons[OF 1, of "map fst l'"]
      by(auto)
  next
    case 2
    then show ?thesis using Ha Hin2'
      by(auto)
  next
    case 3
    then show ?thesis
    proof(cases "(str_ord_update k v l')")
      case Nil
      show ?thesis
      proof(rule strict_order_intro)
        fix i j :: nat
        show "j < length (map fst (str_ord_update k v (a # l'))) \<Longrightarrow> i < j \<Longrightarrow>
                          map fst (str_ord_update k v (a # l')) ! i < 
                          map fst (str_ord_update k v (a # l')) ! j"
          using 3 Ha Nil by(cases i; auto)
      qed
    next
      fix a' :: "'key * 'value"
      fix l'' :: "('key * 'value) list"
      obtain a'k and a'v where Ha' : "a' = (a'k, a'v)" by(cases a'; auto) 
      assume Hcons : "(str_ord_update k v l') = a'#l''"
      show ?thesis
      proof(cases l')
        case Nil
        show ?thesis
        proof(rule strict_order_intro)
          fix i j :: nat
          show " j < length (map fst (str_ord_update k v (a # l'))) \<Longrightarrow> i < j \<Longrightarrow>
                  map fst (str_ord_update k v (a # l')) ! i <
                  map fst (str_ord_update k v (a # l')) ! j"
            using 3 Ha Nil by(cases i; auto)
        qed
      next
        fix x :: "'key * 'value"
        fix m :: "('key * 'value) list"
        obtain xk and xv where Hx : "x = (xk, xv)" by (cases x; auto)
        assume Hcons2 : "l' = x#m"
        consider (C3_1) "(hd (str_ord_update k v l') = (xk, xv))" and "xk \<le> k" |
                 (C3_2) "(hd (str_ord_update k v l')) = (k, v)" and "k \<le> xk"
          using Hcons Ha' Hcons2 Hx str_ord_update_head[of k v xk xv m]
          by( auto simp del:str_ord_update.simps)
        then show ?thesis
        proof cases
          case C3_1
          have "ak < xk" using Ha Ha' Hx Hcons2 strict_order_unfold[OF Hin2', of 1 0] by auto
          then show ?thesis using C3_1 3 Ha Ha' Hx Hcons Hcons2 Hin1' apply(auto)
            apply(rule_tac strict_order_cons) apply(auto)
            done
        next
          case C3_2
          then show ?thesis using 3 Ha Ha' Hx Hcons Hcons2 Hin1' apply(auto)
            apply(rule_tac strict_order_cons) apply(auto)
            done
        qed
      qed
    qed
  qed
qed
     

lift_definition empty :: "('key :: linorder, 'value) oalist" is "[]"
  by(simp add:strict_order_def)

lift_definition update :: "('key :: linorder) \<Rightarrow> 'value \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
  is str_ord_update
proof(-)
  fix k :: "'key :: linorder"
  fix v :: "'value"
  fix l :: "('key * 'value) list"
  assume H : "strict_order (map fst l)"
  show "strict_order (map fst (str_ord_update k v l))" using str_ord_update_correct[OF H] by auto
qed


fun str_ord_delete :: "('key :: linorder) \<Rightarrow> ('key * 'value) list \<Rightarrow> ('key * 'value) list" where
"str_ord_delete k [] = []"
| "str_ord_delete k ((k', v')#t) =
    (if k < k'
     then (k', v')#t
     else (if k = k'
           then t
           else (k', v') # (str_ord_delete k t)))"


lemma str_ord_delete_head :
  fixes l :: "(('key :: linorder) * 'value) list"
  assumes H : "strict_order (hk # map fst l)"
  shows "(hd (str_ord_delete k ((hk, hv)#l)) = (hk, hv) \<and> hk \<noteq> k) \<or>
         (\<exists> k' v' . hd (str_ord_delete k ((hk, hv)#l)) = (k', v') \<and> k = hk \<and> hk < k') \<or>
         (l = [])"
proof(cases l)
  case Nil
  then show ?thesis by auto
next
  fix a l'
  assume Hcons : "l = a # l'"
  obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
  consider (1) "k < hk" |
           (2) "k = hk" |
           (3) "hk < k"
    using less_linear[of k hk] by auto
  then show "hd (str_ord_delete k ((hk, hv) # l)) = (hk, hv) \<and> hk \<noteq> k \<or>
    (\<exists>k' v'. hd (str_ord_delete k ((hk, hv) # l)) = (k', v') \<and> k = hk \<and> hk < k') \<or> l = []"
  proof cases
    case 1
    then show ?thesis by auto
  next
    case 2 thus ?thesis using H Hcons Ha strict_order_unfold[OF H, of 1 0] by(auto)
  next
    case 3 thus ?thesis by auto
  qed
qed

lemma strict_order_2nd :
  assumes H : "strict_order (h1 # h2 # t)"
  shows "strict_order (h1 # t)"
proof(rule strict_order_intro)
  fix i j :: nat
  assume Hlen : "j < length (h1 # t)"
  assume Hlt : "i < j"
  show "(h1 # t) ! i < (h1 # t) ! j"
  proof(cases i)
    case 0
    obtain j' where "j = 1 + j'" using Hlt by (cases j; auto)
    then show ?thesis using 0 Hlen strict_order_unfold[OF H, of "1 + j" "0"] by(auto)
  next
    case (Suc nat)
    obtain j' where "j = 1 + j'" using Hlt by (cases j; auto)
    then show ?thesis using Suc Hlen Hlt strict_order_unfold[OF H, of "1 + j" "1 + i"] by(auto)  
  qed
qed

(* need a similar cons lemma for this one. *)
lemma str_ord_delete_correct :
  fixes k :: "'key :: linorder"
  fixes l :: "('key * 'value) list"
  assumes H : "strict_order (map fst l)"
  shows "strict_order (map fst (str_ord_delete k l))" using H
proof(induction l)
  case Nil
  then show ?case by(auto simp add:strict_order_def)
next
  fix a :: "('key * 'value)"
  fix l' :: "('key * 'value) list"
  assume Hi1 : "(strict_order (map fst l') \<Longrightarrow> strict_order (map fst (str_ord_delete k l')))"
  assume Hi2 : "strict_order (map fst (a # l'))"
  obtain ak and av where Ha: "a = (ak, av)" by(cases a; auto)
  
  have Hi1' : "strict_order (map fst (str_ord_delete k l'))" using Ha Hi1 Hi2 strict_order_tl[of ak "map fst l'"]
    by(auto)

  consider (1) "k < ak" |
           (2) "k = ak" |
           (3) "ak < k"
    using less_linear[of k ak] by auto
  then show "strict_order (map fst (str_ord_delete k (a # l')))"
  proof cases
    case 1
    then show ?thesis using Ha Hi2 by(auto)
  next
    case 2
    have Hi2' : "strict_order (map fst l')" using Ha Hi2 strict_order_tl[of ak "map fst l'"] by auto
    then show ?thesis using 2 Ha by(auto)
  next
    case 3
    have Hi2' : "strict_order (map fst l')" using Ha Hi2 strict_order_tl[of ak "map fst l'"] by auto
    show ?thesis using 3
    proof(cases "(str_ord_delete k l')")
      case Nil
      show ?thesis
      proof(rule strict_order_intro)
        fix i j :: nat
        show "j < length (map fst (str_ord_delete k (a # l'))) \<Longrightarrow>
           i < j \<Longrightarrow> map fst (str_ord_delete k (a # l')) ! i < map fst (str_ord_delete k (a # l')) ! j"
          using 3 Ha Nil by(cases i; auto)
      qed
    next
      fix a' :: "'key * 'value"
      fix l'' :: "('key * 'value) list"
      obtain a'k and a'v where Ha' : "a' = (a'k, a'v)" by(cases a'; auto) 
      assume Hcons : "(str_ord_delete k l') = a'#l''"
      show ?thesis
      proof(cases l')
        case Nil
        show ?thesis
        proof(rule strict_order_intro)
          fix i j :: nat
          show "j < length (map fst (str_ord_delete k (a # l'))) \<Longrightarrow>
           i < j \<Longrightarrow> map fst (str_ord_delete k (a # l')) ! i < map fst (str_ord_delete k (a # l')) ! j"
            using 3 Ha Nil by(cases i; auto split:if_split_asm)
        qed
      next
        fix x :: "'key * 'value"
        fix m :: "('key * 'value) list"
        obtain xk and xv where Hx : "x = (xk, xv)" by (cases x; auto)
        assume Hcons2 : "l' = x#m"
        have Hi2'' : "strict_order (xk # map fst m)" using Hcons2 Hx Hi2' by auto
        consider (C3_1) "hd (str_ord_delete k ((xk, xv)#m)) = (xk, xv)" and "xk \<noteq> k" |
                 (C3_2) k' v' where "hd (str_ord_delete k ((xk, xv)#m)) = (k', v')" and "k = xk" and "xk < k'" |
                 (C3_3) "(l' = [])"
          using str_ord_delete_head[OF Hi2'', of k xv] Hcons Hcons2 Ha Hi2' Hx by(auto split:if_split_asm)
        then show ?thesis
        proof cases
          case C3_1
          have Hcons_a_x : "strict_order (ak # xk # map fst m)" using Hcons2 Hx Ha Hi2 by(auto)
          show ?thesis using C3_1 3 Ha  Ha' Hx Hi1' strict_order_unfold[OF Hcons_a_x, of 1 0] Hcons Hcons2
            apply(auto)
            apply(rule_tac strict_order_cons) apply(auto split:if_splits)
            done
        next
          case C3_2
          have Hcons_a_x : "strict_order (ak # xk # map fst m)" using Hcons2 Hx Ha Hi2 by(auto)
          show ?thesis using 3 Ha  Ha' Hx Hi1' Hcons2 Hcons_a_x strict_order_2nd[OF Hcons_a_x]
            strict_order_unfold[OF Hcons_a_x, of 1 0]
            apply(auto)
            apply(rule_tac strict_order_cons) apply(auto split:if_splits)
            done
        next
          case C3_3
          then show ?thesis using Ha by(auto simp add:strict_order_def)
        qed
      qed
    qed
  qed
qed

lift_definition delete :: "('key :: linorder) \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
is str_ord_delete
proof(-)
  fix k :: "'key :: linorder"
  fix l :: "('key * 'value) list"
  assume H : "strict_order (map fst l)"
  show "strict_order (map fst (str_ord_delete k l))" using str_ord_delete_correct[OF H] by auto
qed

fun to_oalist :: "(('a :: linorder) * 'b) list \<Rightarrow> ('a, 'b) oalist" where
"to_oalist [] = empty"
| "to_oalist ((a, b)#l) = 
     update a b (to_oalist l)"

lift_definition get :: "('key, 'value) oalist \<Rightarrow> ('key :: linorder) \<Rightarrow>  'value option"
is map_of .

definition has_key :: "('key) kmap \<Rightarrow> 'key :: linorder \<Rightarrow> bool" where
"has_key l k = (get l k = Some ())"

(* possibly useful for semantics - if a key map describing updated values
   has only one entry, we can pull it out. *)
definition kmap_singleton :: "('key :: linorder) kmap \<Rightarrow> 'key" where
"kmap_singleton l =
  (case impl_of l of
    [k] \<Rightarrow> fst k)"

definition add_key :: "('key) kmap \<Rightarrow> 'key :: linorder \<Rightarrow> 'key kmap" where
"add_key l k = update k () l"

(* some useful functions for combining oalists *)
fun oalist_merge' :: "(('key :: linorder) * 'value) list \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
  where
"oalist_merge' [] l2 = l2"
| "oalist_merge' ((k,v)#t) l2 =
   update k v (oalist_merge' t l2)"

lift_definition oalist_merge ::
"('key :: linorder, 'value) oalist \<Rightarrow> ('key, 'value) oalist \<Rightarrow> ('key, 'value) oalist"
is oalist_merge' .

lemma strict_order_singleton :
  "strict_order [x]"
proof(rule strict_order_intro)
  fix i j
  assume H1 : "j < length [x]"
  assume H2 : "i < j" 
  show "[x] ! i < [x] ! j" using H1 H2
    by(auto)
qed

fun alist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key * 'v1) list \<Rightarrow> ('key * 'v2) list" where
"alist_map_val f l =
  map (map_prod id f) l"

lemma strict_order_nil : "strict_order []"
  by(rule strict_order_intro; auto)

lift_definition
  oalist_map_val ::
  "('v1 \<Rightarrow> 'v2) \<Rightarrow> ('key :: linorder, 'v1) oalist \<Rightarrow> ('key, 'v2) oalist"
 is alist_map_val
  by (auto intro: strict_order_nil)

definition alist_all_val ::
  "('v1 \<Rightarrow> bool) \<Rightarrow> ('key * 'v1) list \<Rightarrow> bool" where
"alist_all_val P l =
  list_all P (map snd l)"

lift_definition oalist_all_val :: "('v \<Rightarrow> bool) \<Rightarrow> ('key :: linorder, 'v) oalist \<Rightarrow> bool"
is alist_all_val .

lift_definition oaset :: "('key :: linorder, 'v) oalist \<Rightarrow> ('key * 'v) set"
is set .

(* zip two oalists together using the given functions -
 * one for both keys present, one for left key present, one for right key present *)
fun str_ord_zip ::
  "('key \<Rightarrow> 'value1 \<Rightarrow> 'value2 \<Rightarrow> 'value3 ) \<Rightarrow>
   ('key \<Rightarrow> 'value1 \<Rightarrow> 'value3) \<Rightarrow>
   ('key \<Rightarrow> 'value2 \<Rightarrow> 'value3) \<Rightarrow>
   (('key :: linorder) * 'value1) list \<Rightarrow> ('key * 'value2) list \<Rightarrow>
   ('key * 'value3) list" where
"str_ord_zip flr fl fr [] [] = []"
| "str_ord_zip flr fl fr ((lk, lh)#lt) [] =
    (lk, fl lk lh)#str_ord_zip flr fl fr lt []"
| "str_ord_zip flr fl fr [] ((rk, rh)#rt) =
    (rk, fr rk rh)#str_ord_zip flr fl fr [] rt"
| "str_ord_zip flr fl fr ((lk, lh)#lt) ((rk, rh)#rt) =
  (if (lk < rk)
   then (lk, fl lk lh) # str_ord_zip flr fl fr lt ((rk, rh)#rt)
   else (if lk = rk
         then (lk, flr lk lh rh) # str_ord_zip flr fl fr lt rt
         else (rk, fr rk rh) # str_ord_zip flr fl fr ((lk, lh) # lt) (rt)))"

lemma str_ord_zip_head_key :
  shows
    "(\<exists> res_l res_v .
     str_ord_zip flr fl fr ((lk, lv)#ll) ((rk, rv)#lr) = ((lk, res_v)#res_l)) \<or>
    (\<exists> res_l res_v .
     str_ord_zip flr fl fr ((lk, lv)#ll) ((rk, rv)#lr) = ((rk, res_v)#res_l))"
proof-

  consider (A) "lk < rk" |
           (B) "lk = rk" |
           (C) "rk < lk"
    using less_linear[of lk rk] by auto

  then show "(\<exists>res_l res_v.
        str_ord_zip flr fl fr ((lk, lv) # ll) ((rk, rv) # lr) =
        (lk, res_v) # res_l) \<or>
    (\<exists>res_l res_v.
        str_ord_zip flr fl fr ((lk, lv) # ll) ((rk, rv) # lr) =
        (rk, res_v) # res_l)" 
    by(cases; auto)
qed

lemma str_ord_zip_leftonly :
  assumes H : "strict_order (map fst ll)"
  shows "strict_order (map fst (str_ord_zip flr fl fr ll []))" using H
proof(induction ll)
  case Nil
  then show ?case using strict_order_nil
    by auto
next
  case (Cons lh lt)

  obtain lk lv where Lh : "lh = (lk, lv)"
    by(cases lh; auto)

  then show ?case
  proof(cases lt)
    case Nil' : Nil
    then show ?thesis using Lh strict_order_singleton
      by(auto)
  next
    case Cons' : (Cons lh1 lt1)

    have Ord' : "strict_order (map fst lt)"
      using strict_order_tl[of lk "map fst lt"] Cons.prems(1) unfolding Lh
      by auto

    obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)"
      by(cases lh1; auto)

    have Lk_lt : "lk < lk1"
      using strict_order_unfold[OF Cons.prems(1), of 1 0]
      unfolding Cons' Lh Lh1
      by auto

    have Conc' : "strict_order (lk1 # map fst (str_ord_zip flr fl fr lt1 []))"
      using Cons.IH[OF Ord'] Cons.prems Cons' Lh Lh1
      by(auto)

    show ?thesis
      using strict_order_cons[OF Lk_lt Conc'] Cons.prems Cons' Lh Lh1
      by auto
  qed
qed

lemma str_ord_zip_rightonly :
  assumes H : "strict_order (map fst lr)"
  shows "strict_order (map fst (str_ord_zip flr fl fr [] lr))" using H
proof(induction lr)
  case Nil
  then show ?case using strict_order_nil
    by auto
next
  case (Cons rh rt)

  obtain rk rv where Rh : "rh = (rk, rv)"
    by(cases rh; auto)

  then show ?case
  proof(cases rt)
    case Nil' : Nil
    then show ?thesis using Rh strict_order_singleton
      by(auto)
  next
    case Cons' : (Cons rh1 rt1)

    have Ord' : "strict_order (map fst rt)"
      using strict_order_tl[of rk "map fst rt"] Cons.prems(1) unfolding Rh
      by auto

    obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)"
      by(cases rh1; auto)

    have Rk_lt : "rk < rk1"
      using strict_order_unfold[OF Cons.prems(1), of 1 0]
      unfolding Cons' Rh Rh1
      by auto

    have Conc' : "strict_order (rk1 # map fst (str_ord_zip flr fl fr [] rt1))"
      using Cons.IH[OF Ord'] Cons.prems Cons' Rh Rh1
      by(auto)

    show ?thesis
      using strict_order_cons[OF Rk_lt Conc'] Cons.prems Cons' Rh Rh1
      by auto
  qed
qed

lemma str_ord_zip_correct' :
  shows "strict_order (map fst ll) \<longrightarrow>
         strict_order (map fst lr) \<longrightarrow>
         strict_order (map fst (str_ord_zip flr fl fr ll lr))"
proof(induction rule:
      str_ord_zip.induct
        [of "(\<lambda> flr fl fr ll lr . 
              strict_order (map fst ll) \<longrightarrow>
              strict_order (map fst lr) \<longrightarrow>
              strict_order (map fst (str_ord_zip flr fl fr ll lr)))"])
  case (1 flr fl fr)
  then show ?case 
    by auto
next
  case (2 flr fl fr lk lv lt)

  have Conc' : "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow> strict_order (map fst []) \<Longrightarrow> strict_order (map fst (str_ord_zip flr fl fr ((lk, lv) # lt) []))"
  proof-
    assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
    assume Ord2 : "strict_order (map fst [])"

    show "strict_order (map fst (str_ord_zip flr fl fr ((lk, lv) # lt) []))"
      using str_ord_zip_leftonly[OF Ord1] by auto
  qed

  then show ?case by auto
next
  case (3 flr fl fr rk rv rt)

  have Conc' : "strict_order (map fst []) \<Longrightarrow> strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow> strict_order (map fst (str_ord_zip flr fl fr [] ((rk, rv) # rt)))"
  proof-
    assume Ord1 : "strict_order (map fst ((rk, rv) # rt))"
    assume Ord2 : "strict_order (map fst [])"

    show "strict_order (map fst (str_ord_zip flr fl fr [] ((rk, rv) # rt)))"
      using str_ord_zip_rightonly[OF Ord1] by auto
  qed

  then show ?case by auto

next
  case (4 flr fl fr lk lv lt rk rv rt)

  have Conc' : 
    "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
       strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
       strict_order (map fst (str_ord_zip flr fl fr ((lk, lv) # lt) ((rk, rv) # rt)))"
  proof-
    assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
    assume Ord2 : "strict_order (map fst ((rk, rv) # rt))"

    have Ord1_tl : "strict_order (map fst (lt))"
      using strict_order_tl[of lk "map fst lt"] Ord1 by auto
    have Ord2_tl : "strict_order (map fst (rt))"
      using strict_order_tl[of rk "map fst rt"] Ord2 by auto

    consider (A) "lk < rk" |
             (B) "rk < lk" |
             (C) "lk = rk"
      using less_linear[of lk rk] by auto
  
    then show ?thesis 
    proof cases
      case A

      have IH : "strict_order (map fst lt) \<Longrightarrow>
                 strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
                 strict_order (map fst (str_ord_zip flr fl fr lt ((rk, rv) # rt)))"
        using 4(1)[OF A] by blast

      show ?thesis
      proof(cases lt)
        case Nil

        have Conc' : "strict_order (rk # map fst (str_ord_zip flr fl fr [] rt))"
          using IH[OF Ord1_tl Ord2] Nil
          by auto

        then show ?thesis 
          using strict_order_cons[OF A Conc'] A Nil
          by(auto)
      next
        case (Cons lh1 lt1)

        obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)" by(cases lh1; auto)
  
        have Lk_lt: "lk < lk1" 
          using strict_order_unfold[OF Ord1, of 1 0] Cons Lh1
          by auto

        consider (L) res_v res_l where "str_ord_zip flr fl fr ((lk1, lv1) # lt1) ((rk, rv) # rt) = 
              (lk1, res_v) # res_l" "lk1 \<le> rk"
          | (R) res_v res_l where "str_ord_zip flr fl fr ((lk1, lv1) # lt1) ((rk, rv) # rt) = (rk, res_v) # res_l" "rk \<le> lk1"
          using str_ord_zip_head_key[of flr fl fr lk1 lv1 lt1 rk rv rt ]
          by(auto split:if_splits)
  
        then show ?thesis
        proof cases
          case L

          have Lk1_head : "strict_order (lk1 # map fst (res_l))"
            using IH[OF Ord1_tl Ord2] unfolding Cons Lh1 L(1) by auto

          have Lk_head : "strict_order (lk # map fst ((lk1, res_v) # res_l))"
            using strict_order_cons[OF Lk_lt Lk1_head] by auto

          show ?thesis using Lk_head A L(1) unfolding  Cons Lh1
            by(auto)
        next
          case R

          have Rk_head : "strict_order (rk # map fst (res_l))"
            using IH[OF Ord1_tl Ord2] unfolding Cons Lh1 R(1) by auto

          have Lk_head : "strict_order (lk # rk # map fst res_l)"
            using strict_order_cons[OF A Rk_head] by simp

          show ?thesis using Lk_head A R(1) unfolding  Cons Lh1
            by(auto)
        qed
      qed
    next
      case B
      
      have IH : "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
                 strict_order (map fst rt) \<Longrightarrow>
                 strict_order (map fst (str_ord_zip flr fl fr ((lk, lv) # lt) rt))"
        using 4(3) B
        by auto

      show ?thesis
      proof(cases rt)
        case Nil

        have Conc' : "strict_order (lk # map fst (str_ord_zip flr fl fr lt []))"
          using IH[OF Ord1 Ord2_tl] Nil strict_order_singleton
          by(auto)

        then show ?thesis 
          using strict_order_cons[OF B Conc'] B Nil
          by(auto)
      next
        case (Cons rh1 rt1)
        obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)" by(cases rh1; auto)
  
        have Rk_lt: "rk < rk1" 
          using strict_order_unfold[OF Ord2, of 1 0] Cons Rh1
          by auto

        consider (L) res_v res_l where "str_ord_zip flr fl fr ((lk, lv) # lt) ((rk1, rv1) # rt1) = 
              (rk1, res_v) # res_l" "rk1 \<le> lk"
          | (R) res_v res_l where "str_ord_zip flr fl fr ((lk, lv) # lt) ((rk1, rv1) # rt1) = (lk, res_v) # res_l" "lk \<le> rk1"
          using str_ord_zip_head_key[of flr fl fr lk lv lt rk1 rv1 rt1]
          by(auto split:if_splits)
  
        then show ?thesis
        proof cases
          case L

          have Rk1_head : "strict_order (rk1 # map fst (res_l))"
            using IH[OF Ord1 Ord2_tl] unfolding Cons Rh1 L(1) by auto

          have Rk_head : "strict_order (rk # map fst ((rk1, res_v) # res_l))"
            using strict_order_cons[OF Rk_lt Rk1_head] by auto

          show ?thesis using Rk_head B L(1) unfolding Cons Rh1
            by(auto)
        next
          case R

          have Lk_head : "strict_order (lk # map fst (res_l))"
            using IH[OF Ord1 Ord2_tl] unfolding Cons Rh1 R(1) by auto

          have Rk_head : "strict_order (rk # lk # map fst res_l)"
            using strict_order_cons[OF B Lk_head] by simp

          show ?thesis using Rk_head B R(1) unfolding Cons Rh1
            by(auto)
        qed
      qed
    next
      case C

      have IH : "strict_order (map fst lt) \<Longrightarrow> strict_order (map fst rt) \<Longrightarrow> strict_order (map fst (str_ord_zip flr fl fr lt rt))"
        using 4(2) C
        by auto

      show ?thesis
      proof(cases lt)
        case Nil_L : Nil

        show ?thesis
        proof(cases rt)
          case Nil_R : Nil

          then show ?thesis using C Nil_L strict_order_singleton
            by(auto)
        next
          case Cons_R : (Cons rh1 rt1)

          obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)" by(cases rh1; auto)

          have Rk_lt: "rk < rk1" 
            using strict_order_unfold[OF Ord2, of 1 0] Cons_R Rh1
            by(auto)

          have Conc' : "strict_order (rk1 # map fst (str_ord_zip flr fl fr [] rt1))"
            using IH[OF Ord1_tl Ord2_tl] Nil_L Cons_R unfolding Rh1
            by(auto)

          show ?thesis
            using strict_order_cons[OF Rk_lt Conc'] Nil_L Cons_R C Rh1
            by(auto)
        qed
      next
        case Cons_L : (Cons lh1 lt1)

        obtain lk1 lv1 where Lh1 : "lh1 = (lk1, lv1)" by(cases lh1; auto)

        have Lk_lt: "lk < lk1" 
          using strict_order_unfold[OF Ord1, of 1 0] Cons_L Lh1
          by(auto)

        show ?thesis
        proof(cases rt)
          case Nil_R : Nil

          have Conc' : "strict_order (lk1 # map fst (str_ord_zip flr fl fr lt1 []))"
            using IH[OF Ord1_tl Ord2_tl] Cons_L Nil_R unfolding Lh1
            by(auto)

          show ?thesis
            using strict_order_cons[OF Lk_lt Conc'] Nil_R Cons_L C Lh1
            by(auto)
        next
          case Cons_R : (Cons rh1 rt1)

          obtain rk1 rv1 where Rh1 : "rh1 = (rk1, rv1)" by(cases rh1; auto)

          have Rk_lt: "rk < rk1" 
            using strict_order_unfold[OF Ord2, of 1 0] Cons_R Rh1
            by(auto)
  
          consider (L) res_v res_l where "str_ord_zip flr fl fr ((lk1, lv1) # lt1) ((rk1, rv1) # rt1) = 
                (rk1, res_v) # res_l" "rk1 \<le> lk1"
            | (R) res_v res_l where "str_ord_zip flr fl fr ((lk1, lv1) # lt1) ((rk1, rv1) # rt1) = (lk1, res_v) # res_l" "lk1 \<le> rk1"
            using str_ord_zip_head_key[of flr fl fr lk1 lv1 lt1 rk1 rv1 rt1]
            by(auto split:if_splits)
    
          then show ?thesis
          proof cases
            case L
  
            have Rk1_head : "strict_order (rk1 # map fst (res_l))"
              using IH[OF Ord1_tl Ord2_tl] unfolding Cons_L Cons_R Rh1 Lh1 L(1)
              by (auto)
  
            have Rk_head : "strict_order (rk # map fst ((rk1, res_v) # res_l))"
              using strict_order_cons[OF Rk_lt Rk1_head] by auto
  
            show ?thesis using Rk_head C L(1) unfolding Cons_L Cons_R Lh1 Rh1
              by(auto)
          next
            case R

            have Lk_lt': "lk < rk1" 
              using Lk_lt Rk_lt C 
              by simp
  
            have Lk_head : "strict_order (lk1 # map fst (res_l))"
              using IH[OF Ord1_tl Ord2_tl] unfolding Cons_L Cons_R Rh1 Lh1 R(1) by auto

            have Lk_head' : "strict_order (lk # lk1 # map fst res_l)" 
              using strict_order_cons[OF Lk_lt Lk_head] by simp

            show ?thesis using Lk_head' C R(1) unfolding Cons_L Cons_R Lh1 Rh1
              by(auto)
          qed
        qed
      qed
    qed
  qed

  then show ?case by blast
qed

lemma str_ord_zip_correct :
  shows "strict_order (map fst ll) \<Longrightarrow>
         strict_order (map fst lr) \<Longrightarrow>
         strict_order (map fst (str_ord_zip flr fl fr ll lr))"
  using str_ord_zip_correct'
  by blast


(* finally, we get our zip function *)

lift_definition oalist_zip :: 
  "('key \<Rightarrow> 'value1 \<Rightarrow> 'value2 \<Rightarrow> 'value3 ) \<Rightarrow>
   ('key \<Rightarrow> 'value1 \<Rightarrow> 'value3) \<Rightarrow>
   ('key \<Rightarrow> 'value2 \<Rightarrow> 'value3) \<Rightarrow>
   (('key :: linorder), 'value1) oalist \<Rightarrow> ('key, 'value2) oalist \<Rightarrow>
   ('key, 'value3) oalist"
is str_ord_zip
  using str_ord_zip_correct
  by blast

lemma str_ord_zip_get' :
  shows "strict_order (map fst ll) \<longrightarrow> 
   strict_order (map fst lr) \<longrightarrow>
    map_of (str_ord_zip flr fl fr ll lr) k =
    (case (map_of ll k, map_of lr k) of
     (None, None) \<Rightarrow> None
     | (Some vl, None) \<Rightarrow> Some (fl k vl)
     | (None, Some vr) \<Rightarrow> Some (fr k vr)
     | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
proof(induction ll lr rule:str_ord_zip.induct
    [of "(\<lambda> flr fl fr ll lr . 
              strict_order (map fst ll) \<longrightarrow>
              strict_order (map fst lr) \<longrightarrow>
              map_of (str_ord_zip flr fl fr ll lr) k =
                (case (map_of ll k, map_of lr k) of
                 (None, None) \<Rightarrow> None
                 | (Some vl, None) \<Rightarrow> Some (fl k vl)
                 | (None, Some vr) \<Rightarrow> Some (fr k vr)
                 | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr)))"])
case (1 flr fl fr)
  then show ?case 
    by(auto)
next
  case (2 flr fl fr lk lv lt)

  have Conc' :
    "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
    strict_order (map fst []) \<Longrightarrow>
    map_of (str_ord_zip flr fl fr ((lk, lv) # lt) []) k =
    (case (map_of ((lk, lv) # lt) k, map_of [] k) of (None, None) \<Rightarrow> None
     | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
     | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
  proof-
    assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
    assume Ord2 : "strict_order (map fst [])"

    have Ord1' : "strict_order (map fst lt)"
      using strict_order_tl[of lk "map fst lt"] Ord1
      by auto

    show "map_of (str_ord_zip flr fl fr ((lk, lv) # lt) []) k =
    (case (map_of ((lk, lv) # lt) k, map_of [] k) of (None, None) \<Rightarrow> None
     | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
     | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
      using 2 Ord1' strict_order_nil
      by auto
  qed

  then show ?case by blast
next
  case (3 flr fl fr rk rv rt)

  have Conc' :
    "strict_order (map fst []) \<Longrightarrow>
    strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
     map_of (str_ord_zip flr fl fr [] ((rk, rv) # rt)) k =
       (case (map_of [] k, map_of ((rk, rv) # rt) k) of (None, None) \<Rightarrow> None
        | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
        | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
  proof-
    assume Ord1 : "strict_order (map fst [])"

    assume Ord2 : "strict_order (map fst ((rk, rv) # rt))"

    have Ord2' : "strict_order (map fst rt)"
      using strict_order_tl[of rk "map fst rt"] Ord2
      by auto

    show "map_of (str_ord_zip flr fl fr [] ((rk, rv) # rt)) k =
       (case (map_of [] k, map_of ((rk, rv) # rt) k) of (None, None) \<Rightarrow> None
        | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
        | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
      using 3 Ord2' strict_order_nil
      by auto
  qed

  then show ?case by blast
next
  case (4 flr fl fr lk lv lt rk rv rt)

  consider (A) "lk < rk" |
           (B) "rk < lk" |
           (C) "lk = rk"
    using less_linear[of lk rk] by auto

  then show ?case
  proof cases
    case A

    have Conc' : "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
      strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
      map_of (str_ord_zip flr fl fr ((lk, lv) # lt) ((rk, rv) # rt)) k =
      (case (map_of ((lk, lv) # lt) k, map_of ((rk, rv) # rt) k) of (None, None) \<Rightarrow> None
       | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
       | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
    proof-

      assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
      assume Ord2 : "strict_order (map fst ((rk, rv) # rt))"

      have Ord1' : "strict_order (map fst lt)"
        using strict_order_tl[of lk "map fst lt"] Ord1 by auto

      have Ord2' : "strict_order (map fst rt)"
        using strict_order_tl[of rk "map fst rt"] Ord2 by auto

      consider
        (NN) "map_of ((lk, lv) # lt) k = None"  "map_of ((rk, rv) # rt) k = None" |
        (SN) vl where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = None" |
        (NS) vr where "map_of ((lk, lv) # lt) k = None" "map_of ((rk, rv) # rt) k = Some vr" |
        (SS) vl vr where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = Some vr"
        by(cases "map_of ((lk, lv) # lt) k"; cases "map_of ((rk, rv) # rt) k"; auto)

      then show ?thesis
      proof cases
        case NN
        then show ?thesis using A 4(1)[OF A] Ord1 Ord2 Ord1'
          by(auto split:if_split_asm)
      next
        case SN
        then show ?thesis using A 4(1)[OF A] Ord1 Ord2 Ord1'
          by(auto split:if_split_asm)
      next
        case NS
        then show ?thesis using A 4(1)[OF A] Ord1 Ord2 Ord1'
          by(auto split:if_split_asm)
      next
        case SS

        have Contr : "map_of rt lk = None"
        proof(cases "map_of rt lk")
          case None
          then show ?thesis by auto
        next
          case (Some bad)

          have Bad_in : "(lk, bad) \<in> set rt" using map_of_SomeD[OF Some] by simp

          obtain idx where Idx : "idx < length rt" "rt ! idx = (lk, bad)" 
            using Bad_in
            unfolding in_set_conv_nth 
            by blast

          then show ?thesis using strict_order_unfold[OF Ord2, of "1 + idx" 0] A
            by(simp)
        qed

        then show ?thesis using A 4(1)[OF A] Ord1 Ord2 Ord1' Ord2'
          by(auto split: if_split_asm option.split_asm)
      qed
    qed

    then show ?thesis by blast
  next
    case B 

    have Conc' : "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
      strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
      map_of (str_ord_zip flr fl fr ((lk, lv) # lt) ((rk, rv) # rt)) k =
      (case (map_of ((lk, lv) # lt) k, map_of ((rk, rv) # rt) k) of (None, None) \<Rightarrow> None
       | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
       | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
    proof-
      assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
      assume Ord2 : "strict_order (map fst ((rk, rv) # rt))"

      have Ord1' : "strict_order (map fst lt)"
        using strict_order_tl[of lk "map fst lt"] Ord1 by auto

      have Ord2' : "strict_order (map fst rt)"
        using strict_order_tl[of rk "map fst rt"] Ord2 by auto

      consider
        (NN) "map_of ((lk, lv) # lt) k = None"  "map_of ((rk, rv) # rt) k = None" |
        (SN) vl where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = None" |
        (NS) vr where "map_of ((lk, lv) # lt) k = None" "map_of ((rk, rv) # rt) k = Some vr" |
        (SS) vl vr where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = Some vr"
        by(cases "map_of ((lk, lv) # lt) k"; cases "map_of ((rk, rv) # rt) k"; auto)

      then show ?thesis
      proof cases
        case NN
        then show ?thesis using B 4(3) Ord1 Ord2 Ord2'
          by(auto split:if_split_asm)
      next
        case SN
        then show ?thesis using B 4(3) Ord1 Ord2 Ord2'
          by(auto split:if_split_asm)
      next
        case NS
        then show ?thesis using B 4(3) Ord1 Ord2 Ord2'
          by(auto split:if_split_asm)
      next
        case SS

        have Contr : "map_of lt rk = None"
        proof(cases "map_of lt rk")
          case None
          then show ?thesis by auto
        next
          case (Some bad)

          have Bad_in : "(rk, bad) \<in> set lt" using map_of_SomeD[OF Some] by simp

          obtain idx where Idx : "idx < length lt" "lt ! idx = (rk, bad)" 
            using Bad_in
            unfolding in_set_conv_nth 
            by blast

          then show ?thesis using strict_order_unfold[OF Ord1, of "1 + idx" 0] B
            by(simp)
        qed

        then show ?thesis using B 4(3) Ord1 Ord2 Ord1' Ord2'
          by(auto split: if_split_asm option.split_asm)
      qed
    qed

    then show ?thesis by blast
  next
    case C 

    have Conc' : "strict_order (map fst ((lk, lv) # lt)) \<Longrightarrow>
                  strict_order (map fst ((rk, rv) # rt)) \<Longrightarrow>
                    map_of (str_ord_zip flr fl fr ((lk, lv) # lt) ((rk, rv) # rt)) k =
                  (case (map_of ((lk, lv) # lt) k, map_of ((rk, rv) # rt) k) of (None, None) \<Rightarrow> None
                   | (None, Some vr) \<Rightarrow> Some (fr k vr) | (Some vl, None) \<Rightarrow> Some (fl k vl)
                   | (Some vl, Some vr) \<Rightarrow> Some (flr k vl vr))"
    proof-
      assume Ord1 : "strict_order (map fst ((lk, lv) # lt))"
      assume Ord2 : "strict_order (map fst ((rk, rv) # rt))"

      have Ord1' : "strict_order (map fst lt)"
        using strict_order_tl[of lk "map fst lt"] Ord1 by auto

      have Ord2' : "strict_order (map fst rt)"
        using strict_order_tl[of rk "map fst rt"] Ord2 by auto

      consider
        (NN) "map_of ((lk, lv) # lt) k = None"  "map_of ((rk, rv) # rt) k = None" |
        (SN) vl where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = None" |
        (NS) vr where "map_of ((lk, lv) # lt) k = None" "map_of ((rk, rv) # rt) k = Some vr" |
        (SS) vl vr where "map_of ((lk, lv) # lt) k = Some vl" "map_of ((rk, rv) # rt) k = Some vr"
        by(cases "map_of ((lk, lv) # lt) k"; cases "map_of ((rk, rv) # rt) k"; auto)

      then show ?thesis
      proof cases
        case NN
        then show ?thesis using C 4(2) Ord1 Ord2 Ord1' Ord2'
          by(auto split:if_split_asm)
      next
        case SN
        then show ?thesis using C 4(2) Ord1 Ord2 Ord1' Ord2'
          by(auto split:if_split_asm)
      next
        case NS
        then show ?thesis using C 4(2) Ord1 Ord2 Ord1' Ord2'
          by(auto split:if_split_asm)
      next
        case SS

        then show ?thesis using C 4(2) Ord1 Ord2 Ord1' Ord2'
          by(auto split:if_split_asm)
      qed
    qed

    then show ?thesis using C 4(2)
      by(auto split: if_split_asm option.split_asm)
  qed
qed

fun alist_somes :: "('k :: linorder * 'v option) list \<Rightarrow> ('k * 'v) list"
  where
"alist_somes [] = []"
| "alist_somes ((hk, None)#t) = alist_somes t"
| "alist_somes ((hk, Some hv)#t) = (hk, hv) # alist_somes t"

(* TODO: implement alist_fuse... *)

lift_definition oalist_eq :: "('k :: linorder, 'v) oalist \<Rightarrow> ('k, 'v) oalist \<Rightarrow> bool"
is "\<lambda> x y . x = y"
  .

instantiation oalist :: (linorder, _) equal
begin
definition eq_oalist :
"(HOL.equal l1 l2) = (oalist_eq l1 l2)"
instance proof
  fix x y :: "('a, 'b) oalist"
  show "equal_class.equal x y = (x = y)"
    unfolding eq_oalist
    by(transfer; auto)
qed
end

fun oacons' :: "'k \<Rightarrow> 'v \<Rightarrow> ('k :: linorder * 'v) list \<Rightarrow> ('k * 'v) list option" where
"oacons' k v [] = Some [(k, v)]"
| "oacons' k v ((kh, vh) # t) =
   (if k < kh then Some ((k, v) # (kh, vh) # t)
    else None)"

lemma oacons'_correct :
  fixes l :: "(('k :: linorder) * 'v) list"
  assumes Ord : "strict_order (map fst l)"
  assumes Cons' : "oacons' k v l = Some l'"
  shows "strict_order (map fst l')"
proof(cases l)
  case Nil
  then show ?thesis using Ord Cons' strict_order_singleton[of k]
    by(auto simp add: pred_option_def)
next
  case (Cons h t)

  obtain kh vh where H : "h = (kh, vh)"
    by(cases h; auto)

  have Lt : "k < kh"
    using Ord Cons' Cons H
    by(cases "k < kh"; auto)

  have Ord' : "strict_order (kh # map fst t)"
    using Ord Cons' Cons H
    by(auto)

  then show ?thesis
    using Cons' Cons H Lt strict_order_cons[OF Lt Ord']
    by(auto)
qed

lemma oacons'_destruct :
  fixes l :: "(('k :: linorder) * 'v) list"
  assumes Ord : "strict_order (map fst ((kh, vh) # lt))"
  shows "oacons' kh vh lt = Some ((kh, vh) # lt)"
proof(cases lt)
  case Nil
  then show ?thesis 
    by auto
next
  case (Cons h2 t2)

  obtain kh2 vh2 where H2 : "h2 = (kh2, vh2)"
    by(cases h2; auto)

  have Lt : "kh < kh2"
    using strict_order_unfold[OF Ord, of 1 0] Cons H2
    by(auto)

  then show ?thesis using Cons Ord H2
    by(auto)
qed

lift_definition oacons :: "'k :: linorder \<Rightarrow> 'v \<Rightarrow> ('k, 'v) oalist \<Rightarrow> ('k, 'v) oalist option"
is oacons'
proof-
  fix k :: "'k :: linorder"
  fix v :: "'v"
  fix l :: "('k * 'v) list"
  assume Ord : "strict_order (map fst l)"
  show "pred_option
        (\<lambda>xs. strict_order
                (map fst xs))
        (oacons' k v l)"
  proof(cases "oacons' k v l")
    case None
    then show ?thesis
      by(auto simp add: pred_option_def)
  next
    case (Some l')
    show ?thesis
      using oacons'_correct[OF Ord Some] Some Ord
      by(auto simp add: pred_option_def)
  qed
qed

lemma oalist_cases :
  shows "(oal :: ('k :: linorder, 'v) oalist) = empty \<or>
     (\<exists> hk hv oalt .
      oacons hk hv oalt = Some oal)"
proof(transfer)
  fix oal :: "('k * 'v) list"
  assume Ord : "strict_order (map fst oal)"
  show "oal = [] \<or>
       (\<exists>hk hv.
           \<exists>oalt\<in>{xs. strict_order (map fst xs)}.
              oacons' hk hv oalt = Some oal)"
  proof(cases oal)
    case Nil
    then show ?thesis by auto
  next
    case (Cons h t)

    obtain hk hv where H : "h = (hk, hv)"
      by(cases h; auto)

    have Conc1 : "strict_order (map fst t)"
      using strict_order_tl Ord Cons
      by(auto)

    have Conc2 : "oacons' hk hv t = Some ((hk, hv) # t)"
    proof(cases t)
      case Nil' : Nil
      then show ?thesis 
        by(auto)
    next
      case Cons' : (Cons h' t')

      obtain h'k h'v where H' : "h' = (h'k, h'v)"
        by(cases h'; auto)

      have Lt : "hk < h'k"
        using Cons Cons' H H' strict_order_unfold[OF Ord, of 1 0]
        by(auto)

      show ?thesis 
        using Cons Cons' H H' Ord Lt
        by(auto)
    qed

    show ?thesis using Cons H Conc1 Conc2
      by blast
  qed
qed

lemma oalist_ind_list :
  fixes P :: "('k :: linorder, 'v) oalist \<Rightarrow> bool"
  assumes PE : "P (empty :: ('k :: linorder, 'v) oalist)"
  assumes PC :
    "\<And> kh vh (l :: ('k, 'v) oalist) l' . 
      oacons kh vh l = Some l' \<Longrightarrow>
      P l \<Longrightarrow>
      P l'"
  shows "P (l :: ('k, 'v) oalist)"
  using assms
proof-
  fix P :: "('k :: linorder, 'v) oalist \<Rightarrow> bool"
  fix x
  show "P Oalist.empty \<Longrightarrow>
           (\<And>kh vh l l'.
               oacons kh vh l = Some l' \<Longrightarrow> P l \<Longrightarrow> P l') \<Longrightarrow>
           P x"
  proof(transfer; transfer)
    fix P :: "('k :: linorder * 'v) list \<Rightarrow> bool"
    fix x
    show "strict_order (map fst x) \<Longrightarrow>
           P [] \<Longrightarrow>
           (\<And>kh vh l l'.
               strict_order (map fst l) \<Longrightarrow>
               strict_order (map fst l') \<Longrightarrow>
               oacons' kh vh l = Some l' \<Longrightarrow> P l \<Longrightarrow> P l') \<Longrightarrow>
           P x"
    proof(induction x)
      case Nil
      then show ?case 
        by auto
    next
      case (Cons h t)

      obtain hk hv where H : "h = (hk, hv)"
        by(cases h; auto)

      have Ord_t : "strict_order (map fst t)"
        using strict_order_tl Cons.prems
        by(auto)

      have Pt : "P t"
        using Cons.prems Cons.IH[OF Ord_t Cons.prems(2)]
        by(auto)

      have Oacons : "oacons' hk hv t = Some (h # t)"
        using oacons'_destruct Cons.prems(1) H
        by(fastforce)

      show ?case using Cons.prems(3)[OF Ord_t Cons.prems(1) Oacons Pt]
        by(auto)
    qed
  qed
qed

lift_definition oalist_keys :: "('k :: linorder, 'v) oalist \<Rightarrow> 'k list"
is "map fst"
  .

lift_definition oalist_vals :: "('k :: linorder, 'v) oalist \<Rightarrow> 'v list"
is "map snd"
  .

fun oalist_flip' ::
  "('k :: linorder * 'k) list \<Rightarrow> ('k * 'k) list" where
"oalist_flip' [] = []"
| "oalist_flip' ((hl, hr)#t) =
   str_ord_update hr hl (oalist_flip' t)"

lemma oalist_flip'_correct :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  shows "strict_order (map fst (oalist_flip' l))"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons h t)

  obtain h1 h2 where H : "h = (h1, h2)"
    by(cases h; auto)

  have Ord_tl :
    "strict_order (map fst t)"
    using strict_order_tl Cons.prems
    by auto

  have Flip_tl : "strict_order (map fst (oalist_flip' t))"
    using Cons.IH[OF Ord_tl]
    by auto

  then show ?case using
    str_ord_update_correct [OF Flip_tl] H
    by(auto)
qed

lift_definition oalist_flip :: "('k :: linorder, 'k) oalist \<Rightarrow> ('k, 'k) oalist"
is oalist_flip'
  using oalist_flip'_correct
  by auto

lift_definition oalist_one_one :: "('k :: linorder, 'v) oalist \<Rightarrow> bool"
is "\<lambda> l . distinct (map snd l)"
  .

(*
lemma oalist_flip'_flip' :
  fixes l :: "('k :: linorder * 'k) list"
  assumes "strict_order (map fst l)"
  assumes "distinct (map snd l)"
  shows "oalist_flip' (oalist_flip' l) = l"
  using assms
proof(induction l)
  case Nil
  then show ?case
    by auto
next
  case (Cons h t)

  obtain hk hv where H: "h = (hk, hv)"
    by(cases h; auto)

  have Ord_tl : "strict_order (map fst t)"
    using Cons.prems H strict_order_tl
    by auto

  show ?case
    using Cons.prems Cons.IH[OF Ord_tl] H
    using oalist_flip'_update[OF oalist_flip'_correct[OF Ord_tl]]
    apply(auto)
  qed
*)
(*
lemma str_ord_update_map_snd : 
  assumes "strict_order l"
  assumes "distinct (map snd l)"
  assumes "v \<notin>
*)

(*
lemma oalist_flip_get_conv :
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  assumes "get (oalist_flip l) v = Some k"
  shows "get l k = Some v"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "\<And> v k. strict_order (map fst l) \<Longrightarrow> distinct (map snd l) \<Longrightarrow> map_of (oalist_flip' l) v = Some k \<Longrightarrow> map_of l k = Some v"
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

    have Dist_tl : "distinct (map snd (t))"
      using Cons.prems
      by auto

    show ?case
    proof(cases "k = hk")
      case True

      have Map_alt : "map_of (str_ord_update hv hk (oalist_flip' t)) hv = Some hk"
        using str_ord_update_get_eq[OF oalist_flip'_correct[OF Ord_tl]] Cons.prems H
        by fastforce

      have Map1 : "map_of (str_ord_update hv hk (oalist_flip' t)) v = Some hk"
        using Cons.prems H True
        by auto

      have Upd_ord : "strict_order (map fst (str_ord_update hv hk (oalist_flip' t)))"
        using str_ord_update_correct[OF oalist_flip'_correct[OF Ord_tl]]
        by auto

      hence Upd_dist : "distinct (map fst (str_ord_update hv hk (oalist_flip' t)))"
        using strict_order_distinct
        by auto

      have Upd_dist2 : "distinct (map snd (str_ord_update hv hk (oalist_flip' t)))"
        using oalist_flip'_map_snd
        by auto


      have Conc' : "hv = v"
        using map_of_SomeD[OF Map1] map_of_SomeD[OF Map_alt] Upd_dist2
        apply(auto)
        sorry

      show ?thesis using True Conc'
        using Cons.prems Cons.IH[OF Ord_tl Dist_tl] H 
        by(auto)
    next
      case False
      then show ?thesis sorry
    qed
      using Cons.prems Cons.IH[OF Ord_tl Dist_tl] H
      apply(auto)

    qed
*)
(* TODO: this can be weakened (I think) to remove the assumption that l is one-one *)
(*
lemma oalist_flip_one_one :
  fixes l :: "('k :: linorder, 'k) oalist"
  assumes "oalist_one_one l"
  shows "oalist_one_one (oalist_flip l)"
  using assms
proof(transfer)
  fix l :: "('k * 'k) list"
  show "strict_order (map fst l) \<Longrightarrow> distinct (map snd l) \<Longrightarrow> distinct (map snd (oalist_flip' l))"
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

    have Hk_notin : "hk \<notin> set (map fst t)"
      using strict_order_distinct[OF Cons.prems(1)] H
      by(auto)

    show ?case using Cons.IH[OF Ord_tl] Cons.prems H
      apply(auto)

  qed
*)
(*
lemma oalist_flip'_update :
  assumes H : "strict_order (map fst l)"
  assumes Hdist : "distinct (map snd l)"
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

(*
    have Eq1 : "str_ord_update v hk (str_ord_update hv hk (oalist_flip' t)) = 
                str_ord_update v hk (oalist_flip' (str_ord_update hv hk t))"
      using Cons.prems H True
      using sym[OF Cons.IH[OF Ord_tl, of hv hk]] 
      (*using str_ord_update_str_ord_update[OF oalist_flip'_correct[OF Ord_tl]]*)
      apply(auto)
*)

    show ?thesis
      using Cons.prems H True
      using sym[OF Cons.IH[OF Ord_tl, of hv hk]] 
      (*using str_ord_update_str_ord_update[OF oalist_flip'_correct[OF Ord_tl]]*)
      apply(auto)
  next
    case False
    then show ?thesis sorry
  qed
    using Cons.IH[OF Ord_tl] Cons.prems H
    apply(auto)
qed


lemma oalist_flip_flip : 
  fixes l :: "('k :: linorder, 'k) oalist"
  shows "oalist_flip (oalist_flip l) = l"
proof(transfer)
  fix l :: "('k * 'k) list"
  show "strict_order (map fst l) \<Longrightarrow>
         oalist_flip' (oalist_flip' l) = l"
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
      by fastforce

    show ?case using Cons.IH[OF Ord_tl] Cons.prems Lh
      apply(auto)
  qed
qed
*)

(*
lemma oalist_flip_get_Some :
  assumes "
*)
end