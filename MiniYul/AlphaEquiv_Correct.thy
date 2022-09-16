theory AlphaEquiv_Correct
  imports Semantics AlphaEquiv Oalist_Lemmas
begin

(* we need our primitives to not make reference to
 * the variable map. *)

definition prim_proper :: 
  "'g builtin \<Rightarrow> bool" where
"prim_proper p =
  (\<forall> vm1 vm2 g il .
    p g il vm1 = p g il vm2)"

definition mk_prim ::
  "('g \<Rightarrow> int list \<Rightarrow> ('g * int list) option) \<Rightarrow> 'g builtin" where
"mk_prim p =
  (\<lambda> g il vm . p g il)"

lemma mk_prim_proper : 
  shows "prim_proper (mk_prim f)"
  by(auto simp add: prim_proper_def mk_prim_def)

definition ctx_proper :: "'g fctx \<Rightarrow> bool" where
"ctx_proper fctx = 
  oalist_all_val
  (\<lambda> v . case v of
    Inl _ \<Rightarrow> True
    | Inr p \<Rightarrow> prim_proper p) fctx"


lemma alpha_equiv_varmap'_tl : 
  assumes "oacons kh vh l = Some l'"
  assumes "alpha_equiv_varmap' l' vm1 vm2"
  shows "alpha_equiv_varmap' l vm1 vm2"
  using assms
proof(transfer)
  fix kh vh
  fix l l' :: "(name * name) list"
  fix vm1 vm2
  assume Ord1 : "strict_order (map fst l)"
  assume Ord2 : "strict_order (map fst l')"
  assume Cons : "oacons' kh vh l = Some l'"
  assume Eqv : "alpha_equiv_varmap'l l' vm1 vm2"
  show "alpha_equiv_varmap'l l vm1 vm2"
    using Ord1 Ord2 Cons Eqv
    by(cases l; auto split: option.splits if_splits)
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


lemma alpha_equiv_varmap'_cons :
  fixes v1 v2 :: int
  assumes "oacons k1 k2 subst = Some subst'"
  assumes "alpha_equiv_varmap' subst' vm1 vm2"
  shows "get vm1 k1 = get vm2 k2"
  using assms
proof(transfer)
  fix subst'
  show "\<And>k1 k2 subst vm1 vm2 n1 n2.
       strict_order (map fst subst) \<Longrightarrow>
       strict_order (map fst subst') \<Longrightarrow>
       oacons' k1 k2 subst = Some subst' \<Longrightarrow>
       strict_order (map fst vm1) \<Longrightarrow>
       strict_order (map fst vm2) \<Longrightarrow>
       alpha_equiv_varmap'l subst' vm1 vm2 \<Longrightarrow> map_of vm1 k1 = map_of vm2 k2"
  proof(induction subst')
    case Nil
    then show ?case 
      by(cases subst; auto split: if_splits)
  next
    case (Cons subst'h subst't)

    obtain s'hk s'hv where S'h :
      "subst'h = (s'hk, s'hv)"
      by(cases subst'h; auto)

    have Subst' : "subst'h # subst't = ((k1, k2) # subst)"
      using oacons'_cons Cons.prems
      by fastforce

    show ?case
      using Cons.prems S'h Subst'
      by(auto split: option.splits)
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

lemma alpha_equiv_varmap'_get :
  fixes subst :: "(name, name) oalist"
  fixes vm1 vm2 :: "(name, int) oalist"
  assumes "alpha_equiv_varmap' subst vm1 vm2"
  assumes "get subst n1 = Some n2"
  shows "get vm1 n1 = get vm2 n2"
  using assms
proof(induction subst arbitrary: vm1 vm2 n1 n2 rule: oalist_ind_list)
  case Empty : 1
  show ?case
    using Empty(2)
    by(transfer; auto)
next
  case Oacons : (2 kh vh l l')

  have Eqv : "alpha_equiv_varmap' l vm1 vm2"
    using alpha_equiv_varmap'_tl Oacons.prems Oacons.hyps
    by fastforce

  show ?case 
  proof(cases "n1 = kh")
    case True

    have Eq' : "n2 = vh"
      using Oacons.prems Oacons.hyps True
      using get_hd[OF Oacons.hyps]
      by auto

    show ?thesis 
      using Oacons.prems Oacons.hyps True
      using alpha_equiv_varmap'_cons[OF Oacons.hyps Oacons.prems(1)]
      using Eq'
      by(auto)
  next
    case False

    have Get_tl : "get l n1 = Some n2"
      using get_tl[OF Oacons.hyps Oacons.prems(2) False]
      by auto

    then show ?thesis 
      using Oacons.prems Oacons.hyps Oacons.IH[OF Eqv Get_tl]
      by auto
  qed
qed

(*
lemma alpha_equiv_varmap'_empty :
  assumes "

*)

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


lemma alpha_equiv_varmap_name :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "alpha_equiv_name subst v1 v2"
  shows "varmap_get vm1 v1 = varmap_get vm2 v2"
  using assms
proof(induction subst arbitrary: vm1 vm2 v1 v2)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons substh substt)

  obtain vm1h vm1t where Vm1 :
    "vm1 = vm1h # vm1t"
    using Cons.prems
    by(cases vm1; auto)

  obtain vm2h vm2t where Vm2 :
    "vm2 = vm2h # vm2t"
    using Cons.prems
    by(cases vm2; auto)

  have Keys1 : "oalist_keys substh = oalist_keys vm1h"
    and Keys2 :
    "oalist_keys (oalist_flip substh) = oalist_keys vm2h"
    using Cons.prems Vm1 Vm2
    by(auto)

  have Equiv_varmap'_h :
    "alpha_equiv_varmap' substh vm1h vm2h"
    using Cons Vm1 Vm2
    by(auto)

  have One_one : "oalist_one_one substh"
    using Cons.prems Vm1 Vm2
    by auto

  show ?case
  proof(cases "get substh v1")
    case None1 : None

    have None2 : "get (oalist_flip substh) v2 = None"
      using None1 Cons.prems Vm1 Vm2
      by(cases "get (oalist_flip substh) v2"; auto)

    have None3 : "get vm1h v1 = None" 
      using oalist_keys_get_None[OF Keys1 None1]
      by auto

    have None4 : "get vm2h v2 = None"
      using oalist_keys_get_None[OF Keys2 None2] Cons.prems
      by auto

    show ?thesis 
      using None1 None2 Cons.prems None3 None4 Vm1 Vm2
      using Cons.IH
      by(auto)
  next
    case Some1 : (Some v2')

    have Some1' : "get substh v1 = Some v2"
      using Cons.prems Some1 Vm1 Vm2
      by(cases "get (oalist_flip substh) v2"; auto)

    have Some2 : "get (oalist_flip substh) v2 = Some v1"
      using Cons.prems Some1 Vm1 Vm2
      by(cases "get (oalist_flip substh) v2"; auto)

    obtain result where Some3 : "get vm1h v1 = Some result"
      using Cons.prems Some1 Vm1 Vm2 Some1' Some2
      using oalist_keys_get_Some[OF Keys1 Some1]
      by auto

    obtain result' where Some4 : "get vm2h v2 = Some result'"
      using Cons.prems Some1 Vm1 Vm2 Some1' Some2 Some3
      using oalist_keys_get_Some[OF Keys2 Some2]
      by(auto)

    have Results : "result = result'"
      using Cons.prems Vm1 Vm2 Some1' Some2 Some3 Some4
      using alpha_equiv_varmap'_get[OF Equiv_varmap'_h Some1']
      by(auto)

    show ?thesis
      using Cons.prems Vm1 Vm2 Some1' Some2 Some3 Some4 Results
      by auto
  qed
qed


lemma alpha_equiv_eval_expr1_correct :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "alpha_equiv_expr1
    subst e1 e2"
  shows "eval_expr1 vm1 e1 = eval_expr1 vm2 e2"
proof(cases e1)
  case (ELit x1)
  then show ?thesis 
    using assms
    by(cases e2; auto)
next
  case V1 : (EVar v1)

  then obtain v2 where V2 :
    "e2 = EVar v2"
    using assms
    by(cases e2; auto)

  show ?thesis using V1 V2 assms alpha_equiv_varmap_name
    by(auto)
qed

lemma alpha_equiv_eval_expr1s_correct :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "list_all2 (alpha_equiv_expr1 subst) e1s e2s"
  shows "eval_expr1s vm1 e1s = eval_expr1s vm2 e2s"
  using assms
proof(induction e1s arbitrary: subst vm1 vm2 e2s)
case Nil
  then show ?case 
    by(cases e2s; auto)
next
  case Cons1 : (Cons e1h e1t)

  then obtain e2h e2t where Cons2 :
    "e2s = e2h # e2t"
    by(cases e2s; auto)

  have All_tl : "list_all2 (alpha_equiv_expr1 subst) (e1t) e2t"
    using Cons1.prems Cons2
    by auto

  have Eqv_hd : "alpha_equiv_expr1 subst e1h e2h"
    using Cons1.prems Cons2
    by auto

  have Eval_hd : "eval_expr1 vm1 e1h = eval_expr1 vm2 e2h"
    using alpha_equiv_eval_expr1_correct[OF Cons1.prems(1) Eqv_hd]
    by auto

  show ?case using Cons1.prems Cons1.IH[OF Cons1.prems(1) All_tl] Cons2 Eval_hd
    by(auto split: option.split)
qed

fun alpha_equiv_results :: "subst \<Rightarrow> 'g state option \<Rightarrow> 'g state option \<Rightarrow> bool" where
"alpha_equiv_results _ None None = True"
| "alpha_equiv_results _ (Some (Error _)) (Some (Error _)) = True"
| "alpha_equiv_results subst (Some (Ok (vm1, g1))) (Some (Ok ((vm2, g2)))) =
   (alpha_equiv_varmap subst vm1 vm2 \<and> g1 = g2)"
| "alpha_equiv_results _ _ _ = False"

fun alpha_equiv_expr_results :: "(int list * 'g) orerror option \<Rightarrow> (int list * 'g) orerror option \<Rightarrow> bool"
  where
"alpha_equiv_expr_results None None = True"
| "alpha_equiv_expr_results (Some (Error _)) (Some (Error _)) = True"
| "alpha_equiv_expr_results (Some (Ok (res1, g1))) (Some (Ok ((res2, g2)))) =
   (res1 = res2 \<and> g1 = g2)"
| "alpha_equiv_expr_results _ _ = False"

lemma alpha_equiv_varmap'_update_miss :
  assumes "strict_order (map fst vm'1)"
  assumes "strict_order (map fst vm'2)"
  assumes "strict_order (map fst s')"
  assumes "distinct (map snd s')"
  assumes "n1 \<notin> fst ` set s'"
  assumes "n2 \<notin> snd ` set s'"
  assumes "alpha_equiv_varmap'l s' vm'1 vm'2"
  shows "alpha_equiv_varmap'l s' (str_ord_update n1 v vm'1)
     (str_ord_update n2 v vm'2)"
  using assms
proof(induction s' arbitrary: vm'1 vm'2 n1 n2 v)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons s'h s't)

  obtain nh1 nh2 where S'h : "s'h = (nh1, nh2)"
    by(cases s'h; auto)

  show ?case
  proof(cases "n1 = nh1")
    case True
    then show ?thesis
      using Cons S'h
      by(auto)
  next
    case Neq1 : False

    have Neq2 : "n2 \<noteq> nh2"
      using Cons S'h Neq1
      by(auto)

    obtain vh where Vh:
      "map_of vm'1 nh1 = Some vh" "map_of vm'2 nh2 = Some vh"
      "alpha_equiv_varmap'l s't vm'1 vm'2"
      using Cons S'h Neq1
      by(cases "map_of vm'1 nh1"; cases "map_of vm'2 nh2"; auto)

    have Ord_tl1 : "strict_order (map fst vm'1)"
      using Cons.prems strict_order_tl
      by auto

    have Ord_tl2 : "strict_order (map fst vm'2)"
      using Cons.prems strict_order_tl
      by auto

    have Get1 : "map_of (str_ord_update n1 v vm'1) nh1 = Some vh"
      using str_ord_update_get_neq[OF Ord_tl1 _] Neq1 Vh
      by auto

    have Get2 : "map_of (str_ord_update n2 v vm'2) nh2 = Some vh"
      using str_ord_update_get_neq[OF Ord_tl2 _] Neq2 Vh
      by auto

    have Ord_tl_subst : "strict_order (map fst s't)"
      using Cons.prems strict_order_tl
      by auto

    then show ?thesis 
      using Cons.prems Cons.IH[of vm'1 vm'2 n1 n2] S'h Vh Get1 Get2 Ord_tl1 Ord_tl2 Ord_tl_subst
      by(auto)
  qed
qed

lemma alpha_equiv_varmap'_update :
  assumes "alpha_equiv_name' subst' n1 n2"
  assumes "alpha_equiv_varmap' subst' vm'1 vm'2"
(*  assumes "oalist_keys subst' = oalist_keys vm'1"*)
  assumes "oalist_one_one subst'"
(*  assumes "oalist_keys (oalist_flip subst') = oalist_keys vm'2"*)
  shows "alpha_equiv_varmap' subst' (update n1 v vm'1) (update n2 v vm'2)"
  using assms
  unfolding alpha_equiv_name'_def
proof(transfer)
  fix subst' :: "(name * name) list"

  show "\<And>n1 n2 vm'1 vm'2 v .
       strict_order (map fst subst') \<Longrightarrow>
       (case (map_of subst' n1, map_of (oalist_flip' subst') n2) of
       (None, b) \<Rightarrow> False | (Some n2', None) \<Rightarrow> False
       | (Some n2', Some n1') \<Rightarrow> n1 = n1' \<and> n2 = n2') \<Longrightarrow>
       strict_order (map fst vm'1) \<Longrightarrow>
       strict_order (map fst vm'2) \<Longrightarrow>
       alpha_equiv_varmap'l subst' vm'1 vm'2 \<Longrightarrow>
       distinct (map snd subst') \<Longrightarrow>
       alpha_equiv_varmap'l subst' (str_ord_update n1 v vm'1)
        (str_ord_update n2 v vm'2)"
  proof(induction subst')
    case Nil
    then show ?case 
      by(auto)
  next
    case (Cons s'h s't)

    obtain nh1 nh2 where S'h : "s'h = (nh1, nh2)"
      by(cases s'h; auto)

    have Ord_tl_subst : "strict_order (map fst s't)"
      using Cons.prems strict_order_tl by auto

    show ?case

    proof(cases "nh1 = n1")
      case Eq1 : True

      have Eq2 : "nh2 = n2"
        using Cons.prems S'h Eq1
        by(cases "map_of (str_ord_update nh2 nh1 (oalist_flip' s't)) n2"; auto)

      have Get1 : "map_of (str_ord_update n1 v vm'1) n1 = Some v"
        using str_ord_update_get_eq Cons.prems
        by auto

      have Get2 : "map_of (str_ord_update n2 v vm'2) n2 = Some v"
        using str_ord_update_get_eq Cons.prems
        by auto

      have Ord_tl_subst : "strict_order (map fst s't)"
        using Cons.prems strict_order_tl by auto

      obtain vh where Vh:
        "map_of vm'1 nh1 = Some vh" "map_of vm'2 nh2 = Some vh"
        "alpha_equiv_varmap'l s't vm'1 vm'2"
        using Cons S'h Eq1
        by(cases "map_of vm'1 nh1"; cases "map_of vm'2 nh2"; auto)

      have Distinct1 : "distinct (nh1 # map fst s't)"
        using strict_order_distinct[OF Cons.prems(1)] S'h
        by auto

      have Notin1 : "n1 \<notin> fst ` set s't"
        using Distinct1 Eq1 
        by(auto)

      have Equiv_tl : "alpha_equiv_varmap'l s't vm'1 vm'2"
        using Cons.prems Vh
        by(auto)

      have Equiv_tl' : "alpha_equiv_varmap'l s't (str_ord_update n1 v vm'1) (str_ord_update n2 v vm'2)"
        using alpha_equiv_varmap'_update_miss[of vm'1 vm'2 s't nh1 nh2 v]
        using Cons.prems S'h Eq1 Ord_tl_subst Notin1 Get1 Get2 Equiv_tl Vh Eq1 Eq2
        by(auto)

      show ?thesis
        using Cons.prems S'h Eq1 Eq2 Get1 Get2 Cons.IH[of n1 n2 vm'1 vm'2 v]
        using Ord_tl_subst Equiv_tl'
        by(auto)
    next
      case Neq1 : False

      have N1_tl : "map_of s't n1 = Some n2"
        using Neq1 Cons.prems S'h
        by(auto split: option.splits)

      have N2_in : "n2 \<in> snd ` set s't"
        using imageI[OF map_of_SomeD[OF N1_tl], of snd]
        by(auto)

      have Neq2 : "nh2 \<noteq> n2"
        using Cons.prems Neq1 S'h N2_in
        by(auto)

      obtain vold where Vold : "map_of vm'1 nh1 = Some vold" "map_of vm'2 nh2 = Some vold"
        using Cons.prems S'h Neq1
        by(cases "map_of vm'1 nh1"; cases "map_of vm'2 nh2"; auto)

      have Get1 : "map_of (str_ord_update n1 v vm'1) nh1 = Some vold"
        using str_ord_update_get_neq[of vm'1 n1 nh1] Vold Cons.prems Neq1
        by(auto)

      have Get2 : "map_of (str_ord_update n2 v vm'2) nh2 = Some vold"
        using str_ord_update_get_neq[of vm'2 n2 nh2] Vold Cons.prems Neq2
        by(auto)

      have N2_tl : "map_of (oalist_flip' s't) n2 = Some n1"
        using oalist_flip'_get[OF Ord_tl_subst _ N1_tl] Cons.prems
        by(auto)

      show ?thesis using Cons.prems S'h Neq1 Neq2 Get1 Get2 N1_tl Vold Ord_tl_subst N2_tl
        using Cons.IH[of n1 n2 vm'1 vm'2 v]
        by(auto)
    qed
  qed
qed

lemma alpha_equiv_varmap_update :
  assumes "alpha_equiv_name subst n1 n2"
  assumes "alpha_equiv_varmap subst vm1 vm2"
  shows "alpha_equiv_varmap subst (varmap_update vm1 n1 v) (varmap_update vm2 n2 v)"
  using assms
proof(induction subst arbitrary: n1 n2 vm1 vm2 v)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons substh substt)

  obtain vm1h vm1t vm2h vm2t where Cons_vm : "vm1 = (vm1h # vm1t)" "vm2 = (vm2h # vm2t)"
    using Cons.prems
    by(cases vm1; cases vm2; auto)

  show ?case
  proof(cases "get substh n1")
    case None1 : None

    show ?thesis
    proof(cases "get (oalist_flip substh) n2")
      case None2 : None

      have Get1 : "get vm1h n1 = None"
        using Cons.prems None1 None2 Cons.IH Cons_vm
        using oalist_keys_get_None[of substh vm1h]
        by(auto)

      have Get2 : "get vm2h n2 = None"
        using Cons.prems None1 None2 Cons.IH Cons_vm
        using oalist_keys_get_None[of "oalist_flip substh" vm2h]
        by(auto)

      show ?thesis
        using Cons.prems None1 None2 Cons.IH Cons_vm Get1 Get2
        by(auto)
    next
      case Some2 : (Some val2)

      show ?thesis
        using Cons None1 Some2 Cons_vm
        by(auto)
    qed
  next
    case Some1 : (Some n2_alt)

    show ?thesis
    proof(cases "get (oalist_flip substh) n2")
      case None2 : None

      show ?thesis
        using Cons Some1 None2 Cons_vm
        by(auto)
    next
      case Some2 : (Some n1_alt)

      have N1_eq : "n1_alt = n1"
        using Cons.prems Some1 Some2 Cons_vm
        by(auto)

      have N2_eq : "n2_alt = n2"
        using Cons.prems Some1 Some2 Cons_vm
        by(auto)

      obtain val1_old where Get1 : "get vm1h n1 = Some val1_old"
        using Cons.prems Some1 Some2 Cons_vm N1_eq N2_eq
        using oalist_keys_get_Some[of substh vm1h n1]
        by(auto)

      obtain val2_old where Get2 : "get vm2h n2 = Some val2_old"
        using Cons.prems Some1 Some2 Cons_vm N1_eq N2_eq
        using oalist_keys_get_Some[of "oalist_flip substh" vm2h n2]
        by(auto)

      have Equiv_name' : "alpha_equiv_name' substh n1 n2"
        using Cons.prems Some1 Some2 Cons_vm N1_eq N2_eq
        by(auto simp add: alpha_equiv_name'_def)

      have Conc_vm' : "alpha_equiv_varmap' substh (update n1 v vm1h) (update n2 v vm2h)"
        using alpha_equiv_varmap'_update[OF Equiv_name']
        using Cons.prems Some1 Some2 Cons_vm N1_eq N2_eq Get1 Get2
        by(auto)

      have Conc_keys1 : "oalist_keys vm1h = oalist_keys (update n1 v vm1h)"
        using oalist_keys_update_hit[OF Get1]
        by auto

      have Conc_keys2 : "oalist_keys vm2h = oalist_keys (update n2 v vm2h)"
        using oalist_keys_update_hit[OF Get2]
        by auto

      show ?thesis
        using Cons.prems Some1 Some2 Cons_vm N1_eq N2_eq Get1 Get2
        using Conc_vm' Conc_keys1 Conc_keys2
        by(auto)
    qed
  qed
qed

lemma alpha_equiv_varmap_updates :
  assumes "list_all2 (alpha_equiv_name subst) ns1 ns2"
  assumes "alpha_equiv_varmap subst vm1 vm2"
  shows "alpha_equiv_varmap subst (varmap_updates vm1 (zip ns1 vals))
     (varmap_updates vm2 (zip ns2 vals))"
  using assms
proof(induction ns1 arbitrary: subst ns2 vm1 vm2 vals)
  case Nil1 : Nil
  then show ?case 
    by(cases vm2; auto)
next
  case Cons1 : (Cons n1h n1t)

  then obtain n2h n2t where Cons2 :
    "ns2 = n2h # n2t"
    by(cases ns2; auto)

  show ?case
  proof(cases vals)
    case Vnil : Nil

    then show ?thesis 
      using Cons1.prems Cons2
      by(auto)
  next
    case Vcons : (Cons vh vt)

    have Name_h : "alpha_equiv_name subst n1h n2h"
      using Cons1.prems Cons2
      by(auto)

    have Names_tl : "list_all2 (alpha_equiv_name subst) n1t n2t"
      using Cons1.prems Cons2
      by(auto)

    have Eqv_update :
      "alpha_equiv_varmap subst (varmap_update vm1 n1h vh) (varmap_update vm2 n2h vh)"
      using alpha_equiv_varmap_update[OF Name_h Cons1.prems(2)]
      by auto

    show ?thesis
      using Cons1.prems Cons2 Cons1.IH[OF Names_tl Eqv_update] Vcons
      by(auto)
  qed
qed

(*
lemma alpha_equiv_varmap_push :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  shows "alpha_equiv_varmap (Oalist.empty # subst) (Oalist.empty # vm1)  (Oalist.empty # vm2)"
  using assms
proof(induction ns1 arbitrary: subst vm1 vm2 ns2)
  case Nil
  then show ?case 
    apply(auto)
    sorry
next
  case (Cons ns1h ns1t)
  then show ?case 
    apply(auto)
*)

lemma alpha_equiv_varmap'_empty :
  shows "alpha_equiv_varmap' Oalist.empty Oalist.empty Oalist.empty"
  by(transfer; auto)

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

lemma varmap_insert_swap :
  assumes H : "k1 \<noteq> k2"
  shows "varmap_insert (varmap_insert vm k1 v1) k2 v2 =
    varmap_insert (varmap_insert vm k2 v2) k1 v1"
proof(cases vm)
  case Nil
  then show ?thesis
    using H
    by(auto)
next
  case (Cons vmh vmt)

  have H' : "k2 \<noteq> k1"
    using H by auto

  show ?thesis
    using Cons H oalist_update_swap[OF H', of v2 v1]
    by(auto)
qed

lemma varmap_extend_insert_swap :
  assumes "nh \<notin> set nt"
  assumes "distinct nt"
  shows "varmap_extend (varmap_insert vm nh 0) nt = 
         varmap_insert (varmap_extend vm nt) nh 0"
  using assms
proof(induction nt arbitrary: vm nh)
  case Nil
  then show ?case
    by(auto)
next
  case (Cons nh' nt)
  then show ?case  using varmap_insert_swap
    by(auto)
qed

(* strengthen the theorem to talk about subsets of keys? *)
lemma alpha_equiv_varmap'_update_fresh :
  assumes "alpha_equiv_varmap' subst' vm1' vm2'"
  assumes "oalist_one_one subst'"
  assumes "set (oalist_keys subst') \<subseteq> set (oalist_keys vm1')"
  assumes "set (oalist_keys (oalist_flip subst')) \<subseteq> set (oalist_keys vm2')"
  assumes "n1 \<notin> set (oalist_keys vm1')"
  assumes "n2 \<notin> set (oalist_keys vm2')"
  shows "alpha_equiv_varmap' (update n1 n2 subst') (update n1 v vm1') (update n2 v vm2')"
  using assms
proof(transfer)
  fix subst' 
  show "\<And>n1 n2 v vm1' vm2'.
       strict_order (map fst subst') \<Longrightarrow>
       strict_order (map fst vm1') \<Longrightarrow>
       strict_order (map fst vm2') \<Longrightarrow>
       alpha_equiv_varmap'l subst' vm1' vm2' \<Longrightarrow>
       distinct (map snd subst') \<Longrightarrow>
       set (map fst subst') \<subseteq> set (map fst vm1') \<Longrightarrow>
       set (map fst (oalist_flip' subst')) \<subseteq> set (map fst vm2') \<Longrightarrow>
       n1 \<notin> set (map fst vm1') \<Longrightarrow>
       n2 \<notin> set (map fst vm2') \<Longrightarrow>
       alpha_equiv_varmap'l (str_ord_update n1 n2 subst')
        (str_ord_update n1 v vm1') (str_ord_update n2 v vm2')"
  proof(induction subst')
    case Nil

    have Get1_n1 : "map_of (str_ord_update n1 v vm1') n1 = Some v"
      using str_ord_update_get_eq Nil
      by(auto)

    have Get2_n2 : "map_of (str_ord_update n2 v vm2') n2 = Some v"
      using str_ord_update_get_eq Nil
      by(auto)

    show ?case using Nil Get1_n1 Get2_n2
      by(auto)
  next
    case (Cons subst'h subst't)

    obtain hn1 hn2 where Subst'h :
      "subst'h = (hn1, hn2)"
      by(cases subst'h; auto)

    have Get1_hn1 : "map_of (str_ord_update hn1 v vm1') hn1 = Some v"
      using str_ord_update_get_eq[OF Cons.prems(2)]
      by(auto)

    have Get2_n2 : "map_of (str_ord_update n2 v vm2') n2 = Some v"
      using str_ord_update_get_eq[OF Cons.prems(3)]
      by(auto)

    have Get1_n1 : "map_of (str_ord_update n1 v vm1') n1 = Some v"
      using str_ord_update_get_eq[OF Cons.prems(2)]
      by(auto)

    have Ord_tl : "strict_order (map fst subst't)"
      using Cons.prems strict_order_tl
      by auto

    obtain val where Val :
      "map_of vm1' hn1 = Some val" "map_of vm2' hn2 = Some val"
      "alpha_equiv_varmap'l subst't vm1' vm2'"
      using Cons.prems Subst'h
      by(auto split: option.splits)

    show ?case
    proof(cases "n1 = hn1")
      case True1 : True

      have Notin1: "n1 \<notin> fst ` set subst't"
        using strict_order_distinct[OF Cons.prems(1)] Subst'h True1
        by(auto)

      show ?thesis
      proof(cases "n2 = hn2")
        case True2 : True

        show ?thesis using Cons.prems Subst'h
            Get1_hn1 Get2_n2 True1 Val Ord_tl Val True1 True2
          using alpha_equiv_varmap'_update_miss[of vm1' vm2' subst't n1] Notin1
          by(auto)
      next
        case False2 : False

        show ?thesis using Cons.prems Subst'h
            Get1_hn1 Get2_n2 True1 Val Ord_tl Val True1 False2
          by(auto)
      qed
    next
      case False1 : False
      show ?thesis
      proof(cases "n2 = hn2")
        case True2 : True

        have Notin2: "hn2 \<notin> fst ` set vm2'"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 False1 True2 Val Ord_tl Val
          by(auto)

        have Vm2 : "set (map fst (str_ord_update hn2 hn1 (oalist_flip' subst't))) \<subseteq> set (map fst vm2')"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 Val Ord_tl Val
          by(auto)

        have Vm2' : "fst ` set (str_ord_update hn2 hn1 (oalist_flip' subst't)) \<subseteq> fst ` set vm2'"
          unfolding sym[OF set_map]
          using Vm2
          by(auto)

        have Vm2'_set : "set (str_ord_update hn2 hn1 (oalist_flip' subst't)) =
          set (oalist_flip' subst't) - { x . fst x = hn2 } \<union> {(hn2, hn1)}"
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
          by auto

        have Bad : "(hn2) \<in>  fst ` set vm2'"
          using Vm2'_set Vm2'
          by(auto)

        show ?thesis using Bad Notin2
          by auto
      next
        case False2 : False

        have Get2_miss : "map_of (str_ord_update n2 v vm2') hn2 = Some val"
          using str_ord_update_get_neq[OF Cons.prems(3) False2, of v] Val
          by(auto)

        show ?thesis
        proof(cases "n1 < hn1")
          case True3 : True

          have Notin1 : "n1 \<notin> fst ` set vm1'"
            using Cons.prems Subst'h False1 strict_order_distinct[OF Cons.prems(1)]
            by(auto)

          have Keys1_alt : "fst ` set (subst'h # subst't) \<subseteq> fst ` set vm1'"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin1_alt : "n1 \<notin> fst ` set (subst'h # subst't)"
            using Notin1 Keys1_alt
            by(auto)

          have Notin1_alt_tl : "n1 \<notin> fst ` set (subst't)"
            using Notin1_alt
            by auto

          have Notin2 : "n2 \<notin> fst ` set vm2'"
            using Cons.prems Subst'h False1
            by(auto)

          have Keys2_alt : "fst ` set ((oalist_flip' (subst'h # subst't))) \<subseteq> fst ` (set vm2')"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin2_alt : "n2 \<notin> fst ` set ((oalist_flip' (subst'h # subst't))) "
            using Notin2 Keys2_alt
            by(auto)

          hence Notin2_alt2 : "n2 \<notin> fst ` (\<lambda>(x, y). (y, x)) ` set (subst'h # subst't)"
            using oalist_flip'_set[OF Cons.prems(1)] Cons.prems
            by(auto)

          have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
          proof
            fix w
            show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
              by(cases w; auto)
          qed

          have Notin2_alt3 : "n2 \<notin> snd ` set (subst'h # subst't)"
            using Notin2_alt2
            unfolding image_comp Fst_flip
            by(auto)

          have Notin2_alt_tl : "n2 \<notin> snd ` set (subst't)"
            using Notin2_alt3
            by auto

          have Get1_hn1' : "map_of (str_ord_update n1 v vm1') hn1 = Some val"
            using str_ord_update_get_neq[OF Cons.prems(2), of n1 hn1 v] False1
            using Val
            by auto

          show ?thesis using Cons.prems Subst'h False1 False2 True3
              Get1_n1 Get1_hn1' Get1_hn1 Get2_n2 False1 False2 Val Get2_miss
            using alpha_equiv_varmap'_update_miss[OF Cons.prems(2) Cons.prems(3) Ord_tl _ Notin1_alt_tl Notin2_alt_tl, of v]
            by(auto)
        next
          case False3 : False

          have Lt : "hn1 < n1"
            using False1 False2 False3
            by(auto)

          have Notin1 : "n1 \<notin> set (map fst vm1')"
            using Cons.prems Subst'h False1 strict_order_distinct[OF Cons.prems(1)]
            by(auto)

          have Notin2 : "n2 \<notin> set (map fst vm2')"
            using Cons.prems Subst'h False1 strict_order_distinct[OF Cons.prems(1)]
            by(auto)

          have Get1_hn1' : "map_of (str_ord_update n1 v vm1') hn1 = Some val"
            using str_ord_update_get_neq[OF Cons.prems(2), of n1 hn1 v] False1
            using Val
            by auto

          have Fst_flip : "fst o (\<lambda>(x, y). (y, x)) = snd"
          proof
            fix w
            show "(fst \<circ> (\<lambda>(x, y). (y, x))) w = snd w"
              by(cases w; auto)
          qed

          have Vm2'_superset : "fst ` set (oalist_flip' (subst'h # subst't)) \<subseteq> fst ` set vm2'"
            using Cons.prems
            by auto

          have Flip_set : "set (oalist_flip' (subst'h # subst't)) = 
            (\<lambda>(x, y). (y, x)) ` set (subst'h # subst't)"
            using oalist_flip'_set[OF Cons.prems(1)] Cons.prems
            by auto

          have Flip_set' : "set (oalist_flip' (subst't)) = 
            (\<lambda>(x, y). (y, x)) ` set (subst't)"
            using oalist_flip'_set[OF Ord_tl] Cons.prems
            by auto

(*          have Vm2'_superset' :*)
          have "fst ` (\<lambda>(x, y). (y, x)) ` set (subst'h # subst't) \<subseteq> fst ` set vm2'"
            using Vm2'_superset unfolding Flip_set
            by auto

          hence 
            "snd ` set (subst'h # subst't) \<subseteq> fst ` set vm2'"
            unfolding image_comp Fst_flip
            by auto

          hence "snd ` set (subst't) \<subseteq> fst ` set vm2'"
            by auto

          hence "(fst \<circ> (\<lambda>(x, y). (y, x))) ` set (subst't) \<subseteq> fst ` set vm2'"
            unfolding sym[OF Fst_flip]
            by auto

          hence "fst ` (\<lambda>(x, y). (y, x)) ` set (subst't) \<subseteq> fst ` set vm2'"
            by auto

          hence Vm2_superset' : "fst ` set (oalist_flip' subst't) \<subseteq> fst ` set vm2'"
            unfolding Flip_set'
            by auto

          show ?thesis using Cons.prems Subst'h False1 False2 False3
              Get1_hn1 Get1_hn1' Get2_n2 Get2_miss Val Lt 
            using Cons.IH[of vm1' vm2' n1 n2 v] Ord_tl Vm2_superset'
            by(auto)
        qed
      qed
    qed
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

lemma alpha_equiv_varmap_insert :
  assumes Heqv : "alpha_equiv_varmap (substh # substt) (vm1h # vm1t) (vm2h # vm2t)"
  assumes Hone_one : "oalist_one_one substh"
  assumes Hkeys1 : "oalist_keys substh = oalist_keys vm1h"
  assumes Hkeys2 : "oalist_keys (oalist_flip substh) = oalist_keys vm2h"
  assumes N1_notin : "n1 \<notin> set (oalist_keys vm1h)"
  assumes N2_notin : "n2 \<notin> set (oalist_keys vm2h)"
  shows "alpha_equiv_varmap (update n1 n2 substh # substt) (varmap_insert (vm1h # vm1t) n1 v) (varmap_insert (vm2h # vm2t) n2 v)"
  using assms
proof-

  have Heqv' : "alpha_equiv_varmap' substh vm1h vm2h"
    using Heqv
    by auto

  have Hkeys1' : "set (oalist_keys substh) \<subseteq> set (oalist_keys vm1h)"
    using Hkeys1 by auto

  have Hkeys2' : "set (oalist_keys (oalist_flip substh)) \<subseteq> set (oalist_keys vm2h)"
    using Hkeys2 by auto

  have Conc1 : 
    "alpha_equiv_varmap' (update n1 n2 substh) (update n1 v vm1h) (update n2 v vm2h)"
    using alpha_equiv_varmap'_update_fresh[OF Heqv' Hone_one Hkeys1' Hkeys2' N1_notin N2_notin]
    by(auto)

  have Conc2 : "oalist_keys (update n1 n2 substh) = oalist_keys (update n1 v vm1h)"
    using oalist_keys_update_eq[OF Hkeys1]
    by auto

  have N1_notin_alt : "n1 \<notin> set (oalist_keys substh)"
    using Hkeys1 N1_notin
    by auto

  have N2_notin_alt : "n2 \<notin> set (oalist_keys (oalist_flip substh))"
    using Hkeys2 N2_notin
    by auto

  have Conc3 : "oalist_keys (oalist_flip (update n1 n2 substh)) = oalist_keys (update n2 v vm2h)"
    using oalist_flip_update[OF Hone_one N1_notin_alt N2_notin_alt]
    using oalist_keys_update_eq[OF Hkeys2]
    by(auto)

  have Conc4 : "oalist_one_one (update n1 n2 substh)"
    using oalist_one_one_update[OF Hone_one, of n1 n2] Hkeys1 Hkeys2 N1_notin N2_notin
    by auto

  show ?thesis
    using assms Conc1 Conc2 Conc3 Conc4
    by(auto)
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

lemma varmap_extend_keys :
  shows 
    "\<exists> vmh' . ((varmap_extend (vmh # vm) ns) = vmh' # vm \<and>
      set (oalist_keys vmh') = set (oalist_keys vmh) \<union> set ns)"
proof(induction ns arbitrary: vmh vm)
  case Nil
  then show ?case 
    by(auto)
next
  case (Cons nh nt)

  obtain vmh' where Vmh' : "varmap_extend (update nh 0 vmh # vm) nt = vmh' # vm"
     "set (oalist_keys vmh') = set (oalist_keys (update nh 0 vmh)) \<union> set nt"
    using Cons.IH[of "update nh 0 vmh" vm]
    by(auto)

  have Conc' : "set (oalist_keys (update nh 0 vmh)) \<union> set nt =
    insert nh (set (oalist_keys vmh) \<union> set nt)"
    using Vmh'(2) 
    unfolding oalist_keys_update_set[of nh 0 vmh]
    by auto

  show ?case using Cons.prems Vmh' Conc'
    by(simp)
qed

lemma oalist_keys_empty :
  "(oalist_keys (Oalist.empty :: (name, int) oalist)) = []"
  by (transfer; auto)

lemma oalist_keys_empty_nm :
  "(oalist_keys (Oalist.empty :: (name, name) oalist)) = []"
  by (transfer; auto)

lemma oalist_one_one_empty :
  "oalist_one_one (Oalist.empty :: (name, name) oalist)"
  by(transfer; auto)

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

lemma oalist_keys_to_oalist :
  fixes l :: "(name * name) list"
  assumes "distinct (map fst l)"
  shows "set (oalist_keys (to_oalist l)) = set (map fst l)"
  using assms
proof(induction l)
  case Nil
  then show ?case using oalist_keys_empty_nm
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh :
    "lh = (lhk, lhv)"
    by(cases lh; auto)

  show ?case using Cons Lh oalist_keys_update_set[of lhk lhv]
    by(simp)
qed

lemma oalist_flip_empty :
  shows "oalist_flip (empty :: (name, name) oalist) = empty"
  by(transfer; auto)

lemma oalist_keys_to_oalist_flip_full :
  fixes l :: "(name * name) list"
  assumes "distinct (map fst l)"
  assumes "distinct (map snd l)"
  shows "set (oalist_keys (oalist_flip (to_oalist l))) = set (map snd l) \<and>
    oalist_one_one (to_oalist l)"
  using assms
proof(induction l)
  case Nil
  then show ?case 
    using oalist_flip_empty oalist_keys_empty_nm oalist_one_one_empty
    by(auto)
next
  case (Cons lh lt)

  obtain lhk lhv where Lh :
    "lh = (lhk, lhv)"
    by(cases lh; auto)

  have Ind : "set (oalist_keys (oalist_flip (to_oalist lt))) = set (map snd lt)"
    "oalist_one_one (to_oalist lt)"
    using Cons
    by auto

  have Notin1 : "lhk \<notin> set (oalist_keys (to_oalist lt))"
    using oalist_keys_to_oalist[of lt] Cons.prems Lh
    by(auto)

  have Notin2 : "lhv \<notin> set (oalist_keys (oalist_flip (to_oalist lt)))"
    using Ind Cons.prems Lh
    by(auto)

  have Flip : "(oalist_flip (update lhk lhv (to_oalist lt))) =
        update lhv lhk (oalist_flip (to_oalist lt))"
    using oalist_flip_update[OF Ind(2) Notin1 Notin2]
    by(auto)

  have Conc1 : "set (oalist_keys (update lhv lhk (oalist_flip (to_oalist lt)))) =
    insert lhv (snd ` set lt)"
    unfolding oalist_keys_update_set
    using Cons
    by(auto)

  have Conc2 : "oalist_one_one (update lhk lhv (to_oalist lt))"
    using oalist_one_one_update[OF Ind(2) Notin1 Notin2]
    by auto

  show ?case using Cons Lh Flip Conc1 Conc2
    by(clarsimp)
qed

lemma oalist_keys_to_oalist_flip :
  fixes l :: "(name * name) list"
  assumes "distinct (map fst l)"
  assumes "distinct (map snd l)"
  shows "set (oalist_keys (oalist_flip (to_oalist l))) = set (map snd l)"
  using assms oalist_keys_to_oalist_flip_full
  by auto

lemma to_oalist_one_one :
  fixes l :: "(name * name) list"
  assumes "distinct (map fst l)"
  assumes "distinct (map snd l)"
  shows "oalist_one_one (to_oalist l)"
  using assms oalist_keys_to_oalist_flip_full
  by auto

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

lemma to_oalist_flip_zip :
  fixes ns1 ns2 :: "(name) list"
  assumes "distinct ns1"
  assumes "distinct ns2"
  assumes "length ns1 = length ns2"
  shows "(oalist_flip (to_oalist (zip ns1 ns2))) = to_oalist (zip ns2 ns1)"
  using assms
proof(induction ns1 arbitrary: ns2)
  case Nil
  then show ?case using oalist_flip_empty oalist_one_one_empty
    by(auto)
next
  case Cons1 : (Cons ns1h ns1t)

  obtain ns2h ns2t where Cons2 : "ns2 = ns2h # ns2t"
    using Cons1.prems
    by(cases ns2; auto)

  have Tl : "oalist_flip (to_oalist (zip ns1t ns2t)) = to_oalist (zip ns2t ns1t)"
    using Cons1.IH[of ns2t] Cons1.prems Cons2
    by(auto)

  have Dist1' : "distinct (map fst (zip ns1t ns2t))"
    using map_fst_zip[OF Cons1.prems(3)] Cons1.prems Cons2
    by auto

  have Dist2' : "distinct (map snd (zip ns1t ns2t))"
    using map_snd_zip[OF Cons1.prems(3)] Cons1.prems Cons2
    by auto

  have One_one : "oalist_one_one (to_oalist (zip ns1t ns2t))"
    using to_oalist_one_one[OF Dist1' Dist2'] Cons1.prems
    by(auto)

  have One_one_flip : "oalist_one_one (oalist_flip (to_oalist (zip ns1t ns2t)))"
    using oalist_one_one_flip[OF One_one]
    by auto

  have Len_tl : "length ns1t = length ns2t"
    using Cons1.prems Cons2 by auto

  have Notin2 : "ns2h \<notin> set ns2t"
    using Cons1.prems Cons2
    by(auto)

  hence "ns2h \<notin> set (map snd (zip ns1t ns2t))"
    using map_snd_zip[OF Len_tl]
    by auto

  hence "ns2h \<notin> snd ` set (zip ns1t ns2t)"
    by auto
 
  hence Notin2' : "ns2h \<notin> set (oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t))))"
    using oalist_keys_to_oalist_flip[OF Dist1' Dist2']
    by(simp)

  have Notin1 : "ns1h \<notin> set ns1t"
    using Cons1.prems Cons2
    by(auto)

  hence "ns1h \<notin> set (map fst (zip ns1t ns2t))"
    using map_fst_zip[OF Len_tl]
    by auto

  hence "ns1h \<notin> fst ` set (zip ns1t ns2t)"
    by auto

  hence Notin1' : "ns1h \<notin> set (oalist_keys (to_oalist (zip ns1t ns2t)))"
    using oalist_keys_to_oalist[OF Dist1']
    by(simp)

  have Conc' : "oalist_flip (update ns1h ns2h (to_oalist (zip ns1t ns2t))) =
    update ns2h ns1h (to_oalist (zip ns2t ns1t))"
    using oalist_flip_update[OF One_one, OF Notin1' Notin2'] Cons1.prems Cons2 Tl(1)
    by(auto)

  show ?case
    using Cons1.prems Cons2 Tl Conc'
    by(auto)
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

lemma alpha_equiv_varmap_extend :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "length ns1 = length ns2"
  assumes "distinct ns1"
  assumes "distinct ns2"
  shows "alpha_equiv_varmap (to_oalist (zip ns1 ns2) # subst)
           (varmap_extend (Oalist.empty # vm1) ns1)
           (varmap_extend (Oalist.empty # vm2) ns2)"
  using assms
proof(induction ns1 arbitrary: subst vm1 vm2 ns2)
  case Nil

  have Keys : "oalist_keys Oalist.empty = oalist_keys Oalist.empty"
    by(transfer; auto)

  have One_one : "oalist_one_one Oalist.empty"
    by(transfer; auto)

  have Keys_flip : "oalist_keys (oalist_flip Oalist.empty) = oalist_keys Oalist.empty"
    by(transfer; auto)

  show ?case using Nil
    using alpha_equiv_varmap'_empty Keys One_one Keys_flip
    by(auto)
next
  case Cons1 : (Cons ns1h ns1t)

  then obtain ns2h ns2t where Cons2 : "ns2 = ns2h # ns2t"
    by(cases ns2; auto)

  have Vm_tl : "alpha_equiv_varmap (to_oalist (zip ns1t ns2t) # subst) (varmap_extend (Oalist.empty # vm1) ns1t) (varmap_extend (Oalist.empty # vm2) ns2t)"
    using Cons1.prems Cons2 Cons1.IH[OF Cons1.prems(1), of ns2t]
    by(auto)

  have Notin1 : "ns1h \<notin> set ns1t" "distinct ns1t"
    using Cons1.prems
    by auto

  have Notin2 : "ns2h \<notin> set ns2t" "distinct ns2t"
    using Cons1.prems Cons2
    by auto

  have "\<exists>vmh'.
     varmap_extend (Oalist.empty # vm1) ns1t = vmh' # vm1 \<and>
     set (oalist_keys vmh') = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns1t"
    using varmap_extend_keys[of empty vm1 ns1t]
    by auto

  then obtain xh1 where Xh1 :
    "(varmap_extend (Oalist.empty # vm1) ns1t) = xh1 # vm1"
    "set (oalist_keys xh1) = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns1t"
    by auto

  have "\<exists>vmh'.
     varmap_extend (Oalist.empty # vm2) ns2t = vmh' # vm2 \<and>
     set (oalist_keys vmh') = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns2t"
    using varmap_extend_keys[of empty vm2 ns2t]
    by auto

  then obtain xh2 where Xh2 :
    "(varmap_extend (Oalist.empty # vm2) ns2t) = xh2 # vm2"
    "set (oalist_keys xh2) = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns2t"
    by auto

  have Vm_tl' :
    "alpha_equiv_varmap (to_oalist (zip ns1t ns2t) # subst)
     (xh1 # vm1)
     (xh2 # vm2)"
    using Vm_tl
    unfolding Xh1(1) Xh2(1)
    by auto

  have Zip1 : "ns1t = map fst (zip ns1t ns2t)"
    using map_fst_zip Cons1.prems Cons2
    by(auto)

  have Zip2 : "ns2t = map snd (zip ns1t ns2t)"
    using map_fst_zip Cons1.prems Cons2
    by(auto)

  have One_one' : "oalist_one_one (to_oalist (zip ns1t ns2t))"
    using to_oalist_one_one[of "(zip ns1t ns2t)"] Cons1.prems Cons2 Zip1 Zip2
    by(auto)

  have Keys1' : "set (oalist_keys (to_oalist (zip ns1t ns2t))) = set (map fst (zip ns1t ns2t))"
    using oalist_keys_to_oalist[of "(zip ns1t ns2t)"] Zip1 Notin1
    by(auto)

  have Keys1x : "set (oalist_keys xh1) = set (map fst (zip ns1t ns2t))"
    using Xh1 oalist_keys_empty Zip1
    by(auto)

  have Keys1x_eq_set : "set (oalist_keys (to_oalist (zip ns1t ns2t))) = set (oalist_keys xh1)"
    using Keys1' Keys1x
    by auto

  have Keys1_eq : "(oalist_keys (to_oalist (zip ns1t ns2t))) = (oalist_keys xh1)"
    using strict_order_unique_set[OF _ _ Keys1x_eq_set]
    using strict_order_oalist_keys[of "(to_oalist (zip ns1t ns2t))"]
    using strict_order_oalist_keys[of "xh1"]
    by auto

  have Keys2' : "set (oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = (set (map snd (zip ns1t ns2t)))"
    using oalist_keys_to_oalist_flip[of "(zip ns1t ns2t)"] Zip1 Zip2 Notin1 Notin2
    by(auto)

  have Keys2x : "set (oalist_keys xh2) = set (map snd (zip ns1t ns2t))"
    using Xh2 oalist_keys_empty Zip2
    by(auto)

  have Keys2x_eq_set : "set (oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = set (oalist_keys xh2)"
    using Keys2' Keys2x
    by auto

  have Keys2_eq : "(oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = (oalist_keys xh2)"
    using strict_order_unique_set[OF _ _ Keys2x_eq_set]
    using strict_order_oalist_keys[of "(oalist_flip (to_oalist (zip ns1t ns2t)))"]
    using strict_order_oalist_keys[of "xh2"]
    by auto

  have Notin1' : "ns1h \<notin> set (oalist_keys xh1)"
    using Xh1(2) Notin1 oalist_keys_empty
    by(auto)

  have Notin2' : "ns2h \<notin> set (oalist_keys xh2)"
    using Xh2(2) Notin2 oalist_keys_empty
    by(auto)

  show ?case using Vm_tl Cons1.prems Cons2 Vm_tl
    using varmap_extend_insert_swap[OF Notin1(1) Notin1(2)]
    using varmap_extend_insert_swap[OF Notin2(1) Notin2(2)]
    using Xh1(1) Xh2(1)
    using alpha_equiv_varmap_insert[OF Vm_tl' One_one' Keys1_eq Keys2_eq Notin1' Notin2', of 0]
    by(auto simp del: varmap_insert.simps)
qed

(*
fix maps 1 and 2, assume they are alpha equiv

                have Vm_eq_pre_call : "alpha_equiv_varmap [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))] (varmap_inserts (varmap_extend [Oalist.empty] f1_rets) (zip f1_args res2))
                  (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2))"
*)

lemma alpha_equiv_varmap_inserts :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "length ns1 = length ns2"
  assumes "distinct ns1"
  assumes "distinct ns2"
  shows "alpha_equiv_varmap (to_oalist (zip ns1 ns2) # subst)
           (varmap_inserts (Oalist.empty # vm1) ns1)
           (varmap_extend (Oalist.empty # vm2) ns2)"
  using assms
proof(induction ns1 arbitrary: subst vm1 vm2 ns2)
  case Nil

  have Keys : "oalist_keys Oalist.empty = oalist_keys Oalist.empty"
    by(transfer; auto)

  have One_one : "oalist_one_one Oalist.empty"
    by(transfer; auto)

  have Keys_flip : "oalist_keys (oalist_flip Oalist.empty) = oalist_keys Oalist.empty"
    by(transfer; auto)

  show ?case using Nil
    using alpha_equiv_varmap'_empty Keys One_one Keys_flip
    by(auto)
next
  case Cons1 : (Cons ns1h ns1t)

  then obtain ns2h ns2t where Cons2 : "ns2 = ns2h # ns2t"
    by(cases ns2; auto)

  have Vm_tl : "alpha_equiv_varmap (to_oalist (zip ns1t ns2t) # subst) (varmap_extend (Oalist.empty # vm1) ns1t) (varmap_extend (Oalist.empty # vm2) ns2t)"
    using Cons1.prems Cons2 Cons1.IH[OF Cons1.prems(1), of ns2t]
    by(auto)

  have Notin1 : "ns1h \<notin> set ns1t" "distinct ns1t"
    using Cons1.prems
    by auto

  have Notin2 : "ns2h \<notin> set ns2t" "distinct ns2t"
    using Cons1.prems Cons2
    by auto

  have "\<exists>vmh'.
     varmap_extend (Oalist.empty # vm1) ns1t = vmh' # vm1 \<and>
     set (oalist_keys vmh') = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns1t"
    using varmap_extend_keys[of empty vm1 ns1t]
    by auto

  then obtain xh1 where Xh1 :
    "(varmap_extend (Oalist.empty # vm1) ns1t) = xh1 # vm1"
    "set (oalist_keys xh1) = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns1t"
    by auto

  have "\<exists>vmh'.
     varmap_extend (Oalist.empty # vm2) ns2t = vmh' # vm2 \<and>
     set (oalist_keys vmh') = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns2t"
    using varmap_extend_keys[of empty vm2 ns2t]
    by auto

  then obtain xh2 where Xh2 :
    "(varmap_extend (Oalist.empty # vm2) ns2t) = xh2 # vm2"
    "set (oalist_keys xh2) = set (oalist_keys (Oalist.empty :: (name, int) oalist)) \<union> set ns2t"
    by auto

  have Vm_tl' :
    "alpha_equiv_varmap (to_oalist (zip ns1t ns2t) # subst)
     (xh1 # vm1)
     (xh2 # vm2)"
    using Vm_tl
    unfolding Xh1(1) Xh2(1)
    by auto

  have Zip1 : "ns1t = map fst (zip ns1t ns2t)"
    using map_fst_zip Cons1.prems Cons2
    by(auto)

  have Zip2 : "ns2t = map snd (zip ns1t ns2t)"
    using map_fst_zip Cons1.prems Cons2
    by(auto)

  have One_one' : "oalist_one_one (to_oalist (zip ns1t ns2t))"
    using to_oalist_one_one[of "(zip ns1t ns2t)"] Cons1.prems Cons2 Zip1 Zip2
    by(auto)

  have Keys1' : "set (oalist_keys (to_oalist (zip ns1t ns2t))) = set (map fst (zip ns1t ns2t))"
    using oalist_keys_to_oalist[of "(zip ns1t ns2t)"] Zip1 Notin1
    by(auto)

  have Keys1x : "set (oalist_keys xh1) = set (map fst (zip ns1t ns2t))"
    using Xh1 oalist_keys_empty Zip1
    by(auto)

  have Keys1x_eq_set : "set (oalist_keys (to_oalist (zip ns1t ns2t))) = set (oalist_keys xh1)"
    using Keys1' Keys1x
    by auto

  have Keys1_eq : "(oalist_keys (to_oalist (zip ns1t ns2t))) = (oalist_keys xh1)"
    using strict_order_unique_set[OF _ _ Keys1x_eq_set]
    using strict_order_oalist_keys[of "(to_oalist (zip ns1t ns2t))"]
    using strict_order_oalist_keys[of "xh1"]
    by auto

  have Keys2' : "set (oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = (set (map snd (zip ns1t ns2t)))"
    using oalist_keys_to_oalist_flip[of "(zip ns1t ns2t)"] Zip1 Zip2 Notin1 Notin2
    by(auto)

  have Keys2x : "set (oalist_keys xh2) = set (map snd (zip ns1t ns2t))"
    using Xh2 oalist_keys_empty Zip2
    by(auto)

  have Keys2x_eq_set : "set (oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = set (oalist_keys xh2)"
    using Keys2' Keys2x
    by auto

  have Keys2_eq : "(oalist_keys (oalist_flip (to_oalist (zip ns1t ns2t)))) = (oalist_keys xh2)"
    using strict_order_unique_set[OF _ _ Keys2x_eq_set]
    using strict_order_oalist_keys[of "(oalist_flip (to_oalist (zip ns1t ns2t)))"]
    using strict_order_oalist_keys[of "xh2"]
    by auto

  have Notin1' : "ns1h \<notin> set (oalist_keys xh1)"
    using Xh1(2) Notin1 oalist_keys_empty
    by(auto)

  have Notin2' : "ns2h \<notin> set (oalist_keys xh2)"
    using Xh2(2) Notin2 oalist_keys_empty
    by(auto)

  show ?case using Vm_tl Cons1.prems Cons2 Vm_tl
    using varmap_extend_insert_swap[OF Notin1(1) Notin1(2)]
    using varmap_extend_insert_swap[OF Notin2(1) Notin2(2)]
    using Xh1(1) Xh2(1)
    using alpha_equiv_varmap_insert[OF Vm_tl' One_one' Keys1_eq Keys2_eq Notin1' Notin2', of 0]
    by(auto simp del: varmap_insert.simps)
qed

lemma alpha_equiv_varmap_pop :
  assumes H: "alpha_equiv_varmap (substh # subst) vm1 vm2"
  shows "alpha_equiv_varmap subst (varmap_pop vm1) (varmap_pop vm2)"
proof-
  obtain vm1h vm1t where Vm1 : "vm1 = vm1h # vm1t"
    using H
    by(cases vm1; auto)

  obtain vm2h vm2t where Vm2 : "vm2 = vm2h # vm2t"
    using H
    by(cases vm2; auto)

  show "alpha_equiv_varmap subst (varmap_pop vm1)
     (varmap_pop vm2)"
    using Vm1 Vm2 H
    by(auto)
qed

lemma alpha_equiv_fctx'_name :
  assumes "alpha_equiv_fctx' ns ns_full ctx1 ctx2"
  assumes "(f1, f2) \<in> set ns"

  shows "(case get ctx1 f1 of
    None \<Rightarrow> False
    | Some fh1 \<Rightarrow>
    (case get ctx2 f2 of
     None \<Rightarrow> False
     | Some fh2 \<Rightarrow>
      (case (fh1, fh2) of
        (Inl (Decl args1 rets1 body1), Inl (Decl args2 rets2 body2)) \<Rightarrow>
          (length args1 = length args2 \<and>
           length rets1 = length rets2 \<and>
           distinct (args1 @ rets1) \<and>
           distinct (args2 @ rets2) \<and>
           alpha_equiv_stmt ns_full [to_oalist (zip (args1 @ rets1) (args2 @ rets2))] ctx1 ctx2 body1 body2)
        | (Inr bh1, Inr bh2) \<Rightarrow>
          \<comment> \<open>(bh1 = bh2)\<close> True
        | (_, _) \<Rightarrow> False)))"
  using assms
proof(induction ns arbitrary: ns_full ctx1 ctx2 f1 f2)
  case Nil
  then show ?case by(auto)
next
  case (Cons nsh nst)

  obtain nsh1 nsh2 where Nsh :
    "nsh = (nsh1, nsh2)"
    by(cases nsh; auto)

  obtain fh1 where Fh1 : "get ctx1 nsh1 = Some fh1"
    using Cons Nsh
    by(cases "get ctx1 nsh1"; auto)

  obtain fh2 where Fh2 : "get ctx2 nsh2 = Some fh2"
    using Cons Nsh Fh1
    by(cases "get ctx2 nsh2"; auto)

  show ?case
  proof(cases fh1)
    case Inl1 : (Inl fh1d)

    obtain args1 rets1 body1 where
      Decl1 : "fh1d = Decl args1 rets1 body1"
      by(cases fh1d; auto)

    obtain fh2d where Inl2 : "fh2 = Inl fh2d"
      using Cons Nsh Fh1 Fh2 Inl1 Decl1
      by(cases fh2; auto)

    obtain args2 rets2 body2 where
      Decl2: "fh2d = Decl args2 rets2 body2"
      by(cases fh2d; auto)


    show ?thesis 
      using Cons Nsh Fh1 Fh2 Inl1 Decl1 Inl2 Decl2
      by(auto)
  next
    case Inr1 : (Inr err1)
    then show ?thesis 
      using Cons Nsh Fh1 Fh2
      by(cases fh2; auto)
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


lemma alpha_equiv_fctx_name :
  assumes Hfctx : "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
  assumes Hname' : "alpha_equiv_name' fsubst f1 f2"

  shows "(case get ctx1 f1 of
    None \<Rightarrow> False
    | Some fh1 \<Rightarrow>
    (case get ctx2 f2 of
     None \<Rightarrow> False
     | Some fh2 \<Rightarrow>
      (case (fh1, fh2) of
        (Inl (Decl args1 rets1 body1), Inl (Decl args2 rets2 body2)) \<Rightarrow>
          (length args1 = length args2 \<and>
           length rets1 = length rets2 \<and>
           distinct (args1 @ rets1) \<and>
           distinct (args2 @ rets2) \<and>
           alpha_equiv_stmt (to_oalist (impl_of fsubst)) [to_oalist (zip (args1 @ rets1) (args2 @ rets2))] ctx1 ctx2 body1 body2)
        | (Inr bh1, Inr bh2) \<Rightarrow>
          \<comment> \<open>(bh1 = bh2)\<close> True
        | (_, _) \<Rightarrow> False)))"
  using assms
proof-

  have Fctx' : " alpha_equiv_fctx' (impl_of fsubst) (to_oalist (impl_of fsubst)) ctx1 ctx2"
    using Hfctx
    by(auto simp add: alpha_equiv_fctx_def)

  hence Fctx'' : "alpha_equiv_fctx' (impl_of fsubst) fsubst ctx1 ctx2"
    using to_oalist_impl_of[of "impl_of fsubst" fsubst]
    by(auto simp add: alpha_equiv_fctx_def)

  have Get : "get fsubst f1 = Some f2"
    using Hname'
    by(auto simp add: alpha_equiv_name'_def split: option.splits)

  then have In : "(f1, f2) \<in> set (impl_of fsubst)"
  proof(transfer)
    fix fsubst :: "(name* name) list"
    fix f1 f2
    assume Mapof : "map_of fsubst f1 = Some f2" 
    show "(f1, f2) \<in> set fsubst"
      using map_of_SomeD[OF Mapof]
      by auto
  qed

  show ?thesis
    using Hfctx Hname'
      alpha_equiv_fctx'_name[OF Fctx' In]
    by(auto)
qed

lemma varmap_gets_length : 
  assumes "varmap_gets vm ns = Some vals"
  shows "length ns = length vals"
  using assms
proof(induction ns arbitrary: vm vals)
  case Nil
  then show ?case by auto
next
  case Cons1 : (Cons nsh nst)

  obtain vmh vmt where Cons2 : "vm = vmh # vmt"
    using Cons1
    by(cases vm; auto)

  show ?case
  proof(cases "get vmh nsh")
    case None

    obtain vh where Vh : "varmap_get vmt nsh = Some vh"
      using Cons1 Cons2 None
      by(cases "varmap_get vmt nsh"; auto)

    obtain vt where Vt : "varmap_gets (vmh # vmt) nst = Some vt"
      using Cons1 Cons2 None Vh
      by(cases "varmap_gets (vmh # vmt) nst"; auto)

    then show ?thesis using Cons1 Cons2 None Vh Vt
      by(auto)
  next
    case (Some vh)

    obtain vt where Vt : "varmap_gets (vmh # vmt) nst = Some vt"
      using Cons1 Cons2 Some
      by(cases "varmap_gets (vmh # vmt) nst"; auto)

    show ?thesis using Cons1 Cons2 Some Vt
      by(auto)
  qed
qed

lemma alpha_equiv_varmap_gets_names :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "list_all2 (alpha_equiv_name subst) vs1 vs2"
  shows "varmap_gets vm1 vs1 = varmap_gets vm2 vs2"
  using assms
proof(induction vs1 arbitrary: subst vm1 vm2 vs2)
  case Nil
  then show ?case
    by auto
next
  case Cons1 : (Cons v1h v1t)

  obtain v2h v2t where Cons2 : "vs2 = v2h # v2t"
    using Cons1.prems
    by(cases vs2; auto)

  have Eqv_h : "alpha_equiv_name subst v1h v2h"
    using Cons1.prems Cons2
    by auto

  show ?case using Cons1.prems Cons2
      alpha_equiv_varmap_name[OF Cons1.prems(1) Eqv_h]
      Cons1.IH[OF Cons1.prems(1), of v2t]
    by(auto split: option.splits)
qed

lemma alpha_equiv_eval_correct:
  shows "(\<forall> subst fsubst vm1 vm2 
          (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) .
          alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
          alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
          ((\<forall> stm1 stm2 g .
             alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
             alpha_equiv_results subst
              (eval_statement n ctx1 stm1 vm1 g)
              (eval_statement n ctx2 stm2 vm2 g)) \<and>
          (\<forall> expr1 expr2 g .
             alpha_equiv_expr fsubst subst expr1 expr2 \<longrightarrow>
             alpha_equiv_expr_results
              (eval_expression n ctx1 expr1 vm1 g)
              (eval_expression n ctx2 expr2 vm2 g)) \<and>
         (\<forall> stms1 stms2 g .
            list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2) stms1 stms2 \<longrightarrow>
            alpha_equiv_results subst
              (eval_statements n ctx1 stms1 vm1 g)
              (eval_statements n ctx2 stms2 vm2 g)))
         )"
proof(induction n)
  case 0
  then show ?case
    by(auto)
next
  case (Suc n')

  have IH1 :
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) stm1 stm2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
         alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<Longrightarrow>
         alpha_equiv_results subst
              (eval_statement n' ctx1 stm1 vm1 g)
              (eval_statement n' ctx2 stm2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx" 
    fix ctx2 stm1 stm2 g
    
    show "alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
       alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
       alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<Longrightarrow>
       alpha_equiv_results subst (eval_statement n' ctx1 stm1 vm1 g)
        (eval_statement n' ctx2 stm2 vm2 g)"
      using spec[OF Suc.IH, of subst]
      by(auto)
  qed

  have IH2 :
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) expr1 expr2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
         alpha_equiv_expr fsubst subst expr1 expr2 \<Longrightarrow>
         alpha_equiv_expr_results (eval_expression n' ctx1 expr1 vm1 g) (eval_expression n' ctx2 expr2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx"
    fix ctx2 expr1 expr2 g

    show "alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
       alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
       alpha_equiv_expr fsubst subst expr1 expr2 \<Longrightarrow>
       alpha_equiv_expr_results (eval_expression n' ctx1 expr1 vm1 g)
        (eval_expression n' ctx2 expr2 vm2 g)"
      using spec[OF Suc.IH, of subst]
      by fastforce
  qed

  have IH3 :
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) stms1 stms2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
       list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2) stms1 stms2 \<Longrightarrow>
       alpha_equiv_results subst (eval_statements n' ctx1 stms1 vm1 g) (eval_statements n' ctx2 stms2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx"
    fix ctx2 stms1 stms2 g

    show "alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
       alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
       list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2)
        stms1 stms2 \<Longrightarrow>
       alpha_equiv_results subst (eval_statements n' ctx1 stms1 vm1 g) (eval_statements n' ctx2 stms2 vm2 g)"
      using spec[OF Suc.IH, of subst]
      by fastforce
  qed

  have Conc1 : 
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) stm1 stm2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
         alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<Longrightarrow>
         alpha_equiv_results subst (eval_statement (Suc n') ctx1 stm1 vm1 g) (eval_statement (Suc n') ctx2 stm2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx"
    fix ctx2 stm1 stm2 g

    assume Hvm : "alpha_equiv_varmap subst vm1 vm2"
    assume Hfctx : "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
    assume Heqv : "alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2"
    show "alpha_equiv_results subst (eval_statement (Suc n') ctx1 stm1 vm1 g) (eval_statement (Suc n') ctx2 stm2 vm2 g)"
    proof(cases stm1)
      case SB1 : (SBlock ns1 body1)

      then obtain ns2 body2 where SB2 : "stm2 = SBlock ns2 body2"
        using Heqv
        by(cases stm2; auto)

      have Bodies : "list_all2 (alpha_equiv_stmt fsubst
        (to_oalist (zip ns1 ns2) # subst) ctx1 ctx2) body1 body2"
        using Heqv SB1 SB2
        by(auto)

      have Ns_lengths : "length ns1 = length ns2"
        using Heqv SB1 SB2
        by(auto)

      have Ns_distinct1 : "distinct ns1"
        using Heqv SB1 SB2
        by(auto)

      have Ns_distinct2 : "distinct ns2"
        using Heqv SB1 SB2
        by(auto)

      have Vm_extend : "alpha_equiv_varmap (to_oalist (zip ns1 ns2) # subst)
           (varmap_extend (Oalist.empty # vm1) ns1)
           (varmap_extend (Oalist.empty # vm2) ns2)"
        using alpha_equiv_varmap_extend[OF Hvm Ns_lengths Ns_distinct1 Ns_distinct2]
        by auto

      show ?thesis
      proof(cases "eval_statements n' ctx1 body1
            (varmap_extend (Oalist.empty # vm1) ns1) g")
        case None1 : None

        then have None2 :
          "(eval_statements n' ctx2 body2 (varmap_extend (Oalist.empty # vm2) ns2) g) = None"
          using SB1 SB2 Hvm IH3[OF Vm_extend Hfctx Bodies, of g]
          by(cases "(eval_statements n' ctx2 body2 (varmap_extend (Oalist.empty # vm2) ns2) g)"; auto)

        show ?thesis
          using SB1 SB2 None1 None2
          by(auto)
      next
        case Some1 : (Some res1)

        then obtain res2 where Some2 :
          "(eval_statements n' ctx2 body2 (varmap_extend (Oalist.empty # vm2) ns2) g) = Some res2"
          using SB1 SB2 Hvm IH3[OF Vm_extend Hfctx Bodies, of g]
          by(cases "(eval_statements n' ctx2 body2 (varmap_extend (Oalist.empty # vm2) ns2) g)"; auto)

        show ?thesis
        proof(cases res1)
          case Ok1 : (Ok res1_p)

          obtain res1_vm res1_g where Res1 :
            "res1_p = (res1_vm, res1_g)"
            by(cases res1_p; auto)

          then obtain res2_p where Ok2 : "res2 = Ok res2_p"
            using SB1 SB2 Heqv Some1 Some2 Ok1 IH3[OF Vm_extend Hfctx Bodies, of g]
            by(cases res2; auto)

          obtain res2_vm res2_g where Res2 :
            "res2_p = (res2_vm, res2_g)"
            by(cases res2_p; auto)

          have Vmeq_result : "alpha_equiv_varmap (to_oalist (zip ns1 ns2) # subst) res1_vm res2_vm"
            using SB1 SB2 Hvm IH3[OF Vm_extend Hfctx Bodies, of g] Some1 Ok1 Res1 Some2 Ok2 Res2
            by(auto)

          have Pop : "alpha_equiv_varmap subst (varmap_pop res1_vm) (varmap_pop res2_vm)"
            using alpha_equiv_varmap_pop[OF Vmeq_result]
            by(auto)

          show ?thesis 
            using SB1 SB2 Heqv Some1 Some2 Ok1 Res1 Ok2 Res2 IH3[OF Vm_extend Hfctx Bodies, of g]
            using Pop
            by(auto)
        next
          case Error1 : (Error err1)

          then obtain err2 where Error2 : "res2 = Error err2"
            using SB1 SB2 Heqv Some1 Some2 Error1 IH3[OF Vm_extend Hfctx Bodies, of g]
            by(cases res2; auto)

          then show ?thesis 
            using SB1 SB2 Heqv Some1 Some2 Error1 Error2
            by auto
        qed
      qed
    next
      case SA1 : (SAssn ns1 exp1)

      then obtain ns2 exp2 where SA2 : "stm2 = SAssn ns2 exp2"
        using Heqv
        by(cases stm2; auto)

      have Names_eqv : "list_all2 (alpha_equiv_name subst) ns1 ns2"
        using Heqv SA1 SA2
        by auto

      have Exps_eqv : "alpha_equiv_expr fsubst subst exp1 exp2"
        using Heqv SA1 SA2
        by auto

      show ?thesis
      proof(cases "eval_expression n' ctx1 exp1 vm1 g")
        case None1 : None

        then have None2 : "eval_expression n' ctx2 exp2 vm2 g = None"
          using Heqv IH2[OF Hvm Hfctx Exps_eqv, of g]
          by(cases "eval_expression n' ctx2 exp2 vm2 g"; auto)

        show ?thesis using None1 None2 SA1 SA2
          by(auto)
      next
        case Some1 : (Some res1)

        then obtain res2 where Some2 : "eval_expression n' ctx2 exp2 vm2 g = Some res2"
          using Heqv IH2[OF Hvm Hfctx Exps_eqv, of g]
          by(cases "eval_expression n' ctx2 exp2 vm2 g"; auto)

        show ?thesis
        proof(cases res1)
          case Ok1 : (Ok res1')

          then obtain res2' where Ok2 : "res2 = Ok res2'"
            using Heqv SA1 SA2 Some1 Some2
            using IH2[OF Hvm Hfctx Exps_eqv, of g]
            by(cases res2; auto)

          obtain vals1 g1 where Res1' : "res1' = (vals1, g1)"
            by(cases res1'; auto)

          obtain vals2 g2 where Res2' : "res2' = (vals2, g2)"
            by(cases res2'; auto)

          have Ns_len : "length ns1 = length ns2"
            using list_all2_lengthD[OF Names_eqv]
            by auto

          have Conc' : "alpha_equiv_varmap subst (varmap_updates vm1 (zip ns1 vals2))
            (varmap_updates vm2 (zip ns2 vals2))"
            using alpha_equiv_varmap_updates[OF Names_eqv Hvm]
            by auto

          show ?thesis
            using Heqv SA1 SA2 Some1 Some2 Ok1 Ok2 Res1' Res2'
            using IH2[OF Hvm Hfctx Exps_eqv, of g] Ns_len Conc'
            by(auto)
        next
          case Error1 : (Error err1)

          then obtain err2 where Error2 : "res2 = Error err2"
            using Heqv SA1 SA2 Some1 Some2
            using IH2[OF Hvm Hfctx Exps_eqv, of g]
            by(cases res2; auto)

          show ?thesis using Heqv SA1 SA2 Some1 Some2 Error1 Error2
            by(auto)
        qed

      qed
    next
      case SI1 : (SIf c1 t1 f1)

      then obtain c2 t2 f2 where SI2 : "stm2 = SIf c2 t2 f2"
        using Heqv
        by(cases stm2; auto)

      have Cond_eqv : "alpha_equiv_expr1 subst c1 c2"
        using Heqv SI1 SI2
        by(auto)

      show ?thesis
      proof(cases "eval_expr1 vm1 c1")
        case None1 : None

        have None2 : "eval_expr1 vm2 c2 = None"
          using SI1 SI2 Heqv None1 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        show ?thesis
          using SI1 SI2 Heqv None1 None2 
          by(auto)
      next
        case Some1 : (Some res1)

        obtain res2 where Some2 : "eval_expr1 vm2 c2 = Some res2" 
          using SI1 SI2 Heqv Some1 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        have Res_eq : "res1 = res2"
          using SI1 SI2 Heqv Some1 Some2 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        show ?thesis
        proof(cases "res1 = 0")
          case True

          show ?thesis
            using SI1 SI2 Heqv Some1 Some2 True Res_eq
            using IH1[OF Hvm Hfctx]
            by(auto)
        next
          case False
          show ?thesis
            using SI1 SI2 Heqv Some1 Some2 False Res_eq
            using IH1[OF Hvm Hfctx]
            by(auto)
        qed
      qed
    next
      case SW1 : (SWhile c1 b1)
      then obtain c2 b2 where SW2 : "stm2 = SWhile c2 b2"
        using Heqv
        by(cases stm2; auto)

      have Cond_eqv : "alpha_equiv_expr1 subst c1 c2"
        using Heqv SW1 SW2
        by(auto)

      show ?thesis
      proof(cases "eval_expr1 vm1 c1")
        case None1 : None

        have None2 : "eval_expr1 vm2 c2 = None"
          using SW1 SW2 Heqv None1 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        show ?thesis
          using SW1 SW2 Heqv None1 None2 
          by(auto)
      next
        case Some1 : (Some res1)

        obtain res2 where Some2 : "eval_expr1 vm2 c2 = Some res2" 
          using SW1 SW2 Heqv Some1 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        have Res_eq : "res1 = res2"
          using SW1 SW2 Heqv Some1 Some2 alpha_equiv_eval_expr1_correct[OF Hvm Cond_eqv]
          by(auto)

        have Heqv' :
          "alpha_equiv_stmt fsubst subst ctx1 ctx2 b1 b2"
          using SW1 SW2 Heqv Some1 Some2
          by(auto)

        show ?thesis
        proof(cases "res1 = 0")
          case True

          show ?thesis
            using SW1 SW2 Heqv Some1 Some2 True Res_eq Hvm
            by(auto)
        next
          case False
          show ?thesis

          proof(cases "eval_statement n' ctx1 b1 vm1 g")
            case None_stm1 : None
            show ?thesis
            proof(cases "eval_statement n' ctx2 b2 vm2 g")
              case None_stm2 : None
              then show ?thesis
                using SW1 SW2 Heqv Some1 Some2 False None_stm1 Res_eq
                using IH1[OF Hvm Hfctx Heqv', of g]
                by(auto)
            next
              case Some_stm2 : (Some stm_res2)

              show ?thesis
                using SW1 SW2 Heqv Some1 Some2 False None_stm1 Some_stm2 Res_eq
                using IH1[OF Hvm Hfctx Heqv', of g]
                by(auto)
            qed
          next
            case Some_stm1 : (Some stm_res1)
            show ?thesis
            proof(cases "eval_statement n' ctx2 b2 vm2 g")
              case None_stm2 : None
              then show ?thesis
                using SW1 SW2 Heqv Some1 Some2 False Some_stm1 Res_eq
                using IH1[OF Hvm Hfctx Heqv', of g] 
                by(auto)
            next
              case Some_stm2 : (Some stm_res2)

              show ?thesis
              proof(cases stm_res1)
                case Ok1 : (Ok stm_res1')
                show ?thesis
                proof(cases stm_res2)
                  case Ok2 : (Ok stm_res2')
    
                  obtain vm1' g1' where Res1' :
                    "stm_res1' = (vm1', g1')"
                    by(cases stm_res1'; auto)

                  obtain vm2' g2' where Res2' :
                    "stm_res2' = (vm2', g2')"
                    by(cases stm_res2'; auto)

                  have Eqv' : "alpha_equiv_varmap subst vm1' vm2'" "g1' = g2'"
                    using SW1 SW2 Heqv Some1 Some2 False Res_eq Some_stm1 Some_stm2 Ok1 Ok2 Res1' Res2'
                    using IH1[OF Hvm Hfctx Heqv', of g] 
                    by(auto)

                  show ?thesis
                    using SW1 SW2 Heqv Some1 Some2 False Res_eq Some_stm1 Some_stm2 Ok1 Ok2 Res1' Res2'
                    using IH1[OF Eqv'(1) Hfctx Heqv] Eqv'(2)
                    by(auto)
                next
                  case Error2 : (Error err2)
                  then show ?thesis
                    using SW1 SW2 Heqv Some1 Some2 False Res_eq Some_stm1 Some_stm2 Ok1 Error2
                    using IH1[OF Hvm Hfctx Heqv', of g] Suc.prems
                    by(auto)
                qed
              next
                case Error1 : (Error err1)
                show ?thesis
                proof(cases stm_res2)
                  case Ok2 : (Ok stm_res2')
                  then show ?thesis
                    using SW1 SW2 Heqv Some1 Some2 False Res_eq Some_stm1 Some_stm2 Error1 Ok2
                    using IH1[OF Hvm Hfctx Heqv', of g] Suc.prems
                    by(auto)
                next
                  case Error2 : (Error err2)
                  then show ?thesis
                    using SW1 SW2 Heqv Some1 Some2 False Res_eq Some_stm1 Some_stm2 Error1 Error2
                    using IH1[OF Hvm Hfctx Heqv', of g] Suc.prems
                    by(auto)
                qed
              qed
            qed
          qed
        qed
      qed
    next
      case SS1 : SSkip

      then have SS2 : "stm2 = SSkip"
        using Heqv
        by(cases stm2; auto)

      show ?thesis using SS1 SS2 Hvm
        by(auto)
    qed
  qed

  have Conc2 : 
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) expr1 expr2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
         alpha_equiv_expr fsubst subst expr1 expr2 \<Longrightarrow>
         alpha_equiv_expr_results (eval_expression (Suc n') ctx1 expr1 vm1 g) (eval_expression (Suc n') ctx2 expr2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx"
    fix ctx2 expr1 expr2 g

    assume Hvm : "alpha_equiv_varmap subst vm1 vm2"
    assume Hfctx : "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
    assume Heqv : "alpha_equiv_expr fsubst subst expr1 expr2"
    show "alpha_equiv_expr_results
        (eval_expression (Suc n') ctx1 expr1 vm1 g)
        (eval_expression (Suc n') ctx2 expr2 vm2 g)"
    proof(cases expr1)
      case Eone1 : (E1 e1)

      obtain e2 where Eone2 : "expr2 = E1 e2"
        using Heqv Eone1
        by(cases expr2; auto)

      show ?thesis using Eone1 Eone2 Heqv alpha_equiv_eval_expr1s_correct[OF Hvm, of e1 e2]
        by(auto split: option.split)
    next
      case EPrim1 : (EPrim f1 args1)

      obtain f2 args2 where EPrim2 : "expr2 = EPrim f2 args2"
        using EPrim1 Heqv
        by(cases expr2; auto)

      have Args : "eval_expr1s vm1 args1 = eval_expr1s vm2 args2"
        using EPrim1 EPrim2 Heqv alpha_equiv_eval_expr1s_correct[OF Hvm, of args1 args2]
        by auto

      show ?thesis 
      proof(cases "eval_expr1s vm1 args1")
        case None1 : None
        then show ?thesis 
          using EPrim1 EPrim2 Args
          by(cases "eval_expr1s vm2 args2"; auto)
      next
        case Some1 : (Some res1)

        obtain res2 where Some2 :
          "eval_expr1s vm2 args2 = Some res2"
          using EPrim1 EPrim2 Heqv Some1 Args
          by(cases "eval_expr1s vm2 args2"; auto)

        show ?thesis 
          sorry
      qed
    next

      case EFun1 : (EFun f1 args1)
      obtain f2 args2 where EFun2 : "expr2 = EFun f2 args2"
        using EFun1 Heqv
        by(cases expr2; auto)

      have Args : "eval_expr1s vm1 args1 = eval_expr1s vm2 args2"
        using EFun1 EFun2 Heqv alpha_equiv_eval_expr1s_correct[OF Hvm, of args1 args2]
        by auto

      have Fname : "alpha_equiv_name' fsubst f1 f2"
        using EFun1 EFun2 Args Heqv
        by(auto)

      show ?thesis 
      proof(cases "eval_expr1s vm1 args1")
        case None1 : None
        then show ?thesis 
          using EFun1 EFun2 Args
          by(cases "eval_expr1s vm2 args2"; auto)
      next
        case Some1 : (Some res1)

        obtain res2 where Some2 :
          "eval_expr1s vm2 args2 = Some res2"
          using EFun1 EFun2 Heqv Some1 Args
          by(cases "eval_expr1s vm2 args2"; auto)

        show ?thesis 
        proof(cases "get ctx1 f1")
          case None_get_ctx1 : None


          show ?thesis
          proof(cases "get ctx2 f2")
            case None_get_ctx2 : None
            show ?thesis
              using EFun1 EFun2 Args Some1 Some2 Heqv None_get_ctx1 None_get_ctx2
              by auto
          next
            case Some_get_ctx2 : (Some fres2)
            then show ?thesis 
              using EFun1 EFun2 Args Some1 Some2 Heqv Hfctx None_get_ctx1 Some_get_ctx2
              using alpha_equiv_fctx_name[OF Hfctx Fname]
              by(auto)
          qed
        next
          case Some_get_ctx1 : (Some fres1)

          show ?thesis
          proof(cases "get ctx2 f2")
            case None_get_ctx2 : None
            show ?thesis
              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 None_get_ctx2
              using alpha_equiv_fctx_name[OF Hfctx Fname]
              by(auto)
          next
            case Some_get_ctx2 : (Some fres2)

            show ?thesis
            proof(cases fres1)
              case Inl1 : (Inl decl1)

              obtain f1_args f1_rets f1_body where
                Decl1 : "decl1 = Decl f1_args f1_rets f1_body"
                by(cases decl1; auto)

              show ?thesis
              proof(cases fres2)
                case Inl2 : (Inl decl2)

                obtain f2_args f2_rets f2_body where
                  Decl2 : "decl2 = Decl f2_args f2_rets f2_body"
                  by(cases decl2; auto)

                have Args_len_eq : "length f1_args = length f2_args"
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                    EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                  by(auto)

                have Rets_len_eq : "length f1_rets = length f2_rets"
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                    EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                  by(auto)

                have Args_rets_dist1 :
                  "distinct (f1_args @ f1_rets)"
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                    EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                  by(auto)

                have Args_rets_dist2 :
                  "distinct (f2_args @ f2_rets)"
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                    EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                  by(auto)

                have Vm_eq_pre_call : "alpha_equiv_varmap [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))] (varmap_inserts (varmap_extend [Oalist.empty] f1_rets) (zip f1_args res2))
                  (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2))"
                  apply(simp)
                  (* alpha_equiv_varmap_updates, applied to a varmap with only args and rets *)
                  sorry

                have Bodies : "alpha_equiv_stmt (to_oalist (impl_of fsubst)) [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))] ctx1 ctx2 f1_body f2_body"
                  using alpha_equiv_fctx_name[OF Hfctx Fname] Some_get_ctx1 Some_get_ctx2 Inl1 Inl2 Decl1 Decl2
                  by(auto)

                hence Bodies' : "alpha_equiv_stmt fsubst [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))] ctx1 ctx2 f1_body f2_body"
                  using to_oalist_impl_of[of "impl_of fsubst" fsubst]
                  by(auto)

                have Body_results :
                  "alpha_equiv_results [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))]
                    (eval_statement n' ctx1 f1_body (varmap_inserts (varmap_extend [Oalist.empty] f1_rets) (zip f1_args res2)) g)
                    (eval_statement n' ctx2 f2_body (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2)) g)"
                  using IH1[OF Vm_eq_pre_call Hfctx Bodies']
                  by auto

                show ?thesis
                proof(cases "eval_statement n' ctx1 f1_body (varmap_inserts (varmap_extend [Oalist.empty] f1_rets) (zip f1_args res2)) g")
                  case None_eval_body1 : None

                  show ?thesis
                  proof(cases "(eval_statement n' ctx2 f2_body (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2)) g)")
                    case None_eval_body2 : None
                    then show ?thesis 
                      using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 None_eval_body1 Args_len_eq
                      by(auto)
                  next
                    case Some_eval_body2 : (Some bres2)
                    then show ?thesis 
                      using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 None_eval_body1 Args_len_eq
                      using Body_results
                      by(auto)
                  qed
                next
                  case Some_eval_body1 : (Some bres1)

                  show ?thesis
                  proof(cases bres1)
                    case Ok_eval_body1 : (Ok bres1')

                    obtain vmfinal1 gfinal1 where Bres1' : "bres1' = (vmfinal1, gfinal1)"
                      by(cases bres1'; auto)

                    show ?thesis
                    proof(cases "(eval_statement n' ctx2 f2_body (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2)) g)")
                      case None_eval_body2 : None
                      then show ?thesis
                        using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Args_len_eq
                        using Body_results
                        by(auto)
                    next
                      case Some_eval_body2 : (Some bres2)
    
                      show ?thesis
                      proof(cases bres2)
                        case Ok_eval_body2 : (Ok bres2')
    
                        obtain vmfinal2 gfinal2 where Bres2' : "bres2' = (vmfinal2, gfinal2)"
                          by(cases bres2'; auto)

                        have Vm_eq_post_call : 
                          "alpha_equiv_varmap [to_oalist (zip f1_args f2_args @ zip f1_rets f2_rets)] vmfinal1
                               vmfinal2"
                          using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2  Ok_eval_body2 Bres2'
                          using Body_results Args_len_eq
                          by(auto)

                        have Rets_names : "list_all2 (alpha_equiv_name [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))]) f1_rets f2_rets"
                        proof(rule list_all2_all_nthI)
                          show "length f1_rets = length f2_rets"
                            using Rets_len_eq
                            by auto
                        next
                          fix n
                          assume N : "n < length f1_rets"

                          have Dist1 : "distinct (map fst (zip f1_args f2_args @ zip f1_rets f2_rets))"
                            using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2  Ok_eval_body2 Bres2'
                            using alpha_equiv_fctx_name[OF Hfctx Fname]
                            by(auto)

                          have Dist2 : "distinct (map fst (zip f2_args f1_args @ zip f2_rets f1_rets))"
                            using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2  Ok_eval_body2 Bres2'
                            using alpha_equiv_fctx_name[OF Hfctx Fname]
                            by(auto)

                          have Get1 : "get (to_oalist (zip f1_args f2_args @ zip f1_rets f2_rets)) (f1_rets ! n) = map_of (zip f1_args f2_args @ zip f1_rets f2_rets) (f1_rets ! n)"
                            using get_to_oalist[OF Dist1]
                            by auto

                          have Get1' : "map_of (zip f1_args f2_args @ zip f1_rets f2_rets) (f1_rets ! n) = Some (f2_rets ! n)"
                            using Args_len_eq Rets_len_eq Dist1
                            (* via sledgehammer *)
                            by (auto; smt (z3) N dom_map_of_zip map_add_comm map_add_find_right map_of_zip_nth)

                          have Flip : "(oalist_flip (to_oalist (zip f1_args f2_args @ zip f1_rets f2_rets))) =
                            to_oalist (zip f2_args f1_args @ zip f2_rets f1_rets)"
                            using to_oalist_flip_zip[OF Args_rets_dist1 Args_rets_dist2] Args_len_eq Rets_len_eq
                            by(auto)

                          have Get2 : "get (oalist_flip (to_oalist (zip f1_args f2_args @ zip f1_rets f2_rets))) (f2_rets ! n) = 
                                       map_of (zip f2_args f1_args @ zip f2_rets f1_rets) (f2_rets ! n)"
                            using Flip get_to_oalist[OF Dist2]
                            by(auto)

                          have Get2' : "map_of (zip f2_args f1_args @ zip f2_rets f1_rets) (f2_rets ! n) = Some (f1_rets ! n)"
                            using Args_len_eq Rets_len_eq Dist2
                            (* via sledgehammer *)
                            by (auto; smt (z3) N dom_map_of_zip map_add_comm map_add_find_right map_of_zip_nth)

                          show "alpha_equiv_name
                            [to_oalist (zip (f1_args @ f1_rets) (f2_args @ f2_rets))]
                            (f1_rets ! n) (f2_rets ! n)"
                            using alpha_equiv_fctx_name[OF Hfctx Fname] Some_get_ctx1 Some_get_ctx2 Inl1 Inl2 Decl1 Decl2
                            using Get1 Get1' Get2 Get2'
                            by(auto)
                        qed

                        show ?thesis
                        proof(cases "varmap_gets vmfinal1 f1_rets")
                          case None_returns1 : None
                          then show ?thesis 
                            using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2  Ok_eval_body2 Bres2'
                            using Body_results Args_len_eq
                            using alpha_equiv_varmap_gets_names[OF Vm_eq_post_call, of f1_rets f2_rets ] Rets_names
                            by(auto)

                        next
                          case Some_returns1 : (Some retvals1)
                          show ?thesis
                          proof(cases "varmap_gets vmfinal2 f2_rets")
                            case None_returns2 : None

                            then show ?thesis
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2  Ok_eval_body2 Bres2'
                              using Body_results Args_len_eq
                              using alpha_equiv_varmap_gets_names[OF Vm_eq_post_call, of f1_rets f2_rets ] Rets_names
                              by(auto)

                          next
                            case Some_returns2 : (Some retvals2)

                            have Fname : "alpha_equiv_name' fsubst f1 f2"
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                                Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2 Ok_eval_body2 Bres2' Some_returns1 Some_returns2
                              by(auto)

                            have Rets_len_eq1 : "length retvals1 = length f1_rets"
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                              Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2 Ok_eval_body2 Bres2' Some_returns1 Some_returns2
                              using varmap_gets_length
                              by(auto)

                            have Rets_len_eq2 : "length retvals2 = length f2_rets"
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                              Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2 Ok_eval_body2 Bres2' Some_returns1 Some_returns2
                              using varmap_gets_length

                              by(auto)

                            have Retvals_eq : "retvals1 = retvals2"
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                                Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2 Ok_eval_body2 Bres2' Some_returns1 Some_returns2
                              using Body_results Args_len_eq
                              using alpha_equiv_varmap_gets_names[OF Vm_eq_post_call , of f1_rets f2_rets] Rets_names
                              by(auto)

                            show ?thesis
                              using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                                Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2 Ok_eval_body2 Bres2' Some_returns1 Some_returns2
                              using Body_results Args_len_eq Rets_len_eq1 Rets_len_eq2 Retvals_eq
                              by(auto)
                          qed
                        qed
                      next
                        case Error_eval_body2 : (Error err2)

                        then show ?thesis
                          using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2
                            Some_eval_body1 Ok_eval_body1 Bres1' Some_eval_body2
                          using Body_results
                          by(auto)
                      qed
                    qed
                  next
                    case Error_eval_body1 : (Error err1)

                    show ?thesis
                    proof(cases "(eval_statement n' ctx2 f2_body (varmap_inserts (varmap_extend [Oalist.empty] f2_rets) (zip f2_args res2)) g)")
                      case None_eval_body2 : None
                      then show ?thesis
                        using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Args_len_eq
                        using Body_results
                        by(auto)
                    next
                      case Some_eval_body2 : (Some bres2)
    
                      show ?thesis
                      proof(cases bres2)
                        case Ok_eval_body2 : (Ok bres2')
    
                        obtain vmfinal2 gfinal2 where Bres2' : "bres2' = (vmfinal2, gfinal2)"
                          by(cases bres2'; auto)

                        show ?thesis
                          using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Args_len_eq
                          using Error_eval_body1 Some_eval_body2 Ok_eval_body2
                          using Body_results
                          by(auto)
                      next
                        case Error_eval_body2 : (Error err2)

                        show ?thesis
                          using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inl2 Decl2 Some_eval_body1 Args_len_eq
                          using Error_eval_body1 Some_eval_body2 Error_eval_body2
                          using Body_results
                          by(auto)
                      qed
                    qed
                  qed
                qed
              next
                case Inr2 : (Inr err2)

                show ?thesis
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                  using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inl1 Decl1 Inr2
                  by(auto)
              qed
            next
              case Inr1 : (Inr err1)
              show ?thesis
              proof(cases fres2)
                case Inl2 : (Inl decl2)
                show ?thesis
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                  using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inr1 Inl2
                  by(auto)
              next
                case Inr2 : (Inr err2)
                show ?thesis
                  using alpha_equiv_fctx_name[OF Hfctx Fname]
                  using EFun1 EFun2 Args Some1 Some2 Heqv Some_get_ctx1 Some_get_ctx2 Inr1 Inr2
                  by(auto)
              qed
            qed
          qed
        qed
      qed
    qed
  qed

  have Conc3 : 
" \<And> subst fsubst vm1 vm2 (ctx1 :: 'g fctx) (ctx2 :: 'g fctx) stms1 stms2 g.
     alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
     alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
       list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2) stms1 stms2 \<Longrightarrow>
       alpha_equiv_results subst (eval_statements (Suc n') ctx1 stms1 vm1 g) (eval_statements (Suc n') ctx2 stms2 vm2 g)"
  proof-
    fix subst fsubst vm1 vm2
    fix ctx1 :: "'g fctx"
    fix ctx2 stms1 stms2 g

    assume Hvm : "alpha_equiv_varmap subst vm1 vm2"
    assume Hfctx : "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
    assume Heqv : "list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2) stms1 stms2 "

    show "alpha_equiv_results subst (eval_statements (Suc n') ctx1 stms1 vm1 g)
        (eval_statements (Suc n') ctx2 stms2 vm2 g)"
    proof(cases stms1)
      case Nil
      then show ?thesis using Heqv Hvm
        by(cases stms2; auto)
    next
      case Cons1 : (Cons stm1h stm1t)

      obtain stm2h stm2t where Cons2 : "stms2 = stm2h # stm2t"
        using Cons1 Heqv
        by(cases stms2; auto)

      have Eqv_hd : "alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1h stm2h"
        using Cons1 Cons2 Heqv
        by(auto)

      have Eqv_tl : "list_all2 (alpha_equiv_stmt fsubst subst ctx1 ctx2) stm1t stm2t"
        using Cons1 Cons2 Heqv
        by(auto)

      have Eval_hd : "alpha_equiv_results subst (eval_statement n' ctx1 stm1h vm1 g) (eval_statement n' ctx2 stm2h vm2 g)"
        using IH1[OF Hvm Hfctx Eqv_hd, of g]
        by auto

      show ?thesis
      proof(cases "eval_statement n' ctx1 stm1h vm1 g")
        case None1h : None

        have None2h : "eval_statement n' ctx2 stm2h vm2 g = None"
          using None1h Eval_hd
          by(cases "eval_statement n' ctx2 stm2h vm2 g"; auto)

        show ?thesis using None1h None2h Cons1 Cons2
          by(auto)
      next
        case Some1h : (Some res1h)

        obtain res2h where Some2h : "eval_statement n' ctx2 stm2h vm2 g = Some res2h"
          using Some1h Eval_hd
          by(cases "eval_statement n' ctx2 stm2h vm2 g"; auto)

        show ?thesis
        proof(cases res1h)
          case Ok1h : (Ok res1h_p)

          obtain res1h_vm res1h_g where Res1h :
            "res1h_p = (res1h_vm, res1h_g)"
            by(cases res1h_p; auto)

          obtain res2h_p where Ok2h : "res2h = Ok res2h_p"
            using Some1h Some2h Ok1h Eval_hd
            by(cases res2h; auto)

          obtain res2h_vm res2h_g where Res2h :
            "res2h_p = (res2h_vm, res2h_g)"
            by(cases res2h_p; auto)

          have Vmh_eqv : "alpha_equiv_varmap subst res1h_vm res2h_vm"
            using Cons1 Cons2 Eval_hd Some1h Some2h Ok1h Res1h Ok2h Res2h
            by(auto)

          show ?thesis
            using Cons1 Cons2 Eval_hd Some1h Some2h Ok1h Res1h Ok2h Res2h
            using IH3[OF Vmh_eqv Hfctx Eqv_tl]
            by(auto)
        next
          case Error1h : (Error err1)

          obtain err2 where Error2h : "res2h = Error err2"
            using Some1h Some2h Error1h Eval_hd
            by(cases res2h; auto)

          show ?thesis using Cons1 Cons2 Some1h Some2h Error1h Error2h Eval_hd
            by(auto)
        qed
      qed
    qed
  qed

  show ?case
    using Conc1 Conc2 Conc3
    by(auto)
qed


lemma alpha_equiv_eval_correct_test :
  shows "(\<forall> subst fsubst vm1 vm2 ctx1 ctx2 stm1 stm2 .
          alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
          alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
          alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
          (\<forall> g .
             eval_statement n ctx1 stm1 vm1 g =
             eval_statement n ctx2 stm2 vm2 g) \<and>
          (\<forall> x1 expr1 x2 expr2 g .
             stm1 = SAssn x1 expr1 \<longrightarrow>
             stm2 = SAssn x2 expr2 \<longrightarrow>
             alpha_equiv_expr fsubst subst expr1 expr2 \<longrightarrow>
             eval_expression n ctx1 expr1 vm1 g =
             eval_expression n ctx2 expr2 vm2 g) 
         )\<and>
         (\<forall> subst fsubst vm1 vm2 ctx1 ctx2 stm1 stm2 x1 x2 stms1 stms2 g .
            alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
            alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
            alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
            stm1 = SBlock x1 stms1 \<longrightarrow>
            stm2 = SBlock x2 stms2 \<longrightarrow>
            eval_statements n ctx1 stms1 vm1 g =
            eval_statements n ctx2 stms2 vm2 g
         )"

proof(induction n)
  case 0
  then show ?case 
    by(auto)
next
  case (Suc n')

  have Hyp' :
    "(\<And> subst fsubst vm1 vm2 ctx1 ctx2 stm1 stm2.
      alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
      alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
      alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
      (\<forall>g. eval_statement n' ctx1 stm1 vm1 g = eval_statement n' ctx2 stm2 vm2 g) \<and>
      (\<forall>x1 expr1 x2 expr2 g.
          stm1 = SAssn x1 expr1 \<longrightarrow>
          stm2 = SAssn x2 expr2 \<longrightarrow>
          alpha_equiv_expr fsubst subst expr1 expr2 \<longrightarrow>
          eval_expression n' ctx1 expr1 vm1 g =
          eval_expression n' ctx2 expr2 vm2 g))"
  "(\<forall>subst fsubst vm1 vm2 ctx1 ctx2 stm1 stm2 x1 x2 stms1 stms2 g.
      alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
      alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
      alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
      stm1 = SBlock x1 stms1 \<longrightarrow>
      stm2 = SBlock x2 stms2 \<longrightarrow>
      eval_statements n' ctx1 stms1 vm1 g = eval_statements n' ctx2 stms2 vm2 g)"

  have Conc' : 

  show ?case
  proof(cases stm1)

  then show ?case
    apply(auto)
qed

lemma alpha_equiv_eval_correct :
  shows "(\<forall> subst fsubst vm1 vm2 ctx1 ctx2 stm2 .
          alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
          alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
          alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
          (\<forall> g n .
             eval_statement n ctx1 stm1 vm1 g =
             eval_statement n ctx2 stm2 vm2 g) \<and>
          (\<forall> x1 expr1 x2 expr2 g n .
             stm1 = SAssn x1 expr1 \<longrightarrow>
             stm2 = SAssn x2 expr2 \<longrightarrow>
             alpha_equiv_expr fsubst subst expr1 expr2 \<longrightarrow>
             eval_expression n ctx1 expr1 vm1 g =
             eval_expression n ctx2 expr2 vm2 g) 
         )\<and>
         (\<forall> subst fsubst vm1 vm2 ctx1 ctx2 stm1 stm2 x1 x2 stms2 g n .
            alpha_equiv_varmap subst vm1 vm2 \<longrightarrow>
            alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<longrightarrow>
            alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2 \<longrightarrow>
            stm1 = SBlock x1 stms1 \<longrightarrow>
            stm2 = SBlock x2 stms2 \<longrightarrow>
            eval_statements n ctx1 stms1 vm1 g =
            eval_statements n ctx2 stms2 vm2 g
         )"
proof(induction  rule: statement_induct_strong)
  case SBlock1 : (1 x1 x2)
  show ?case 
    apply(auto)
    sorry
next
  case SAssn1 : (2 x1 x2)

  have Conc'1 :
    "\<And>subst fsubst vm1 vm2 ctx1 ctx2 stm2 g n.
          alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
          alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
          alpha_equiv_stmt fsubst subst ctx1 ctx2 (SAssn x1 x2) stm2 \<Longrightarrow>
          eval_statement n ctx1 (SAssn x1 x2) vm1 g =
          eval_statement n ctx2 stm2 vm2 g"
  proof-
    fix subst fsubst vm1 vm2 ctx1 ctx2 stm2 g n
    assume Hmap : "alpha_equiv_varmap subst vm1 vm2"
    assume Hfctx : "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
    assume Hstmt : "alpha_equiv_stmt fsubst subst ctx1 ctx2 (SAssn x1 x2) stm2"

    obtain y1 y2 where SAssn2 : "stm2 = SAssn y1 y2"
      using Hstmt
      by(cases stm2; auto)

    show "eval_statement n ctx1 (SAssn x1 x2) vm1 g = eval_statement n ctx2 stm2 vm2 g"
    proof(cases n)
      case 0
      then show ?thesis by auto
    next
      case (Suc n')

      show ?thesis
      proof(cases "eval_expression n' ctx1 x2 vm1 g")
        case None1 : None
        show ?thesis
        proof(cases "eval_expression n' ctx2 y2 vm2 g")
          case None2 : None
          show ?thesis
            using Hmap Hfctx Hstmt SAssn2 Suc None1 None2
            by(auto)
        next
          case Some2 : (Some res2)
          show ?thesis
            using Hmap Hfctx Hstmt SAssn2 Suc None1 Some2
            apply(auto)

        next
          case (Some a)
          then show ?thesis sorry
        qed
        then show ?thesis sorry
      next
        case (Some a)
        then show ?thesis sorry
      qed

      then show ?thesis
        using Hmap Hfctx Hstmt SAssn2
        apply(auto)
    qed
      using Hmap Hfctx Hstmt SAssn2
      apply(cases n; auto split: option.splits if_splits orerror.splits)

      sorry
  qed

  have Conc'2 :
    "\<And>subst fsubst vm1 vm2 ctx1 ctx2 stm2 x1a expr1 x2a expr2 g n.
          alpha_equiv_varmap subst vm1 vm2 \<Longrightarrow>
          alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2 \<Longrightarrow>
          alpha_equiv_stmt fsubst subst ctx1 ctx2 (SAssn x1 x2) stm2 \<Longrightarrow>
          SAssn x1 x2 = SAssn x1a expr1 \<Longrightarrow>
          stm2 = SAssn x2a expr2 \<Longrightarrow>
          eval_expression n ctx1 expr1 vm1 g = eval_expression n ctx2 expr2 vm2 g"
    sorry

  show ?case
    using Conc'1 Conc'2 
    by(metis)
next
  case SIf1 : (3 x1 x2 x3)
  then show ?case sorry
next
  case SWhile1 : (4 x1 x2)
  then show ?case sorry
next
  case SSkip1 : 5
  then show ?case 
    apply(auto)
next
  case SNil : 6
  then show ?case sorry
next
  case SCons : (7 h t)
  then show ?case sorry
qed

lemma alpha_equiv_eval_correct :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "alpha_equiv_fctx (impl_of fsubst) ctx1 ctx2"
  assumes "alpha_equiv_stmt fsubst subst ctx1 ctx2 stm1 stm2"
  shows "eval_statement n ctx1 stm1 vm1 g =
         eval_statement n ctx2 stm2 vm2 g"
  using assms
proof(induction stm1 arbitrary: subst vm1 vm2 fsubst ctx1 ctx2 stm2 n g)
  case SB1 : (SBlock names1 body1)

  obtain names2 body2 where SB2 : "stm2 = SBlock names2 body2"
    using SB1.prems
    by(cases stm2; auto)

  show ?case
  proof(cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc n')

    show ?thesis using SB1 SB2 Suc
      sorry
  qed
next
  case SA1 : (SAssn names1 expr1)
  obtain names2 expr2 where SA2 : "stm2 = SAssn names2 expr2"
    using SA1.prems
    by(cases stm2; auto)

  show ?case
  proof(cases n)
    case 0
    then show ?thesis by auto
  next
    case (Suc n')

    show ?thesis using SA1 SA2 Suc
      sorry
  qed
next
  case SI1 : (SIf x1 stm11 stm12)
  then show ?case sorry
next
  case SW1 : (SWhile x1 stm1)
  then show ?case sorry
next
  case SS1 : SSkip

  have SS2 : "stm2 = SSkip"
    using SS1
    by(cases stm2; auto)

  show ?case using SS1 SS2
    apply(cases n; auto)

  then show ?case sorry
qed

(*
lemma alpha_equiv_eval_correct_full :
  assumes "alpha_equiv_varmap subst vm1 vm2"
  assumes "alpha_equiv_fctx fsubst ctx1 ctx2"
  assumes "alpha_equiv_stmt fsubst subst stm1 stm2"
  shows
    "(\<forall> n .
     eval_statement n ctx1 stm1 vm1 g =
     eval_statement n ctx2 stm2 vm2 g) \<and>
     (\<forall> n decls1 body1 decls2 body2.
      stm1 = SBlock decls1 body1 \<Longrightarrow>
      stm2 = SBlock decls2 body2 \<Longrightarrow>
      eval_statements n ctx1 body1 (varmap_extend (varmap_push vm1) decls1) =
      eval_statements n ctx2 body2 (varmap_extend (varmap_push vm2) decls2)) \<and>
     (\<forall> n names1 expr1 names2 expr2 .
      stm1 = SAssn ns1 expr1 \<Longrightarrow>
      stm2 = SAssn ns2 expr2 \<Longrightarrow>
      eval_statement n ctx1 stm1 vm1 g =
      eval_statement n ctx2 stm2 vm2 g)"
  assumes "alpha_equiv_expr fsubst subst e1 e2"
  shows "eval_expr vm1 e1 = eval_expr vm2 e2"
  using assms
*)

(*
 *
*)

(*
lemma alpha_equiv_eval :
  assumes "alpha_equiv_fctx fnames ctx1 ctx2"
  assumes "alpha_equiv_varmap vsubst vars1 vars2"
  assumes "fsubst = to_oalist fnames"
  shows "alpha_equiv_stmt fsubst vsubst ctx1 ctx2 stm1 stm2 \<Longrightarrow>
         eval_statement n ctx1 stm1 vars1 g =
         eval_statement n ctx2 stm2 vars2 g"
and "list_all2 (alpha_equiv_stmt fsubst vsubst ctx1 ctx2) stms1 stms2 \<Longrightarrow>
    eval_statements n ctx1 stms1 vars1 g =
    eval_statements n ctx2 stms2 vars2 g"
and "alpha_equiv_expr fsubst vsubst e1 e2 \<Longrightarrow>
    eval_expression n ctx1 e1 vars1 g =
    eval_expression n ctx2 e2 vars2 g"
  using assms
proof(rule
eval_statement_eval_statements_eval_expression.induct)
case (1 uu uv uw ux)
then show ?case sorry
next
  case (2 n ctx decls stms vars g)
  then show ?case sorry
next
  case (3 n ctx ns expr vars g)
  then show ?case sorry
next
  case (4 n ctx expr1 stm_t stm_f vars g)
  then show ?case sorry
next
  case (5 n ctx expr1 stm_body vars g)
  then show ?case sorry
next
  case (6 n ctx vars g)
  then show ?case sorry
next
  case (7 ctx uy vars g)
  then show ?case sorry
next
  case (8 n ctx vars g)
  then show ?case sorry
next
  case (9 n ctx stm_h stm_t vars g)
  then show ?case sorry
next
  case (10 ctx uz vars g)
  then show ?case sorry
next
  case (11 n ctx e1s vars g)
  then show ?case sorry
next
  case (12 n ctx p args vars g)
  then show ?case sorry
next
  case (13 n ctx f args vars g)
  then show ?case sorry
qed
*)

(* the goal. *)
(* assumptions:
 * primitives do not inspect variable map (proper)
 * manually supplied function mapping is valid.
 * how exactly do we specify this?
 *)

(*
lemma alpha_equiv_eval_program :
  assumes "prog1 = Prog ctx1 body1"
  assumes "prog2 = Prog ctx2 body2"
  assumes "ctx_proper ctx1"
  assumes "ctx_proper ctx2"
  assumes "alpha_equiv_program prog1 prog2"
  shows
    "eval_program n prog1 g =
     eval_program n prog2 g"
*)

end