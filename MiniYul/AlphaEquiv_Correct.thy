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

(* alternative version of varmap_extend that leads to cleaner
 * inductive proof *)
(*
fun varmap_extend_alt :: "varmap \<Rightarrow> name list \<Rightarrow> varmap" where
"varmap_extend_alt vm [] = vm"
| "varmap_extend_alt vm (nh # nt) =
   varmap_insert (varmap_extend vm nt) nh 0"

lemma varmap_extend_alt_spec : 
  assumes "distinct ns"
  shows "varmap_extend vm ns = varmap_extend_alt vm ns"
  using assms
proof(induction ns arbitrary: vm)
  case Nil
  then show ?case by auto
next
  case (Cons nh nt)
  show ?case using Cons.prems
    apply(auto)
    using sym[OF Cons.IH[of "varmap_insert vm nh 0"]] Cons.IH[of vm]
    apply(auto)

qed
*)

(*
lemma alpha_equiv_varmap'_update_fresh_present :
  assumes "alpha_equiv_varmap' subst' vm1' vm2'"
  assumes "oalist_one_one subst'"
  assumes "oalist_keys subst' = oalist_keys vm1'"
  assumes "oalist_keys (oalist_flip subst') = oalist_keys vm2'"
  assumes "n1 \<in> set (oalist_keys vm1')"
  assumes "n2 \<in> set (oalist_keys vm2')"  
  shows "alpha_equiv_varmap' (update n1 n2 subst') vm1' vm2'"
  using assms
proof(transfer)
  fix subst'
  show "\<And> vm1' vm2' n1 n2. strict_order (map fst subst') \<Longrightarrow>
       strict_order (map fst vm1') \<Longrightarrow>
       strict_order (map fst vm2') \<Longrightarrow>
       alpha_equiv_varmap'l subst' vm1' vm2' \<Longrightarrow>
       distinct (map snd subst') \<Longrightarrow>
       map fst subst' = map fst vm1' \<Longrightarrow>
       map fst (oalist_flip' subst') = map fst vm2' \<Longrightarrow> n1 \<in> set (map fst vm1') \<Longrightarrow> n2 \<in> set (map fst vm2') \<Longrightarrow> alpha_equiv_varmap'l (str_ord_update n1 n2 subst') vm1' vm2'"
  proof(induction subst')
    case Nil
    then show ?case
      by(auto)
  next
    case (Cons subst'h subst't)

    obtain hn1 hn2 where Subst'h :
      "subst'h = (hn1, hn2)"
      by(cases subst'h; auto)

    obtain val where Val :
      "map_of vm1' hn1 = Some val" "map_of vm2' hn2 = Some val"
      "alpha_equiv_varmap'l subst't vm1' vm2'"
      using Cons.prems Subst'h
      by(auto split: option.splits)

    obtain val1 where Val1 : "(n1, val1) \<in> set vm1'"
      using Cons.prems
      by(auto)

    then have Val1' : "map_of vm1' n1 = Some val1"
      using Some_eq_map_of_iff[of vm1'] strict_order_distinct[OF Cons.prems(2)]
      by auto

    obtain val2 where Val2 : "(n2, val2) \<in> set vm2'"
      using Cons.prems
      by(auto)

    then have Val2' : "map_of vm2' n2 = Some val2"
      using Some_eq_map_of_iff[of vm2'] strict_order_distinct[OF Cons.prems(3)]
      by(auto)

    show ?case
    proof(cases "n1 = hn1")
      case True1 : True


      show ?thesis using Cons.prems Subst'h
          True1 Val Val2'
        apply(auto)
    next
      case False1 : False
      show ?thesis
      proof(cases "n2 = hn2")
        case True2 : True

      using Cons.prems Subst'h Val Val1' Val2'
      apply(auto)

  qed
*)
lemma alpha_equiv_varmap'_update_fresh :
  assumes "alpha_equiv_varmap' subst' vm1' vm2'"
  assumes "oalist_one_one subst'"
  assumes "oalist_keys subst' = oalist_keys vm1'"
  assumes "oalist_keys (oalist_flip subst') = oalist_keys vm2'"
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
       map fst subst' = map fst vm1' \<Longrightarrow>
       map fst (oalist_flip' subst') = map fst vm2' \<Longrightarrow>
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

      show ?thesis using Cons.prems Subst'h
          Get1_hn1 Get2_n2 True1 Val Ord_tl Val
        using alpha_equiv_varmap'_update_miss[of vm1' vm2' subst't n1] Notin1
        apply(auto)
    next
      case False1 : False
      show ?thesis
      proof(cases "n2 = hn2")
        case True2 : True

        have Notin2: "hn2 \<notin> fst ` set vm2'"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 False1 True2 Val Ord_tl Val
          by(auto)

        have Vm2 : "map fst (str_ord_update hn2 hn1 (oalist_flip' subst't)) = map fst vm2'"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 Val Ord_tl Val
          by(auto)

        have Vm2' : "fst ` set (str_ord_update hn2 hn1 (oalist_flip' subst't)) = fst ` set vm2'"
          unfolding sym[OF set_map]
          using Vm2
          by(auto)

        have Vm2'_set : "set (str_ord_update hn2 hn1 (oalist_flip' subst't)) =
          set (oalist_flip' subst't) - { x . fst x = hn2 } \<union> {(hn2, hn1)}"
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
          by auto

        have Bad : "(hn2) \<in>  fst ` set vm2'"
          using Vm2'_set unfolding sym[OF Vm2']
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

          have Keys1_alt : "fst ` set (subst'h # subst't) = fst ` set vm1'"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin1_alt : "n1 \<notin> fst ` set (subst'h # subst't)"
            using Notin1
            unfolding Keys1_alt
            by(auto)

          have Notin1_alt_tl : "n1 \<notin> fst ` set (subst't)"
            using Notin1_alt
            by auto

          have Notin2 : "n2 \<notin> fst ` set vm2'"
            using Cons.prems Subst'h False1
            by(auto)

          have Keys2_alt : "fst ` set ((oalist_flip' (subst'h # subst't))) = fst ` (set vm2')"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin2_alt : "n2 \<notin> fst ` set ((oalist_flip' (subst'h # subst't))) "
            using Notin2
            unfolding Keys2_alt
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

          show ?thesis using Cons.prems Subst'h False1 False2 True3
              Get1_hn1 Get2_n2 False1 False2 Val Get2_miss
            using alpha_equiv_varmap'_update_miss[OF Cons.prems(2) Cons.prems(3) Ord_tl _ Notin1_alt_tl Notin2_alt_tl]
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

          obtain vm1'hk vm1'hv vm1't where Vm1'_cons : "vm1' = (vm1'hk, vm1'hv) # vm1't"
            using Cons.prems
            by(cases vm1'; auto)

          have Vm_tl' : "alpha_equiv_varmap'l subst't ((vm1'hk, val) # vm1't) vm2'"
            using Cons.prems Subst'h False1 False2 False3
              Get1_hn1 Get2_n2 Get2_miss Val Lt Vm1'_cons
            by(auto)

          show ?thesis using Cons.prems Subst'h False1 False2 False3
              Get1_hn1 Get2_n2 Get2_miss Val Lt Vm1'_cons
            apply(auto)
        qed

        show ?thesis using Cons.prems Subst'h
            Get1_hn1 Get2_n2 False1 False2 Val Get2_miss
          apply(auto)
          sorry
      qed
    qed
  qed
qed


lemma alpha_equiv_varmap'_update_fresh :
  assumes "alpha_equiv_varmap' subst' vm1' vm2'"
  assumes "oalist_one_one subst'"
  assumes "oalist_keys subst' = oalist_keys vm1'"
  assumes "oalist_keys (oalist_flip subst') = oalist_keys vm2'"
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
       map fst subst' = map fst vm1' \<Longrightarrow>
       map fst (oalist_flip' subst') = map fst vm2' \<Longrightarrow>
       n1 \<notin> set (map fst vm1') \<Longrightarrow>
       n2 \<notin> set (map fst vm2') \<Longrightarrow>
       alpha_equiv_varmap'l (str_ord_update n1 n2 subst')
        (str_ord_update n1 v vm1') (str_ord_update n2 v vm2')"
  proof(induction subst')
    case Nil
    then show ?case 
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

      show ?thesis using Cons.prems Subst'h
          Get1_hn1 Get2_n2 True1 Val Ord_tl Val
        by(auto)
    next
      case False1 : False
      show ?thesis
      proof(cases "n2 = hn2")
        case True2 : True

        have Notin2: "hn2 \<notin> fst ` set vm2'"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 False1 True2 Val Ord_tl Val
          by(auto)

        have Vm2 : "map fst (str_ord_update hn2 hn1 (oalist_flip' subst't)) = map fst vm2'"
          using Cons.prems Subst'h
            Get1_hn1 Get2_n2 Val Ord_tl Val
          by(auto)

        have Vm2' : "fst ` set (str_ord_update hn2 hn1 (oalist_flip' subst't)) = fst ` set vm2'"
          unfolding sym[OF set_map]
          using Vm2
          by(auto)

        have Vm2'_set : "set (str_ord_update hn2 hn1 (oalist_flip' subst't)) =
          set (oalist_flip' subst't) - { x . fst x = hn2 } \<union> {(hn2, hn1)}"
          using str_ord_update_set[OF oalist_flip'_correct[OF Ord_tl]]
          by auto

        have Bad : "(hn2) \<in>  fst ` set vm2'"
          using Vm2'_set unfolding sym[OF Vm2']
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

          have Keys1_alt : "fst ` set (subst'h # subst't) = fst ` set vm1'"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin1_alt : "n1 \<notin> fst ` set (subst'h # subst't)"
            using Notin1
            unfolding Keys1_alt
            by(auto)

          have Notin1_alt_tl : "n1 \<notin> fst ` set (subst't)"
            using Notin1_alt
            by auto

          have Notin2 : "n2 \<notin> fst ` set vm2'"
            using Cons.prems Subst'h False1
            by(auto)

          have Keys2_alt : "fst ` set ((oalist_flip' (subst'h # subst't))) = fst ` (set vm2')"
            using Cons.prems
            unfolding sym[OF set_map]
            by auto

          have Notin2_alt : "n2 \<notin> fst ` set ((oalist_flip' (subst'h # subst't))) "
            using Notin2
            unfolding Keys2_alt
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

          show ?thesis using Cons.prems Subst'h False1 False2 True3
              Get1_hn1 Get2_n2 False1 False2 Val Get2_miss
            using alpha_equiv_varmap'_update_miss[OF Cons.prems(2) Cons.prems(3) Ord_tl _ Notin1_alt_tl Notin2_alt_tl]
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

          obtain vm1'hk vm1'hv vm1't where Vm1'_cons : "vm1' = (vm1'hk, vm1'hv) # vm1't"
            using Cons.prems
            by(cases vm1'; auto)

          have Vm_tl' : "alpha_equiv_varmap'l subst't ((vm1'hk, val) # vm1't) vm2'"
            using Cons.prems Subst'h False1 False2 False3
              Get1_hn1 Get2_n2 Get2_miss Val Lt Vm1'_cons
            by(auto)

          show ?thesis using Cons.prems Subst'h False1 False2 False3
              Get1_hn1 Get2_n2 Get2_miss Val Lt Vm1'_cons
              Cons.IH
            apply(auto)
        qed

        show ?thesis using Cons.prems Subst'h
            Get1_hn1 Get2_n2 False1 False2 Val Get2_miss
          apply(auto)
          sorry
      qed
    qed
  qed
qed


(* need assumptions about n1 and n2 not being present in substh? 
 * no, I think we need them to not be present in vm1h *)
lemma alpha_equiv_varmap_insert :
  assumes "alpha_equiv_varmap (substh # substt) vm1 vm2"
  shows "alpha_equiv_varmap (update n1 n2 substh # substt)
     (varmap_insert vm1 n1 v)
     (varmap_insert vm2 n2 v)"
  using assms
proof(induction substt arbitrary: substh vm1 vm2 n1 n2 v)
  case Nil
  then show ?case
    apply(cases vm1; cases vm2; auto)
    sorry
next
  case Cons_s : (Cons sh' st')

  obtain vm1h vm1t where Cons1 : "vm1 = vm1h # vm1t"
    using Cons_s.prems
    by(cases vm1; auto)

  obtain vm2h vm2t where Cons2 : "vm2 = vm2h # vm2t"
    using Cons_s.prems
    by(cases vm2; auto)

  show ?case
    using Cons_s.prems Cons1 Cons2
    using Cons_s.IH[of sh' vm1t vm2t]
    apply(auto)

  have Eq_h : "alpha_equiv_varmap' substh vm1 vm2"
    using Cons1.prems Cons2
    by auto

  have Conc1 : "alpha_equiv_varmap' (update n1 n2 substh) (update n1 v vm1h) (update n2 v vm2h)"
    using alpha_equiv_varmap'_update[of "update n1 n2 substh"] (* this won't work *)
    sorry

  have Conc2 : "oalist_keys (update n1 n2 substh) = oalist_keys (update n1 v vm1h)"
    sorry

  have Conc3 : "oalist_one_one (update n1 n2 substh)"
    sorry

  have Conc4 : "oalist_keys (oalist_flip (update n1 n2 substh)) = oalist_keys (update n2 v vm2h)"
    sorry

  show ?case
    using Cons1 Cons2 Conc1 Conc2 Conc3 Conc4
    by(auto)
qed

lemma alpha_equiv_varmap_insert_mini :
  assumes "length ns1 = length ns2"
  assumes "alpha_equiv_varmap (to_oalist (zip ns1 ns2) # subst)
     (varmap_extend (Oalist.empty # vm1) ns1)
     (varmap_extend (Oalist.empty # vm2) ns2)"
  shows "alpha_equiv_varmap (update n1 n2 (to_oalist (zip ns1 ns2)) # subst)
     (varmap_insert (varmap_extend (Oalist.empty # vm1) ns1) n1 0)
     (varmap_insert (varmap_extend (Oalist.empty # vm2) ns2) n2 0)"
  using assms
proof(induction ns1 arbitrary: subst vm1 vm2 n1 n2 ns2)
  case Nil
  then show ?case
    apply(auto)
    sorry
    
next
  case Cons1 : (Cons ns1h ns1t)

  obtain ns2h ns2t where Cons2 : "ns2 = ns2h # ns2t"
    using Cons1.prems
    by(cases ns2; auto)

(*
  have Eq_h : "alpha_equiv_varmap' substh vm1h vm2h"
    using Cons1.prems Cons2
    by auto

  have Conc1 : "alpha_equiv_varmap' (update n1 n2 substh) (update n1 v vm1h) (update n2 v vm2h)"
    using alpha_equiv_varmap'_update[of "update n1 n2 substh"] (* this won't work *)
    sorry

  have Conc2 : "oalist_keys (update n1 n2 substh) = oalist_keys (update n1 v vm1h)"
    sorry

  have Conc3 : "oalist_one_one (update n1 n2 substh)"
    sorry

  have Conc4 : "oalist_keys (oalist_flip (update n1 n2 substh)) = oalist_keys (update n2 v vm2h)"
    sorry
*)

  show ?case
    using Cons1 Cons2 
    apply(auto)
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

(* need an alternate version of alpha_equiv_varmap_update
 * dealing with values not present? *)
  show ?case using Vm_tl Cons1.prems Cons2 Vm_tl
    using varmap_extend_insert_swap[OF Notin1(1) Notin1(2)]
    using varmap_extend_insert_swap[OF Notin2(1) Notin2(2)]
    apply(auto simp del: varmap_insert.simps)
    sorry
(*
(* need an assumption about one-one ness of ns1 and ns2? *)
  show ?case
  proof(cases "get (to_oalist (zip ns1t ns2t)) ns1h")
    case None1 : None

    show ?thesis
    proof(cases "get (oalist_flip (to_oalist (zip ns1t ns2t))) ns2h")
      case None2 : None
      then show ?thesis 
        using Cons1.prems Cons2 None1
        using alpha_equiv_varmap_update[OF _ Vm_tl, of ns1h ns2h]
    apply(auto)
        apply(auto)

    next
      case (Some a)
      then show ?thesis sorry
    qed
      using None1 alpha_equiv_varmap_update[OF _ Vm_tl, of ns1h ns2h]
      apply(auto)


  show ?case using alpha_equiv_varmap_update[OF _ Vm_tl, of ns1h ns2h]
    apply(auto)

  then show ?case 
    apply(auto)
*)
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

          have Pop : "alpha_equiv_varmap subst (varmap_pop res1_vm) (varmap_pop res2_vm)"
            using SB1 SB2 Heqv Some1 Some2 Ok1 Ok2 Res1 Res2 Hvm
            apply(auto)
            sorry (* lemma *)

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
          using EFun1 EFun2 Args Some1 Some2 Heqv
          apply(auto)
          sorry
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