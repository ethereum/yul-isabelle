theory SparseArray
  imports "HOL-Data_Structures.Tries_Binary" "HOL.Parity"
  "HOL-Library.Adhoc_Overloading"
begin

(* typeclass for data we can convert to binary 
   for use with radix *)

class rx_key =
  fixes rx_serialize ::
    "'a \<Rightarrow> bool list"

  assumes serialize_distinct :
  "\<And> (x :: 'a) (x' :: 'a) . rx_serialize x = rx_serialize x' \<Longrightarrow> x = x'"
begin
end


value "divide_int_inst.divide_int (3 :: int)  2"

fun nat_to_bool_list :: "nat \<Rightarrow> bool list" where
"nat_to_bool_list i =
  (if i = 0 then []
   else 
    (if (i mod 2) = 0 then False else True) #
    nat_to_bool_list (i div 2))"

lemma nat_to_bool_list_distinct :
  assumes H : "nat_to_bool_list i = nat_to_bool_list i'"
  shows "i = i'" using assms
  sorry
(*
proof(induction i arbitrary: i' rule: Nat.nat_less_induct)
  case (1 n)
  show ?case
  proof(cases n)
    case 0
    then show ?thesis using "1.prems" by(cases i'; auto)
  next
    case (Suc nat)

    obtain i'p where I' : "i' = Suc i'p"
      using "1.prems" Suc by(cases i'; auto)

    show ?thesis 
    proof(cases "(n mod 2) = 0")
      case True : True
      then show ?thesis
      proof(cases "(i' mod 2) = 0")
        case True' : True

        have Next: "nat_to_bool_list (n div 2) =
              nat_to_bool_list (i' div 2)"
          using "1.prems" True True' Suc I'
          by(simp)

        have LeqN : "n div 2 < n" using Suc by auto

        have LeqI : "i' div 2 < i'" using I' by auto

        have Conc' : "n div 2 = i' div 2"
          using Next spec[OF "1.IH", of "n div 2"] LeqN LeqI 
          apply(clarify)
          apply(drule_tac x = "i' div 2" in spec)
          apply(clarify)
          done

        then show ?thesis using True True' "1.prems" Suc I'
          apply(simp)

      next
  case False
  then show ?thesis sorry
qed
        

      next
      case False
      then show ?thesis sorry
    qed
      
      using "1.prems"
  qed
    apply(cases n) apply(simp)
    apply(cases i') apply(simp) apply(simp)
qed
  case (stable a)
  have 0: "a = 0" using stable(1)
    by(cases a; auto)
  hence 1: "i' = 0" using stable(2)
    by(cases i'; auto)
  show ?case using 0 1 by auto
next
  case (rec a b)
  show ?case
  proof(cases a)
    case 0
    then show ?thesis sorry
  next
    case (Suc nat)
    then show ?thesis sorry
  qed

  proof(cases b)
    case True
    then show ?thesis using  "rec"(1) apply(simp)
  next
    case False
    then show ?thesis sorry
  qed

qed
  case (1 i)
  show ?case
  proof(cases "i < 0")
    case True
    then show ?thesis
    proof(cases "i' < 0")
      case True' : True
      then show ?thesis 
      proof(cases "(i mod 2) = 0")
        case True'' : True
        then show ?thesis using True True' True'' "1.prems" "1.IH"
          apply(auto)
      next
        case False
        then show ?thesis sorry
      qed
    next
      case False
      then show ?thesis sorry
    qed
  next
    case False
    then show ?thesis sorry
  qed
qed
  case (1 i)
  then show ?case 
qed
  sorry
*)

instantiation nat :: rx_key begin
definition nat_rx_serialize :
"rx_serialize i = nat_to_bool_list i"

instance proof
  fix x x' :: nat
  assume H: "rx_serialize x = rx_serialize x'"
  then show "x = x'"
    unfolding nat_rx_serialize
    using nat_to_bool_list_distinct [of x x']
    by(simp)
qed
    
end

fun rx_trie_put :: 

(*
 * pseudo typeclass for sparse arrays
 *)

consts sa_get ::
  "'t \<Rightarrow> 'k \<Rightarrow> 'v"

consts sa_put ::
  "'t \<Rightarrow> 'k \<Rightarrow> 'v \<Rightarrow> 't"


end