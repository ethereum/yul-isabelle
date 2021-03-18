theory Logic imports "../Yul/YulSemanticsSingleStep"
begin

definition YulSteps ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
  (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ % {_} {_}")
  where
"YulSteps D P Q =
  (\<forall> st . P st \<longrightarrow>
    (\<exists> n st' . evalYul' D st n = YulResult st' \<and>
     Q st'))"

lemma YSI [intro]:
  assumes
    "\<And> st . P st \<Longrightarrow> 
      (\<exists> n st' . evalYul' D st n = YulResult st' \<and>
     Q st')"
  shows "D % {P} {Q}" using assms
  unfolding YulSteps_def 
  by auto

lemma HTE [elim]:
  assumes H : "D%{P} {Q}"
  assumes HP : "P st"
  shows "(\<exists> n st'. evalYul' D st n = YulResult st' \<and>
     Q st')"
  using assms unfolding YulSteps_def by auto

(* Hoare logic rules *)
lemma HT_conseq :
  assumes H : "D%{P} {Q}"
  assumes HP : "\<And> st . P' st \<Longrightarrow> P st"
  assumes HQ : "\<And> st . Q st \<Longrightarrow> Q' st"
  shows "D%{P'} {Q'}"
proof
  fix st
  assume P' : "P' st"
  hence P : "P st" using HP by auto

  obtain n st' where Exec : "evalYul' D st n = YulResult st' \<and> 
           Q st'"
    using HTE[OF H P] by auto

  hence Q' : "Q' st'" using HQ Exec by auto

  thus "\<exists>n st'.
             evalYul' D st n = YulResult st' \<and> Q' st'"
    using Exec by blast
qed


lemma HT_step :
  assumes H : "\<And> st . P st \<Longrightarrow> 
      (\<exists> st' . evalYulStep D st = YulResult st' \<and> Q st')"
  shows "D%{P} {Q}"
proof
  fix st
  assume P : "P st"
  obtain st' where St' : "evalYulStep D st = YulResult st'"  and Q : "Q st'"
    using H[OF P] by auto

  hence "evalYul' D st 1 = YulResult st'" by auto

  thus "\<exists>n st' . evalYul' D st n = YulResult st' \<and>  Q st'" using St' Q by blast
qed

lemma evalYul'_steps :
  assumes H1 : "evalYul' D st1 n1 = YulResult st2"
  assumes H2 : "evalYul' D st2 n2 = st3"
  shows "evalYul' D st1 (n1 + n2) = st3" using assms
proof(induction n1 arbitrary: st1 st2 n2 st3)
  case 0
  then show ?case by auto
next
  case (Suc n1)
  show ?case
  proof(cases "cont st1")
    case Nil
    then show ?thesis using Suc by(auto)
  next
    case (Cons ch1 ct1)

    obtain st1' where "evalYulStep D st1 = YulResult st1'"
      using Suc.prems Cons by(auto simp del: evalYulStep.simps split:YulResult.splits)    

    then show ?thesis using Suc.prems Suc.IH Cons
      by(simp del: evalYulStep.simps)
  qed
qed

lemma HT_steps :
  assumes H1 : "D % {P1} {P2}"
  assumes H2 : "D % {P2} {P3}"
  shows "D % {P1} {P3}"
proof
  fix st1
  assume P1 : "P1 st1"
  obtain n1 st2 where Exec1 : "evalYul' D st1 n1 = YulResult st2" and P2 : "P2 st2"
    using HTE[OF H1 P1] by auto
  obtain n2 st3 where Exec2 : "evalYul' D st2 n2 = YulResult st3" and P3 : "P3 st3"
    using HTE[OF H2 P2] by auto

  have Exec : "evalYul' D st1 (n1 + n2) = YulResult st3"
    using evalYul'_steps[OF Exec1 Exec2] by auto

  thus "\<exists>n st'. evalYul' D st1 n = YulResult st' \<and> P3 st'" using P3 by blast
qed

(* characterize successfully halted states *)
definition is_halted :: "('g, 'v, 't) result \<Rightarrow> bool" where
"is_halted r = (cont r = [])"

(* a more familiar-looking Hoare logic of statements - but showing its relationship to the
   actual executions beyond the first instruction will take some work. *)
definition YulStepsStmt ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
   (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ % {_} _ {_}") where
"(D % {P} c {Q}) =
  ((D % {P} {Q}) \<and>
   (\<forall> st . P st \<longrightarrow> cont st = [EnterStatement c]))"


(* Revisiting the implementation - how can we make it easier to model behavior?
   1: formalize continuation stack transformation patterns. everything except for
break and continue will add a (possibly empty) prefix to the stack, and drop the current element.
*)

(* one idea: we could have a
delta function that precisely describes the
change to the continuation *)

lemma evalYulStep_cont_pref :
  assumes Hcont : "cont st = h#t"
  assumes Hstep : "evalYulStep D st = YulResult st'"
  shows "\<exists> pre . cont st' = pre @ t" 
proof(cases h)
  case (EnterStatement st)
  show ?thesis
  proof(cases st)
    case (YulFunctionCallStatement x)
    then show ?thesis using assms EnterStatement
      by(cases x; auto)
  next
    case (YulAssignmentStatement x)
    then show ?thesis using assms EnterStatement
      by(cases x; auto)
  next
    case (YulVariableDeclarationStatement x)
    show ?thesis
    proof(cases x)
      case (YulVariableDeclaration x1 x2)
      then show ?thesis using assms EnterStatement YulVariableDeclarationStatement 
        by(cases x2; auto)
    qed
  next
    case (YulFunctionDefinitionStatement x)
    then show ?thesis using assms EnterStatement YulFunctionDefinitionStatement
      by(auto)
  next
    case (YulIf x1 x2)
    then show ?thesis using assms EnterStatement by auto
  next
    case (YulSwitch x1 x2)
    then show ?thesis using assms EnterStatement by auto
  next
    case (YulForLoop pre cond post body)
    then show ?thesis using assms EnterStatement 
      by(cases pre; auto)
  next
  case YulBreak
  then show ?thesis using assms EnterStatement
    by(auto)
  next
    case YulContinue
    then show ?thesis using assms EnterStatement
      by auto
  next
    case YulLeave
    then show ?thesis using assms EnterStatement
      by auto
  next
    case (YulBlock x11)
    then show ?thesis using assms EnterStatement
      by(auto split: sum.splits)
  qed
next
  case (ExitStatement st locals sigs)
  show ?thesis
  proof(cases st)
    case (YulFunctionCallStatement x)
    then show ?thesis using assms ExitStatement
      by(cases x; auto split:list.splits)
  next
    case (YulAssignmentStatement x)
    then show ?thesis using assms ExitStatement
      by(cases x; auto split:list.splits if_splits option.splits)
  next
    case (YulVariableDeclarationStatement x)
    show ?thesis
    proof(cases x)
      case (YulVariableDeclaration x1 x2)
      then show ?thesis using assms ExitStatement YulVariableDeclarationStatement 
        by(cases x2; auto split: if_splits option.splits)
    qed
  next
    case (YulFunctionDefinitionStatement x) 
    then show ?thesis using assms ExitStatement YulFunctionDefinitionStatement
      by(auto)
  next
    case (YulIf x1 x2)
    then show ?thesis using assms ExitStatement
      by(auto split:list.splits if_splits)
  next
    case (YulSwitch x1 x2)
    then show ?thesis using assms ExitStatement
      by(auto split:list.splits if_splits prod.splits option.splits YulSwitchCase.splits YulLiteral.splits)
  next
    case (YulForLoop x1 x2 x3 x4)
    then show ?thesis using assms ExitStatement
      by(auto split:list.splits if_splits)
  next
    case YulBreak
    then show ?thesis using assms ExitStatement
      apply(auto split:list.splits if_splits)
  next
    case YulContinue
    then show ?thesis sorry
  next
    case YulLeave
    then show ?thesis sorry
  next
    case (YulBlock x11)
    then show ?thesis sorry
  qed
    
next
  case (EnterFunctionCall x31 x32)
  then show ?thesis sorry
next
  case (ExitFunctionCall x41 x42 x43 x44 x45)
  then show ?thesis sorry
next
  case (Expression x5)
  then show ?thesis sorry
qed


(* reasoning about Seq. idea:
   - EnterStatement (spre  @ spost) becomes
   - (map statement spre) @ (map statement spost)   
*)

(*
  another perspective. suppose P \<Longrightarrow> cont = h#t
  and also Q1 \<Longrightarrow> cont = t

  then. if (P, Q1) holds and (Q1, Q2) holds, then so does
  (P, Q2) (i.e., extending execution

  this is a special case of ht_steps. but could be a useful
  notion for reasoning about individual statements.

*)

(*
lemma evalYul'_bisect_cont :
  assumes H :
*)

(* 
  relating terminating sub-executions
*)

(*
  P1 P2 (? ?)

*)

end