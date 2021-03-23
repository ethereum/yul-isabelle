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

  hence "evalYul' D st 1 = YulResult st'" by(auto split:YulMode.splits)

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

lemma evalYulStep_cont_prefix_reg :
  assumes Hcont : "cont st = h#t"
  assumes Hstep : "evalYulStep D st = YulResult st'"
  shows "\<exists> pre . cont st' = pre @ t" 
proof(cases "mode st")
  case Regular
  show ?thesis
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
next
  case Break
  then show ?thesis 
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Break
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Break
      by(auto split: YulStatement.split_asm)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Break
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Break
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Break
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
next
  case Continue
  then show ?thesis
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Continue
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Continue
      by(auto split: YulStatement.split_asm)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Continue
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Continue
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Continue
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
next
  case Leave
  then show ?thesis 
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Leave
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Leave
      by(auto split: YulStatement.split_asm)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Leave
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Leave
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Leave
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
qed

lemma evalYul'_step_succeed_prior :
  assumes H : "evalYul' D input n = YulResult res"
  assumes "n' \<le> n"
  shows "\<exists> res' . evalYul' D input n' = YulResult res'" using assms
proof(induction n arbitrary: D input n' res)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof(cases "cont input")
    case Nil
    then show ?thesis using Suc.prems
      by(auto)
  next
    case (Cons ch ct)

    show ?thesis using Suc
    proof(cases "evalYulStep D input")
      case (ErrorResult x21 x22)
      then show ?thesis using Suc.prems Cons by auto
    next
      case (YulResult res1)

      then have Eval' : "evalYul' D res1 n = YulResult res"
        using Suc.prems Cons by auto

      have Leq : "n' - 1 \<le> n" using Suc.prems by auto

      obtain penult where Penult :
        "evalYul' D res1 (n' - 1) = YulResult penult" 
        using Suc.IH[OF Eval' Leq] by auto

      have FirstStep :
        "evalYul' D input 1 = YulResult res1"
        using YulResult
        by(auto split:YulMode.splits)

      have Conc' : "evalYul' D input (1 + (n' - 1)) = YulResult penult"
        using evalYul'_steps[OF FirstStep Penult] by auto

      show ?thesis
      proof(cases n')
        case Zero' : 0
        then show ?thesis 
          by(auto)
      next
        case Suc' : (Suc nat)

        hence N'Eq : "(1 + (n' - 1)) = n'"
          by auto

        show ?thesis using Conc' unfolding N'Eq by blast
      qed
    qed
  qed
qed

lemma evalYulStep_cont_extend :
  assumes Hstep : "evalYulStep D \<lparr>result = r, cont = h#t\<rparr> = 
                   YulResult \<lparr>result = r', cont = c'\<rparr>"
  shows "\<exists> pre . 
           evalYulStep D \<lparr> result = r, cont = [h] \<rparr> =
           YulResult \<lparr>result = r', cont = pre \<rparr> \<and>
           c' = pre @ t" 
proof(cases "r_mode r")
  case Regular
  then show ?thesis
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
next
  case Break
  then show ?thesis  using Hstep
    by(cases h; auto split: YulStatement.split_asm)
next
  case Continue
  then show ?thesis using Hstep
    by(cases h; auto split: YulStatement.split_asm)
next
  case Leave
  then show ?thesis using Hstep
    by(cases h; auto)
qed


lemma evalYulStep_cont_extend_fail :
  assumes Hstep : "evalYulStep D \<lparr>result = r, cont = h#t\<rparr> = 
                   ErrorResult msg bad"
  shows "\<exists>  bad' . evalYulStep D \<lparr> result = r, cont = [h] \<rparr> =
           ErrorResult msg bad'" 
proof(cases "r_mode r")
  case Regular
  then show ?thesis
  proof(cases h)
    case (EnterStatement st)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall name fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitFunctionCall name vals_old local_old funs_old fsig)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (Expression e)
    then show ?thesis using assms Regular
      by(auto simp add: updateResult_def split: YulResult.splits option.splits)
  qed
next
  case Break
  then show ?thesis  using Hstep
    by(cases h; auto split: YulStatement.splits)
  next
  case Continue
  then show ?thesis  using Hstep
    by(cases h; auto split: YulStatement.splits)
next
  case Leave
  then show ?thesis  using Hstep
    by(cases h; auto split: YulStatement.splits)
qed


lemma evalYul'_pres_fail :
  assumes H : "evalYul' D input n = ErrorResult msg res"
  assumes Leq : "n \<le> n'"
  shows "evalYul' D input n' = ErrorResult msg res" using assms
proof(induction n arbitrary: D input n' msg res)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case
  proof(cases "cont input")
    case Nil
    then show ?thesis using Suc.prems
      by(auto)
  next
    case (Cons ch ct)
    
    show ?thesis
    proof(cases "evalYulStep D input")
      case (ErrorResult msg' res')
      then show ?thesis using Suc.prems by(auto)
    next
      case (YulResult res')
  
      then have Eval' : "evalYul' D res' n = ErrorResult msg res"
        using Suc.prems Cons by auto
  
      show ?thesis using Suc.prems
      proof(cases "n' - Suc n")
        case Zero' : 0
        then show ?thesis using Suc.prems YulResult by auto
      next
        case Suc' : (Suc diff1)

        hence Leq : "n \<le> n' - 1" using Suc.prems by auto

        have NZ : "1 + (n' - 1) = n'" using Suc by auto
  
        have Penult :
          "evalYul' D res' (n' - 1) = ErrorResult msg res" 
          using Suc.IH[OF Eval' Leq] by auto
  
        have FirstStep :
          "evalYul' D input 1 = YulResult res'"
          using YulResult
          by(auto split:YulMode.splits)
  
        have Conc' : "evalYul' D input (1 + (n' - 1)) = ErrorResult msg res"
          using evalYul'_steps[OF FirstStep Penult] by auto
  
        then show ?thesis unfolding NZ by auto
      qed
    qed
  qed
qed

lemma evalYul'_pres_succeed :
  assumes H : "evalYul' D input n = YulResult res"
  assumes Hcont : "cont res = []"
  assumes Leq : "n \<le> n'"
  shows "evalYul' D input n' = YulResult res" using assms
proof(induction n arbitrary: D input n' res)
  case 0
  then show ?case by auto
next
  case (Suc n)

  show ?case
  proof(cases "cont input")
    case Nil
    then show ?thesis using Suc.prems
      by(auto)
  next
    case (Cons ch ct)
    
    show ?thesis
    proof(cases "evalYulStep D input")
      case (ErrorResult msg' res')
      then show ?thesis using Suc.prems Cons by(auto)
    next
      case (YulResult res1)
  
      then have Eval' : "evalYul' D res1 n = YulResult res"
        using Suc.prems Cons by auto
  
      show ?thesis
      proof(cases "n' - Suc n")
        case Zero' : 0
        then show ?thesis using Suc.prems YulResult by auto
      next
        case Suc' : (Suc diff1)

        hence Leq : "n \<le> n' - 1" using Suc.prems by auto

        have NZ : "1 + (n' - 1) = n'" using Suc by auto
  
        have Penult :
          "evalYul' D res1 (n' - 1) = YulResult res" 
          using Suc.IH[OF Eval' Suc.prems(2) Leq] by auto
  
        have FirstStep :
          "evalYul' D input 1 = YulResult res1"
          using YulResult
          by(auto split:YulMode.splits)
  
        have Conc' : "evalYul' D input (1 + (n' - 1)) = YulResult res"
          using evalYul'_steps[OF FirstStep Penult] by auto
  
        then show ?thesis unfolding NZ by auto
      qed
    qed
  qed
qed
  
(* ok, so now for local reasoning.
   there is a complication here, which is that it would be better to show that
   n1 is exactly the right number of steps to first reach []
*)

lemma evalYulStep_minsteps :
  assumes H : "evalYul' D \<lparr> result = r, cont = c \<rparr> n = YulResult \<lparr> result = rfin, cont = []\<rparr>"
  shows "\<exists> n' . n' \<le> n \<and> 
                evalYul' D \<lparr> result = r, cont = c \<rparr> n' = YulResult \<lparr> result = rfin, cont = [] \<rparr> \<and>
                (\<forall> x . x < n' \<longrightarrow>
                  (\<exists> r' ch ct .
                    evalYul' D \<lparr> result = r, cont = c \<rparr> x = 
                    YulResult \<lparr> result = r', cont = ch#ct \<rparr> ))" using H
proof(induction n arbitrary: r c rfin)
  case 0
  then show ?case by(auto)
next
  case (Suc n)
  show ?case 
  proof(cases "evalYul' D \<lparr>result = r, cont = c\<rparr> n")
    case (ErrorResult x21 x22)
    show ?thesis using evalYul'_pres_fail[OF ErrorResult, of "Suc n"] Suc.prems by auto
  next
    case (YulResult res1)

    obtain r1 c1 where Res1 : "res1 = \<lparr> result = r1, cont = c1 \<rparr>" by(cases res1; auto)

    show ?thesis
    proof(cases c1)
      case Nil

      have YR' : "evalYul' D \<lparr>result = r, cont = c\<rparr> n = YulResult \<lparr> result = r1, cont = [] \<rparr>"
        using YulResult Nil Res1 by simp

      obtain n' where Leq : "n' \<le> n"
                and Conc'1 : 
                    "evalYul' D \<lparr>result = r, cont = c\<rparr> n' = YulResult \<lparr>result = r1, cont = []\<rparr>"
                and Conc'2 :
                        "(\<forall>x<n'. \<exists>r' ch ct. evalYul' D \<lparr>result = r, cont = c\<rparr> x = 
                              YulResult \<lparr>result = r', cont = ch # ct\<rparr>)"
        using Suc.IH[OF YR'] by auto

      have Leq' : "n' \<le> Suc n" using Leq by auto

      have R1Eq : "r1 = rfin"
        using evalYul'_pres_succeed[OF Conc'1 _ Leq'] Suc.prems by auto

      show ?thesis using Leq' Conc'1 Conc'2 unfolding R1Eq by blast
    next
      case (Cons c1h c1t)

      have YR' : "evalYul' D \<lparr>result = r, cont = c\<rparr> n = YulResult \<lparr> result = r1, cont = c1h#c1t \<rparr>"
        using YulResult Cons Res1 by simp

      (* In this case Suc n is itself the minimal number of steps. *)
      have Conc'2 :
        "\<And> x . x < Suc n \<Longrightarrow> \<exists>r' ch ct. evalYul' D \<lparr>result = r, cont = c\<rparr> x = 
                    YulResult \<lparr>result = r', cont = ch # ct\<rparr>"
      proof-
        fix x
        assume Hx : "x < Suc n"

        hence Xleq : "x \<le> n" by auto

        show "\<exists>r' ch ct. evalYul' D \<lparr>result = r, cont = c\<rparr> x = 
                YulResult \<lparr>result = r', cont = ch # ct\<rparr>"
        proof(cases "evalYul' D \<lparr>result = r, cont = c\<rparr> x")
          case ErrorResult' : (ErrorResult x21 x22)
          show ?thesis using evalYul'_pres_fail[OF ErrorResult', of "Suc n"] Suc.prems Hx
            by auto
        next
          case YulResult' : (YulResult resx)

          show ?thesis
          proof(cases "cont resx")
            case Nil' : Nil

            have False using evalYul'_pres_succeed[OF YulResult' Nil' Xleq ] YR' Nil'
              by(cases resx; auto)

            then show ?thesis by auto
          next
            case (Cons rxh rxt)
            then show ?thesis using YulResult'
              by(cases resx; auto)
          qed
        qed
      qed

      show ?thesis using Suc.prems Conc'2 by blast
    qed
  qed
qed


(* if we're not done evaluating, what's in the tail doesn't matter
   *)
lemma evalYul'_cont_extend :
  assumes H : "evalYul' D \<lparr> result = ri, cont = ci \<rparr> n = YulResult \<lparr> result = rf, cont = cf\<rparr>"
  assumes Hcont : "cf = cfh#cft"
  shows "evalYul' D \<lparr> result = ri, cont = ci @ post \<rparr> n = 
                      YulResult \<lparr> result = rf, cont = cf @ post \<rparr>" using assms
proof(induction n arbitrary: ri ci rf cf post )
  case 0
  then show ?case 
    by(auto)
next
  case (Suc n)
  then show ?case

  proof(cases "evalYulStep D \<lparr> result = ri, cont = ci \<rparr>")
    case (ErrorResult msg res1)

    then show ?thesis 
    proof(cases "ci")
      case Nil
      then show ?thesis using Suc.prems by auto
    next
      case (Cons cih cit)
      then show ?thesis 
        using Suc.prems ErrorResult by auto
    qed
  next
    case (YulResult res1)

    obtain r1 c1 where Res1 : "res1 = \<lparr> result = r1, cont = c1 \<rparr>" by(cases res1; auto)

    show ?thesis
    proof(cases c1)
      case Nil

      have YR' : "evalYul' D \<lparr> result = ri, cont = ci \<rparr> 1 = YulResult \<lparr> result = r1, cont = [] \<rparr>"
        using YulResult Nil Res1 
        by(cases "ci"; simp split:YulMode.splits)

      have False using evalYul'_pres_succeed[OF YR', of "Suc n"] Suc.prems by auto

      thus ?thesis by auto
    next
      case (Cons c1h c1t)

      have YR' : "evalYul' D \<lparr> result = ri, cont = ci \<rparr> 1 = 
                  YulResult \<lparr> result = r1, cont = c1h#c1t \<rparr>"
        using YulResult Cons Res1
        by(cases "ci"; simp split:YulMode.splits)

      show ?thesis
      proof(cases "evalYul' D \<lparr> result = r1, cont = c1h#c1t \<rparr> n")
        case ErrorResult' : (ErrorResult msg2 res2)

        have False using evalYul'_steps[OF YR' ErrorResult'] Suc.prems by auto

        thus ?thesis by auto
      next
        case YulResult' : (YulResult res2)

        have Res2 : "res2 = \<lparr> result = rf, cont = cf\<rparr>"
          using evalYul'_steps[OF YR' YulResult'] Suc.prems by auto

        have Rest : "evalYul' D \<lparr> result = r1, cont = c1h#c1t \<rparr> n = 
                     YulResult \<lparr> result = rf, cont = cf\<rparr>"
          using YulResult' unfolding Res2 by auto

        have IHspec: "evalYul' D \<lparr>result = r1, cont = c1h#c1t @ post\<rparr> n =
                       YulResult\<lparr> result = result res2, cont = cont res2 @ post \<rparr>"
          using Suc.IH[OF Rest] Suc.prems Res2
          by auto

        show ?thesis
        proof(cases "ci")
          case Nil' : Nil
          then show ?thesis using Suc.prems by auto
        next
          case Cons' : (Cons cih cit)
          obtain res1_pre where 
            Res1_pre : "c1h#c1t = res1_pre @ cit" and
            Res1_pre_eval : "evalYulStep D \<lparr>result = ri, cont = [cih]\<rparr> = 
                             YulResult \<lparr>result = r1, cont = res1_pre\<rparr>"
            using evalYulStep_cont_extend[of D "ri" "cih" "cit" r1 c1] YulResult 
                  Cons' Res1 Cons
            by(auto)

          show ?thesis
          proof(cases "evalYulStep D \<lparr> result = ri, cont = cih#cit@post \<rparr>")
            case ErrorResult'' : (ErrorResult msg3 bad3)

            have False using evalYulStep_cont_extend_fail[OF ErrorResult''] Res1_pre_eval
              by auto

            then show ?thesis by auto
          next
            case YulResult''' : (YulResult res3)

            obtain r3 c3 where Res3 : "res3 = \<lparr> result = r3, cont = c3 \<rparr>" by(cases res3; auto)

            obtain res3_pre where
              Res3_pre : "c3 = res3_pre @ cit@post" and
              Res3_pre_eval : "evalYulStep D \<lparr>result = ri, cont = [cih]\<rparr> = 
                                YulResult \<lparr>result = r3, cont = res3_pre\<rparr>"
              using evalYulStep_cont_extend[of D "ri" "cih" "cit@post" r3 c3] 
                  YulResult''' Res3
                  Cons' Res3 Cons
              by auto

            have R1_R3 : "r1 = r3"
              using Res3_pre_eval Res1_pre_eval by auto

            have R1pre_R3pre : "res1_pre = res3_pre"
              using Res3_pre_eval Res1_pre_eval by auto

            have YR''' : "evalYul' D \<lparr> result = ri, cont = cih#cit@post \<rparr> 1 = 
                        YulResult \<lparr> result = r1, cont = c1h#c1t@post \<rparr>"
              using YulResult''' Cons Res1 Res3 R1_R3 R1pre_R3pre 
                    Res1_pre Res1_pre_eval
                    Res3_pre Res3_pre_eval
              by(simp split:YulMode.splits)


            show ?thesis
              using evalYul'_steps[OF YR''' IHspec] Res2 Cons'
              by(auto)
          qed
        qed
      qed
    qed
  qed
qed

(* generalization: assume a potentially nonempty residual continuation after running first command? *)

lemma evalYul'_seq :
  assumes H1 : "evalYul' D \<lparr>result = r1, cont = c1\<rparr> n1 = 
               YulResult \<lparr>result = r2, cont = residue\<rparr>"
  assumes H2 : "evalYul' D \<lparr>result = r2, cont = residue @ c2 \<rparr> n2 = YulResult \<lparr> result = r3, cont = [] \<rparr>"
  shows "evalYul' D \<lparr> result = r1, cont = c1 @ c2\<rparr> (n1 + n2) = YulResult \<lparr> result = r3, cont = [] \<rparr>" using assms
proof(induction n1 arbitrary: r1 c1 r2 residue c2 n2 r3)
  case 0
  then show ?case
    by auto
next
  case (Suc n1)

  show ?case
  proof(cases c1)
    case Nil

    then have AlreadyDone : 
      "evalYul' D \<lparr>result = r1, cont = c1\<rparr> 0 = YulResult \<lparr>result = r1, cont = c1\<rparr>"
      by(auto)

    have R2 : "r1 = r2" and Residue : "residue = []"
      using evalYul'_pres_succeed[OF AlreadyDone, of "Suc n1"] Suc.prems(1) Nil
      by auto

    have Conc' : "evalYul' D \<lparr>result = r2, cont = c2\<rparr> n2 = YulResult \<lparr>result = r3, cont = []\<rparr>"
      using Suc.prems(2) unfolding R2 Residue Nil by auto

    show ?thesis using evalYul'_pres_succeed[OF Conc', of "Suc n1 + n2"]
      unfolding R2 Residue Nil by auto
  next
    case (Cons c1h c1t)

    show ?thesis
    proof(cases "evalYulStep D \<lparr>result = r1, cont = c1\<rparr>")
      case (ErrorResult msg rbad)
  
      then have False using Suc Cons
        by(cases c1; simp del:evalYulStep.simps)

      thus ?thesis by auto
    next
      case (YulResult res1')

      obtain r1' c1' where Res1' : "res1' = \<lparr> result = r1', cont = c1' \<rparr>"
        by(cases res1'; auto)

      have Eval' : "evalYul' D \<lparr>result = r1', cont = c1'\<rparr> n1 =
                    YulResult \<lparr>result = r2, cont = residue\<rparr>"
        using Res1' Suc.prems YulResult Cons by auto

      have IHspec : "evalYul' D \<lparr>result = r1', cont = c1' @ c2\<rparr> (n1 + n2) =
              YulResult \<lparr>result = r3, cont = []\<rparr>"
        using Suc.IH[OF Eval'] (* Suc.prems(2) *) Suc.prems(2)
        by auto

      (* need a "first step" lemma *)

      obtain c1'_new where
        C1'_new_step : "evalYulStep D \<lparr>result = r1, cont = [c1h] \<rparr> = 
                        YulResult \<lparr>result = r1', cont = c1'_new\<rparr>" and
        C1'_new_pre : "c1' = c1'_new @ c1t"
        using evalYulStep_cont_extend[of D r1 c1h c1t r1' c1'] YulResult Cons Res1'
        by auto

      have FirstStep' : "evalYul' D \<lparr>result = r1, cont = c1h#c1t \<rparr> 1 = YulResult \<lparr> result = r1', cont = c1' \<rparr>"
        using Res1' YulResult Cons
        by(auto)

      show ?thesis
      proof(cases "evalYulStep D \<lparr>result = r1, cont = c1 @ c2\<rparr>")
        case ErrorResult' : (ErrorResult msg rbad)

        hence ER' : "evalYulStep D \<lparr>result = r1, cont = c1h# (c1t @ c2)\<rparr> = ErrorResult msg rbad" 
          using Cons by auto

        have False using evalYulStep_cont_extend_fail[OF ER'] C1'_new_step by auto

        thus ?thesis by auto
      next
        case YulResult' : (YulResult res1'')

        obtain r1'' c1'' where Res1'' : "res1'' = \<lparr> result = r1'', cont = c1'' \<rparr>"
          by(cases res1''; auto)

        have YR' : "evalYulStep D \<lparr>result = r1, cont = c1h # (c1t @ c2)\<rparr> =
                    YulResult \<lparr> result = r1'', cont = c1'' \<rparr>"
          using YulResult' unfolding Res1'' Cons by auto

        have C1'' : "c1'' = c1'_new @ (c1t @ c2)" and R1'' : "r1'' = r1'"
          using evalYulStep_cont_extend[OF YR'] C1'_new_step C1'_new_pre
          by auto

        hence C1''_C1' : "c1'' = c1' @ c2" using C1'_new_pre
          by simp

        have FirstStep : "evalYul' D \<lparr>result = r1, cont = c1 @ c2\<rparr> 1 = 
                          YulResult \<lparr> result = r1', cont = c1' @ c2 \<rparr> "
          using YR' unfolding Cons C1''_C1' R1''
        by(auto)

      show ?thesis using evalYul'_steps[OF FirstStep IHspec] by auto
    qed
  qed
qed


(* evalYul' D \<lparr>result = r1, cont = c1 @ c2\<rparr> = YulResult \<lparr>result = r1', cont = c1' @ c2\<rparr>  *)
(*
      proof(cases residue)
      case Nil' : Nil
        then show ?thesis using evalYul'_steps
      next
        case (Cons resdh resdt)
        then show ?thesis sorry
      qed

      show ?thesis using evalYul'_steps
*)
(* idea: apply continuation-decomposition here to show that we get what we expect after the first step *)
(* may need a lemma saying what happens when we add a suffix.
probably this will require a case analysis on residue...?
 *)
  
(*
  show ?case
  proof(cases c1)
    case Nil
    show ?thesis
      using Suc


    proof(cases c2)
      case Nil' : Nil
      then show ?thesis using Suc Nil by(cases n2; auto)
    next
      case (Cons c2h c2t)

(*
      obtain r2' where R2' : "evalYulStep D \<lparr>result = r2, cont = c2h # c2t\<rparr> = YulResult r2'"
        using Suc.prems Nil Cons
        by(cases n2; cases "evalYulStep D \<lparr>result = r2, cont = c2h # c2t\<rparr>"; 
                           auto simp del: evalYulStep.simps)
*)
      show ?thesis
      proof(cases "evalYul' D \<lparr>result = r1, cont = c1\<rparr> n1")
        case (ErrorResult x21 x22)

        have False using evalYul'_pres_fail[OF ErrorResult, of "Suc n1"] Suc.prems(1)
          by auto

        then show ?thesis by auto
      next
        case (YulResult res1')

        obtain r1' c1' where Res1' : "res1' = \<lparr> result = r1', cont = c1' \<rparr>"
          by(cases res1'; auto)

        have YR' : "evalYul' D \<lparr>result = r1, cont = c1\<rparr> n1 = YulResult \<lparr> result = r1', cont = c1' \<rparr>"
          using YulResult unfolding Res1' by auto

        show ?thesis using Suc.IH YR'
        
      qed
  next
    case (Cons a list)
    then show ?thesis sorry
  qed

        apply(auto simp del: evalYulStep.simps)


  proof(cases n1)
    case Zero' : 0
    show ?thesis
    proof(cases n2)
      case Zero'' : 0
      then show ?thesis 
        using Suc Zero' by(auto)
    next
      case Suc'' : (Suc nat)
      then show ?thesis using Suc Zero'
        apply(auto simp del: evalYulStep.simps)
    qed

    then show ?thesis using Suc apply(auto simp del: evalYulStep.simps)
  next
    case (Suc nat)
    then show ?thesis sorry
  qed

    apply(auto simp del: evalYulStep.simps)



  proof(cases "evalYulStep D \<lparr>result = r2', cont = xh # xt\<rparr>")
    case (YulResult x1)
    show ?thesis
      using YulResult 0 apply(auto simp del: evalYulStep.simps)

    proof(cases "evalYulStep D \<lparr>result = r2', cont = xh # xt @ c2\<rparr> ")
      case YulResult' : (YulResult x1')
      then show ?thesis using YulResult 0 apply(auto simp del: evalYulStep.simps)
    next
      case (ErrorResult x21 x22)
      then show ?thesis sorry
    qed
    then show ?thesis using 0 apply(auto simp del: evalYulStep.simps)
  next
    case (ErrorResult x21 x22)
    then show ?thesis sorry
  qed
    
    apply(auto simp del: evalYulStep.simps)
next
  case (Suc n1)
  show ?case
  proof(cases c1)
    case Nil
    then show ?thesis using Suc.prems(1) Suc.prems(2) apply(cases c2; auto)
      apply(cases "r_mode r2"; auto) 
  next
    case (Cons a list)
    then show ?thesis sorry
  qed

  show ?case using Suc.prems(1) Suc.prems(2)
    apply(auto simp del: evalYulStep.simps)
    apply(cases c1; auto)
    
  next
    case Suc' : (Suc n1')
    then show ?thesis sorry
  qed

    apply(auto)
qed
*)
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