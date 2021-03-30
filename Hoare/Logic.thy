theory Logic imports "../Yul/YulSemanticsSingleStep"
begin

(* need to figure out relationship between states now that we are
   kind of masking out the continuation. *)

(*
  
*)
definition YulSteps ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
  (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ % {_} {_}")
  where
"YulSteps D P Q =
  (\<forall> st . P (st) \<longrightarrow>
    (\<exists> n st' . evalYul' D st n = YulResult st' \<and>
     Q st'))"

lemma HTI [intro]:
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
"is_halted r = (cont r = [] \<and> mode r = Regular)"

(*
lemma YSSI' :
  assumes H : "(D % {P} {Q})"
  assumes HP : "\<And> st . P st \<Longrightarrow> cont st = [EnterStatement c]"
  assumes HQ : "\<And> st . Q st \<Longrightarrow> cont st = []"
  shows "(D % {P} c {Q})"
  using assms unfolding YulStepsStmt_def by auto

lemma YSSE' :
  assumes H : "(D % {P} c {Q})"
  shows "(D % {P} {Q})" 
        "\<And> st . P st \<Longrightarrow> cont st = [EnterStatement c]" 
        "\<And> st . Q st \<Longrightarrow> cont st = []"
  using assms unfolding YulStepsStmt_def by auto

lemma YSSI [intro] :
  assumes H : "\<And> st . P st \<Longrightarrow> 
                (\<exists> n st' . evalYul' D st n = YulResult st' \<and>
                   Q st')"
  assumes HP : "\<And> st . P st \<Longrightarrow> cont st = [EnterStatement c]"
  assumes HQ : "\<And> st . Q st \<Longrightarrow> cont st = []"
  shows "(D % {P} c {Q})"
  using assms unfolding YulStepsStmt_def by auto

lemma YSSE1 :
  assumes H : "(D % {P} c {Q})"
  assumes HP : "P st"
  shows "(\<exists> n st'. evalYul' D st n = YulResult st' \<and> Q st')"
  using assms unfolding YulStepsStmt_def YulSteps_def by auto

lemma YSSE2 :
  assumes H : "(D % {P} c {Q})"
  assumes HP : "P st"
  shows "cont st = [EnterStatement c]" 
  using assms unfolding YulStepsStmt_def YulSteps_def by auto

lemma YSSE3 :
  assumes H : "(D % {P} c {Q})"
  assumes HQ : "Q st"
  shows "cont st = []"
  using assms unfolding YulStepsStmt_def YulSteps_def by auto

lemma YSElI [intro] :
  assumes H : "\<And> st . P st \<Longrightarrow> 
                (\<exists> n st' . evalYul' D st n = YulResult st' \<and>
                   Q st')"
  assumes HP : "\<And> st . P st \<Longrightarrow> cont st = els"
  assumes HQ : "\<And> st . Q st \<Longrightarrow> cont st = []"
  shows "(D %* {P} els {Q})"
  using assms unfolding YulStepsStEls_def by auto

lemma YSElE1 :
  assumes H : "(D %* {P} els {Q})"
  assumes HP : "P st"
  shows "(\<exists> n st'. evalYul' D st n = YulResult st' \<and> Q st')"
  using assms unfolding YulStepsStEls_def YulSteps_def by auto

lemma YSElE2 :
  assumes H : "(D %* {P} els {Q})"
  assumes HP : "P st"
  shows "cont st = els" 
  using assms unfolding YulStepsStEls_def YulSteps_def by auto

lemma YSElE3 :
  assumes H : "(D %* {P} els {Q})"
  assumes HQ : "Q st"
  shows "cont st = []"
  using assms unfolding YulStepsStEls_def YulSteps_def by auto
*)
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

lemma evalYul'_seq_gen :
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
qed

lemma evalYul'_seq :
  assumes H1 : "evalYul' D \<lparr>result = r1, cont = c1\<rparr> n1 = 
               YulResult \<lparr>result = r2, cont = []\<rparr>"
  assumes H2 : "evalYul' D \<lparr>result = r2, cont = c2 \<rparr> n2 = YulResult \<lparr> result = r3, cont = [] \<rparr>"
  shows "evalYul' D \<lparr> result = r1, cont = c1 @ c2\<rparr> (n1 + n2) = YulResult \<lparr> result = r3, cont = [] \<rparr>" 
  using evalYul'_seq_gen[of D r1 c1 n1 r2 "[]" c2 n2 r3] H1 H2
  by auto

(* a more familiar-looking Hoare logic of statements - but showing its relationship to the
   actual executions beyond the first instruction will take some work. *)
abbreviation YulStepsStmt ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   ('v, 't) YulStatement \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ % {_} _ {_}") where
"(D % {P} c {Q}) \<equiv>
  (D % {(\<lambda> st . P (result st) \<and> cont st = [EnterStatement c])}
       {(\<lambda> st . Q (result st) \<and> cont st = [])})"

(* how to correctly constrain p/q? *)
abbreviation YulStepsStackEls ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   ('g, 'v, 't) StackEl list \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ %* {_} _ {_}") where
"(D %* {P} els {Q}) \<equiv>
  (D % {(\<lambda> st . P (result st) \<and> cont st = els)}
       {(\<lambda> st . Q (result st) \<and> cont st = [])})"


(* TODO: make sure this says what we think it does. *)
lemma stackEls_sem_nil :
  shows "D %* {P} [] {P}"
  unfolding YulSteps_def
  by auto

(* convenience lemmas for Hoare triples separating
   result and cont *)

lemma HTI' [intro]:
  assumes H :
    "\<And> res contn. P1 res \<Longrightarrow> P2 contn \<Longrightarrow>
      (\<exists> n st' . evalYul' D \<lparr>result = res, cont = contn \<rparr> n = YulResult st' \<and>
     Q st')"
  shows "D % {(\<lambda> st . P1 (result st) \<and> P2 (cont st))} {Q}" 
proof
  fix st :: "('a, 'b, 'c) result"
  assume Assm : "P1 (result st) \<and> P2 (cont st)"
  show "\<exists>n st'. evalYul' D st n = YulResult st' \<and> Q st'"
    using H Assm
    by(cases st; auto)
qed

lemma HTE' [elim]:
  assumes H : "D%{(\<lambda> st . P1 (result st) \<and> P2 (cont st))} {Q}"
  assumes HP1 : "P1 res"
  assumes HP2 : "P2 contn"
  shows "(\<exists> n st'. evalYul' D \<lparr> result = res, cont = contn \<rparr> n = YulResult st' \<and>
     Q st')"
  using assms unfolding YulSteps_def by (auto)


lemma stackEls_sem_cons :
  fixes h :: "('v, 't) YulStatement"
  fixes t :: "('g, 'v, 't) StackEl list"
  assumes H1 : "D % {P1} h {P2}"
  assumes H2 : "D %* {P2} t {P3}"
  shows "D %* {P1} (EnterStatement h#t) {P3}"
proof(rule HTI)
  fix st1 :: "('g, 'v, 't) result"

  assume "P1 (result st1) \<and> cont st1 = EnterStatement h # t"
  then obtain res1 cont1 where
  RC1 : "st1 = \<lparr> result = res1, cont = cont1 \<rparr>" and
  Hp1 : "P1 res1" and Hcont1 : "cont1 = EnterStatement h # t"
    by (cases st1; auto)

  obtain n1 st2 where
    Eval1 : "evalYul' D \<lparr>result = res1, cont = [EnterStatement h]\<rparr> n1 = 
                   YulResult st2"
    and Hp2 : "P2 (result st2)"
    and Cont2 : "cont st2 = []"
    using HTE'[OF H1 Hp1 refl] by auto

  obtain res2 where St2 : "st2 = \<lparr> result = res2, cont = [] \<rparr>"
    using Hp2 Cont2 by(cases st2; auto)

  hence Eval1' : "evalYul' D \<lparr>result = res1, cont = [EnterStatement h]\<rparr> n1 =
                  YulResult \<lparr> result = res2, cont = [] \<rparr>"
    using Eval1 by auto

  obtain n2 st3 
    where Eval2 : "evalYul' D \<lparr>result = res2, cont = t\<rparr> n2 = 
                   YulResult st3"
    and Hp3 : "P3 (result st3)"
    and Hcont3 : "cont st3 = []"
    using HTE'[OF H2 Hp2 refl] St2
    by(auto)

  obtain res3 where St3 : "st3 = \<lparr> result = res3, cont = []\<rparr>"
    using Hcont3 by(cases st3; auto)

  hence Eval2' : "evalYul' D \<lparr>result = res2, cont = t\<rparr> n2 = YulResult \<lparr> result = res3, cont = []\<rparr>"
    using Eval2 by auto

  have Conc' : "evalYul' D st1 (n1 + n2) = YulResult st3 \<and>
                  P3 (result st3) \<and> cont st3 = []"
    using evalYul'_seq[OF Eval1' Eval2'] Hp3 Hcont3 unfolding RC1 Hcont1 St3
    by auto
   
  thus "\<exists>n st'.
           evalYul' D st1 n = YulResult st' \<and>
           P3 (result st') \<and> cont st' = []"
    by(blast)
qed

(* next step: show the rule for blocks.
   this will be basically the same, but will have some extra stuff corresponding to the
    contexts.
*)



(* for the precondition in H, we need another clause characterizing funs
   (by analogy with forward Hoare assignment rule.)
*)
(* r_vals = []? *)

(* need to be able to use H to prove that gatherFunctions succeeds
   (right now we don't have that - we need to prove it succeeds to use H) *)
(* "P \<longrightarrow> ..." part of the conclusion is probably wrong.
   what we really want to say is 
   
*)

(* formal final clause in conclusion Hoare triple
hopefully unneeded, as I'm pretty sure it's not true in general.
hopefully the hypothesis Hoare triple captures all the needed relationships


maybe we change this forall to an exists?

(*
(\<forall> st0 . P st0 \<longrightarrow>
                        r_funs st = r_funs st0 \<and>
                        r_locals st = restrict (r_locals st) (r_locals st0)))
*)
*)


(*
lemma HBlock :
assumes HP : "\<And> st . P st \<Longrightarrow> (\<exists> f . gatherYulFunctions (r_funs st) ls = Inl f)"
assumes H : 
  "D %* {(\<lambda> st . \<exists> funs' . P (st \<lparr> r_funs := funs' \<rparr>) \<and> 
                   Inl (r_funs st) = gatherYulFunctions (funs') ls)} 
        (map EnterStatement ls :: ('g, 'v, 't) StackEl list)
        {Q}"
shows "D % {X} 
           YulBlock ls
           {Q}"
proof
*)

(*
 the issue is that in the predicate on the final state, we don't actually have the data we
 need to reconstruct the old values of locals. that is, what new locals were introduced
 during the block.
*)

(* Appel: "{P} c {Q} forall k . {Q} k \<longrightarrow> {P} c;k"
*)

(* let's look at a backwards version of this Hoare rule, instead. *)

(* if we actually do include the final "exitStatement" in the hypothesis, does this help? *)

(*
lemma HBlock_inner : 
  assumes HP : "\<And> st . P st \<Longrightarrow> (\<exists> f . gatherYulFunctions (r_funs st) ls = Inl f)"
  assumes H : "D %* {(\<lambda> st . \<exists> funs' . P (st \<lparr> r_funs := funs' \<rparr>) \<and> 
                   Inl (r_funs st) = gatherYulFunctions (funs') ls)} 
        ((map EnterStatement ls :: ('g, 'v, 't) StackEl list) @
          [ExitStatement (YulBlock ls) locals funs])
        {Q}"
*)
(* idea: what if we include this in the rule? *)
(*
[ExitStatement YUL_STMT{ {\<guillemotleft>sl\<guillemotright>} } (r_locals r) (r_funs r)]
*)  

lemma restrict_self_gen :
  "restrict x (pref @ x) = x"
proof(induction x arbitrary: pref)
  case Nil
  then show ?case by auto
next
  case (Cons a x)

  obtain a1 a2 where A: "a = (a1, a2)" by(cases a; auto)

  show ?case
  proof(cases "map_of pref a1")
    case None
    then show ?thesis using A Cons.prems Cons.IH[of "pref @ [(a1, a2)]"]
      by(auto split: option.splits)
  next
    case (Some v)
    then show ?thesis using A Cons.prems Cons.IH[of "pref @ [(a1, a2)]"]
      by(auto split: option.splits)
  qed
qed
    
lemma restrict_self : "restrict x x = x"
  using restrict_self_gen[of "x" "[]"]
  by auto


definition is_regular :: "YulMode \<Rightarrow> bool" where
"is_regular x =
  (x = Regular)"

declare is_regular_def [simp]

definition is_irregular :: "YulMode \<Rightarrow> bool" where
"is_irregular x =
  (x \<noteq> Regular)"

declare is_irregular_def [simp]

definition is_break :: "YulMode \<Rightarrow> bool" where
"is_break x =
  (x = Break)"

declare is_break_def [simp]

definition is_continue :: "YulMode \<Rightarrow> bool" where
"is_continue x =
  (x = Continue)"

declare is_continue_def [simp]

definition is_leave :: "YulMode \<Rightarrow> bool" where
"is_leave x =
  (x = Leave)"

declare is_leave_def [simp]

lemma irregular_skips_body :
  assumes H : "is_irregular (mode st)"
  assumes Cont : "cont st = (map EnterStatement ls :: ('g, 'v, 't) StackEl list)"
  assumes Eval : "evalYul' D st n = YulResult st'"
  shows "result st = result st' \<and> (\<exists> pref . cont st = pref @ cont st')"
  using assms
proof(induction n arbitrary: st st' ls)
  case 0
  then show ?case by(auto)
next
  case (Suc n)

  show ?case
  proof(cases ls)
    case Nil
    then show ?thesis using Suc.prems by(auto)
  next
    case (Cons lh lt)

    show ?thesis
    proof(cases "r_mode (result st)")
      case Regular
      then show ?thesis using Suc.prems by(auto)
    next
      case Break

      then have St1 : "evalYulStep D st = YulResult (st\<lparr>cont := map EnterStatement lt\<rparr>)"
        using Suc.prems Cons by auto

      hence Eval' : "evalYul' D (st\<lparr>cont := map EnterStatement lt\<rparr>) n = YulResult st'"
        using Suc.prems Cons Break 
        by(auto)

      have ResEq : "result (st\<lparr>cont := map EnterStatement lt\<rparr>) = result st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence ResEq' : "result (st) = result st'" by auto

      obtain pref where Pref : "cont (st\<lparr>cont := map EnterStatement lt\<rparr>) = pref @ cont st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence Pref' : "cont st = (EnterStatement lh # pref) @ cont st'"
        using Suc.prems Cons by auto

      show ?thesis using ResEq' Pref' by auto
    next
      case Continue

      then have St1 : "evalYulStep D st = YulResult (st\<lparr>cont := map EnterStatement lt\<rparr>)"
        using Suc.prems Cons by auto

      hence Eval' : "evalYul' D (st\<lparr>cont := map EnterStatement lt\<rparr>) n = YulResult st'"
        using Suc.prems Cons Continue
        by(auto)

      have ResEq : "result (st\<lparr>cont := map EnterStatement lt\<rparr>) = result st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence ResEq' : "result (st) = result st'" by auto

      obtain pref where Pref : "cont (st\<lparr>cont := map EnterStatement lt\<rparr>) = pref @ cont st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence Pref' : "cont st = (EnterStatement lh # pref) @ cont st'"
        using Suc.prems Cons by auto

      show ?thesis using ResEq' Pref' by auto
    next
      case Leave
      then have St1 : "evalYulStep D st = YulResult (st\<lparr>cont := map EnterStatement lt\<rparr>)"
        using Suc.prems Cons by auto

      hence Eval' : "evalYul' D (st\<lparr>cont := map EnterStatement lt\<rparr>) n = YulResult st'"
        using Suc.prems Cons Leave
        by(auto)

      have ResEq : "result (st\<lparr>cont := map EnterStatement lt\<rparr>) = result st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence ResEq' : "result (st) = result st'" by auto

      obtain pref where Pref : "cont (st\<lparr>cont := map EnterStatement lt\<rparr>) = pref @ cont st'"
        using Suc.IH[OF _ _ Eval', of lt] Suc.prems by(auto)

      hence Pref' : "cont st = (EnterStatement lh # pref) @ cont st'"
        using Suc.prems Cons by auto

      show ?thesis using ResEq' Pref' by auto
    qed
  qed
qed

(* TODO: need to figure out whether we can state HBlock this way in the presence of
   non-Regular execution mode. The problem is that in a non-regular execution mode,
   empty continuation means "about to crash".
*)


lemma HBlock :

  assumes H : "D %* {P} 
                    (map EnterStatement ls :: ('g, 'v, 't) StackEl list) 
                    {(\<lambda> st . Q (st \<lparr> r_funs := orig_funs
                                          , r_locals := restrict (r_locals st) orig_locals \<rparr>))}"
  shows "D % {(\<lambda> st . r_locals st = orig_locals \<and>
                      r_funs st = orig_funs \<and>
                      gatherYulFunctions (r_funs st) ls = Inl f \<and>
                      P (st \<lparr> r_funs := f \<rparr> ))}
              YulBlock (ls )
              {Q}"
proof
  fix res contn

  assume "r_locals res = orig_locals \<and>
       r_funs res = orig_funs \<and>
       gatherYulFunctions (r_funs res) ls = Inl f \<and> P (res\<lparr>r_funs := f\<rparr>)"

  hence Locals : "r_locals res = orig_locals" and
        Funs : "r_funs res = orig_funs" and
        Gather : "gatherYulFunctions (r_funs res) ls = Inl f" and
        HP : "P (res\<lparr>r_funs := f\<rparr>)"
    by auto

  assume Contn : "contn = ([EnterStatement (YulBlock ls)] :: ('g, 'v, 't) StackEl list)"

  have "\<exists>n st'.
     evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls\<rparr> n =
     YulResult st' \<and>
     Q (result st'
        \<lparr>r_funs := orig_funs, r_locals := restrict (r_locals (result st')) orig_locals\<rparr>) \<and>
     cont st' = []"
    using HTE[OF H, of "\<lparr> result = (res \<lparr> r_funs := f \<rparr>), cont = map EnterStatement ls\<rparr>"]
    unfolding result.simps using HP
    by(blast)

  then obtain n1 st1 where
    Eval : "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls\<rparr> n1 =
     YulResult st1" and
    HQ : "Q (result st1
          \<lparr>r_funs := orig_funs, r_locals := restrict (r_locals (result st1)) orig_locals\<rparr>)" and
    Cont1 : "cont st1 = []" by blast

  obtain res1 cont1 where St1 : 
    "st1 = \<lparr> result = res1, cont = cont1 \<rparr>" by(cases st1; auto)

(* i think we want n = n+1
   st' = st1, but with locals and funs reset.
*)
  show "\<exists>n st'.
          evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult st' \<and>
          Q (result st') \<and> cont st' = []"
  proof(cases "evalYulStep D \<lparr>result = res, cont = contn\<rparr>")
    case (ErrorResult x21 x22)
    then show ?thesis using Eval Contn Gather
      by(cases "r_mode res"; simp add: updateResult_def)
  next
    case (YulResult res2)
    show ?thesis
    proof(cases "r_mode res")
      case Regular

(* get cont of res2
   use sequencing lemma to relate it to the inner body premises
   then combine 
      first step + body steps + final exit step
      to get final result
*)

      show ?thesis
      proof(cases "cont res2")
        case Nil

        then have Conc' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = YulResult res2 \<and> Q (result res2) \<and> cont res2 = []"
          using Contn Regular  Gather Eval YulResult HQ St1
          by(auto simp add: updateResult_def)

        then show ?thesis by blast
      next
        case (Cons r2h r2t)

        then have Conc' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> (2 + n1) = 
          YulResult (\<lparr> result = res1  \<lparr>r_funs := orig_funs, r_locals := restrict (r_locals (result st1)) orig_locals\<rparr>
                     , cont = []\<rparr>)"
          using Contn Regular  Gather Eval YulResult HQ St1
          apply(auto simp add: updateResult_def)

      qed
(*

      have Conc' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> (2 + n1) = 
        YulResult (\<lparr> result = res1  \<lparr>r_funs := orig_funs, r_locals := restrict (r_locals (result st1)) orig_locals\<rparr>
                   , cont = []\<rparr>)"
        using Eval HQ Cont1 Locals Funs Gather HP Contn YulResult Regular
        apply(auto)
*)
(*
    next
      case Break

      have Res1' : "res1 = res\<lparr>r_funs := f\<rparr>"
        using irregular_skips_body[OF _ _ Eval] Break St1
        by auto

      have Res2 : "res2 = \<lparr>result = res, cont = []\<rparr>"
        using YulResult Res1' Break St1 Contn
        by(auto)

      hence ResQ : "Q res" using HQ St1 Locals Funs Res1'
        by(cases res; simp add: restrict_self)

      have Conc' : 
        "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = YulResult res2 \<and> 
                    Q (result res2) \<and> cont res2 = []"
        using YulResult Res1' Break St1 Contn Res2 ResQ
        by(auto)

      then show ?thesis by blast
    next
      case Continue

      have Res1' : "res1 = res\<lparr>r_funs := f\<rparr>"
        using irregular_skips_body[OF _ _ Eval] Continue St1
        by auto

      have Res2 : "res2 = \<lparr>result = res, cont = []\<rparr>"
        using YulResult Res1' Continue St1 Contn
        by(auto)

      hence ResQ : "Q res" using HQ St1 Locals Funs Res1'
        by(cases res; simp add: restrict_self)

      have Conc' : 
        "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = YulResult res2 \<and> 
                    Q (result res2) \<and> cont res2 = []"
        using YulResult Res1' Continue St1 Contn Res2 ResQ
        by(auto)

      then show ?thesis by blast
    next
      case Leave

      have Res1' : "res1 = res\<lparr>r_funs := f\<rparr>"
        using irregular_skips_body[OF _ _ Eval] Leave St1
        by auto

      have Res2 : "res2 = \<lparr>result = res, cont = []\<rparr>"
        using YulResult Res1' Leave St1 Contn
        by(auto)

      hence ResQ : "Q res" using HQ St1 Locals Funs Res1'
        by(cases res; simp add: restrict_self)

      have Conc' : 
        "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = YulResult res2 \<and> 
                    Q (result res2) \<and> cont res2 = []"
        using YulResult Res1' Leave St1 Contn Res2 ResQ
        by(auto)

      then show ?thesis by blast
    qed
  qed
qed
*)
(*
      proof(rule exI[of _ "1 :: nat"];
            rule exI[of _ "st1
            \<lparr>funs := orig_funs, locals := restrict (r_locals (result st1)) orig_locals\<rparr>"])

        show "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 =
    YulResult (locals_update (\<lambda>_. restrict (r_locals (result st1)) orig_locals) (funs_update (\<lambda>_. orig_funs) st1)) \<and>
    Q (result (locals_update (\<lambda>_. restrict (r_locals (result st1)) orig_locals) (funs_update (\<lambda>_. orig_funs) st1))) \<and>
    cont (locals_update (\<lambda>_. restrict (r_locals (result st1)) orig_locals) (funs_update (\<lambda>_. orig_funs) st1)) = []"
          using Contn Break St1 Eval HQ Cont1
          apply(simp)
          apply(cases n1; clarsimp)

      show ?thesis using YulResult Break Contn St1 HQ Cont1
        apply(simp)
*)
(*
      obtain stc where Stc : "stc = \<lparr> result = result st1
                                         \<lparr>r_funs := orig_funs,
                                          r_locals := restrict (r_locals (result st1)) orig_locals \<rparr>
                                    , cont = [] \<rparr>"
        by simp
*)
(*
      have Conc' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = YulResult stc \<and>
                      Q (result stc) \<and> cont stc = []"
        using Eval Contn Gather HQ Cont1 Locals Funs Break Stc
        apply(cases n1; cases res; simp del: evalYul'.simps; simp)
*)
(*
    then show ?thesis using Eval Contn Gather HQ Cont1 Locals Funs
      apply(cases st1; cases res; simp del: evalYul'.simps)
      apply(cases n1; simp)
       apply(rule_tac x = 1 in exI)
       apply(simp add: restrict_self)
      apply(cases ls; simp)
       apply(clarsimp)
       apply(rule_tac x = 1 in exI)
       apply(simp add: restrict_self)
       apply(clarsimp)
*)
      
    next
      case Continue
      then show ?thesis sorry
    next
      case Leave
      then show ?thesis sorry
    qed
  qed
qed

(*
lemma HBlock :
assumes HP : "\<And> st . P st \<Longrightarrow> (\<exists> f . gatherYulFunctions (r_funs st) ls = Inl f)"
assumes H : 
  "D %* {(\<lambda> st . P (st \<lparr> r_funs := funs' \<rparr>) \<and> 
                   r_locals st = locals' \<and>
                   Inl (r_funs st) = gatherYulFunctions (funs') ls)} 
        (map EnterStatement ls :: ('g, 'v, 't) StackEl list)
        {Q}"
shows "D % {P} 
           YulBlock ls
           {(\<lambda> st .
                Q (st \<lparr> r_funs := funs', r_locals := locals' \<rparr>))}"
proof
  fix res :: "('g, 'v, 't) result'"
  fix contn :: "('g, 'v, 't) StackEl list"

  assume Hres : "P res"
  assume Hcontn : "contn = [EnterStatement (YulBlock ls)]"

  obtain f where F: "gatherYulFunctions (r_funs res) ls = Inl f"
    using HP[OF Hres] by auto

  have Hres' : "P (res\<lparr>r_funs := r_funs res\<rparr>)" using Hres by auto

  have Hyp : "P (res\<lparr>r_funs := f, r_funs := r_funs res\<rparr>) \<and>
                 Inl (r_funs (res\<lparr>r_funs := f\<rparr>)) = gatherYulFunctions (r_funs res) ls"
    using Hres' F 
    by(simp del: gatherYulFunctions.simps)

  hence Hyp' : "\<exists> fns . P (res\<lparr>r_funs := f, r_funs := fns\<rparr>) \<and>
                 Inl (r_funs (res\<lparr>r_funs := f\<rparr>)) = gatherYulFunctions fns ls"
    by blast

  obtain n1 st1 where
    "evalYul' D
      \<lparr>result = res\<lparr>r_funs := f\<rparr>,
         cont = map EnterStatement ls\<rparr>
      n1 =
     YulResult st1 \<and>
     Q (result st1) \<and> cont st1 = []"
    using HTE'[OF H Hyp' refl]
    by blast

  hence Eval1 : "evalYul' D
      \<lparr>result = res\<lparr>r_funs := f\<rparr>,
         cont = map EnterStatement ls\<rparr>
      n1 =
     YulResult st1"
    and Q1 : "Q (result st1)"
    and Cont1 : "cont st1 = []"
    by auto

  show "\<exists>n st'.
          evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult st' \<and>
          (\<exists>funs' locals'.
              Q ((result st') \<lparr>r_funs := funs', r_locals := locals'\<rparr>) \<and>
              (\<forall>st0. P st0 \<longrightarrow> r_funs (result st') = r_funs st0 \<and> r_locals (result st') = restrict (r_locals (result st')) (r_locals st0))) \<and>
          cont st' = []"
  proof(cases "evalYulStep D \<lparr>result = res, cont = contn\<rparr>")
    (* idea: if we error here it must either be due to an error inside the block
       (but this would show up in Eval1 as well, contradiction) or we can't compute
       the new function context (but this contracticts F) *)
    case (ErrorResult msg bad)

    then have False
      using Hcontn F by(simp split: YulMode.splits sum.splits add: updateResult_def)

    thus ?thesis by auto
  next

    case (YulResult st2)

    obtain cont2 res2 where St2 : "st2 = \<lparr> result = res2, cont = cont2 \<rparr>"
      by(cases st2; auto)

    show ?thesis
    proof(cases "r_mode res")
      case Regular
      then show ?thesis 
        sorry
      next

        (* the idea here is that we are going to
           skip the entire block, then take another step
                   *)
      case Break

      (* NB this is a weird way to express being "done" - for non-Regular operation it means
         "is about to crash". I think this might actually be OK though. *)
      have Done : "cont2 = []" using Break St2 YulResult Hcontn
        by(auto)

      have Conc_Mid : True sorry

(* ok, this should hopefully be fine. 
   after 1 step we will reach the same place. hopefully...
*)
      show ?thesis sorry
    next
      case Continue
      then show ?thesis sorry
    next
      case Leave
      then show ?thesis sorry
    qed


    have Res2 : "res2 = (res \<lparr> r_funs := f \<rparr>)"
      using Hcontn F St2 YulResult 
      apply(simp split: YulMode.splits sum.splits add: updateResult_def)

    using HTE'[OF H, of "(res \<lparr> r_funs := f \<rparr>)"
                        "map EnterStatement ls"]
*)
(*
idea: want P in conclusion to just be P

** relationship between funs/funs' and locals/locals' is backwards. **

want P1 to be P after enriching context and functions

want Q1 to be whatever it needs to be (?)

want Q to be restriction of Q1

*)
    
(*
proof(induction t)
  case Nil

  show ?case
  proof(rule HTI)
    fix st1
    assume "P1 st1 \<and> cont st1 = [EnterStatement h]"
    hence Hp1 : "P1 st1" and Hcont1 : "cont st1 = [EnterStatement h]"
      by auto

    obtain st2 where Hp2 : "P2 st2" and Hcont2 : "cont st2 = []"
      using HTE'[OF H1 Hp1 Hcont1] by auto

    obtain st3 where Hp3 : "P3 st3" and Hcont3 : "cont st3 = []"
      using HTE'[OF H2 Hp2]

    show "\<exists>n st'.
             evalYul' D st n = YulResult st' \<and>
             P3 st' \<and> cont st' = []"
next
  case (Cons a t)
  then show ?case sorry
qed
*)

(* lemmas for block cons/nil 
    idea:
    {P} (map EnterStatement sl) {Q} \<Longrightarrow>
    {P}  {Q}
*)

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