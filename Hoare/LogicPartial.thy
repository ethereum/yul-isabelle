theory LogicPartial imports "../Yul/YulSemanticsSingleStep"
begin

(*
 * An implementation of Hoare logic for partial correctness,
 * for use with the Yul semantics
 *)

(*
 * This is our "lowest-level" notion of Hoare triples - it avoids mentioning
 * syntax at all; predicates can talk freely about the continuation stack
 *)
definition YulSteps ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
  (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   (('g, 'v, 't) result \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ % {_} {_}")
  where
"YulSteps D P Q =
  (\<forall> st n st' . P (st) \<longrightarrow>
   evalYul' D st n = YulResult st' \<longrightarrow>
   cont st' = [] \<longrightarrow>
   Q st')"

lemma HTI [intro]:
  assumes
    "\<And> st n st' . P st \<Longrightarrow> 
      evalYul' D st n = YulResult st' \<Longrightarrow>
      cont st' = [] \<Longrightarrow>
     Q st'"
  shows "D % {P} {Q}" using assms
  unfolding YulSteps_def 
  by auto

lemma HTE [elim]:
  assumes H : "D%{P} {Q}"
  assumes HP : "P st"
  assumes Heval : "evalYul' D st n = YulResult st'"
  assumes Hhalt : "cont st' = []"
  
  shows "Q st'"
  using assms unfolding YulSteps_def by auto

(* Consequence rule *)
lemma HT_conseq :
  assumes H : "D%{P} {Q}"
  assumes HP : "\<And> st . P' st \<Longrightarrow> P st"
  assumes HQ : "\<And> st . Q st \<Longrightarrow> Q' st"
  shows "D%{P'} {Q'}"
proof
  fix st n st'
  assume P' : "P' st"
  hence P : "P st" using HP by auto

  assume Eval : "evalYul' D st n = YulResult st'"
  assume Done : "cont st' = []"

  have Q : "Q st'" using HTE[OF H P Eval Done] by auto

  show "Q' st'" using HQ[OF Q] by auto
qed

(* Some lemmata useful for composing parts of executions of the Yul interpreter *)
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

(* characterize successfully halted states *)
definition is_halted :: "('g, 'v, 't) result \<Rightarrow> bool" where
"is_halted r = (cont r = [] \<and> mode r = Regular)"


(*
 * Some helper lemmas describing the evolution of the continuation stack as
 *  Yul executes
*)

(* "each step, we remove the first element of cont and add a prefix" *)
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
      by(cases st; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Break
      by(cases st; auto simp add: updateResult_def YulStatement.split_asm)
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
      by(cases st; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Continue
      by(cases st; auto simp add: updateResult_def split: YulResult.splits option.splits)
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
      by(cases st; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement st L F)
    then show ?thesis using assms Leave
      by(cases st; auto simp add: updateResult_def split: YulResult.splits option.splits)
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

(* If we do not crash after n steps, we did not crash at any point before n steps
   (in other words, we can't "un-crash") *)
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

(* Each step's behavior depends only on the first element of the continuation stack *)
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
      by(cases "r_vals r"; auto simp add: updateResult_def split: YulResult.splits option.splits)
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
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Break Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Break Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  qed
next
  case Continue
  then show ?thesis  using Hstep
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Continue Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Continue Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  qed
next
  case Leave
  then show ?thesis  using Hstep
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Leave Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Leave Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  qed
qed

(* If a step fails, this failure was caused by the first element of the continuation stack *)
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
      by(cases "r_vals r"; auto simp add: updateResult_def split: YulResult.splits option.splits)
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
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Break Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Break Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Break Hstep
      by(auto split: YulStatement.split_asm)
  qed
next
  case Continue
  then show ?thesis  using Hstep
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Continue Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Continue Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Continue Hstep
      by(auto split: YulStatement.split_asm)
  qed
next
  case Leave
  then show ?thesis  using Hstep
  proof(cases h)
    case (EnterStatement x1)
    then show ?thesis using Leave Hstep
      by(cases x1; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (ExitStatement x21 x22 x23)
    then show ?thesis using Leave Hstep
      by(cases x21; auto simp add: updateResult_def split: YulResult.splits option.splits)
  next
    case (EnterFunctionCall x31 x32)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (ExitFunctionCall x41 x42 x43 x44 x45)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  next
    case (Expression x5)
    then show ?thesis using Leave Hstep
      by(auto split: YulStatement.split_asm)
  qed
qed

(* If we fail for some n, we will fail for greater n
   (another expression of "can't un-crash"; possibly the contrapositive of
   evalYul'_step_succeed_prior *)
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

(* If we have halted, further steps taken will not change the state *)
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
  
(* Existence of a minimal number of steps to reach halting *)
lemma evalYul'_minsteps :
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


(* "If we're not done evaluating, what's in the tail doesn't matter"
   (if we are done evaluating, it may matter since this will cause a crash
   if we are not in Regular mode)
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

(*
 * A generalized sequencing rule for evalYul'.
 * If we run one continuation stack c1 for n1 steps, getting back a result r2 and a residue
 * (remaining continuation stack), and running the residue appended with a suffix c2,
 * for n2 steps, and the resulting computation halts,
 * then running (c1 @ c2) for (n1 + n2) steps has the same result
 *)
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

(* setting residue to [] in the above gets us a more standard rule about sequencing
   two halting computations *)
lemma evalYul'_seq :
  assumes H1 : "evalYul' D \<lparr>result = r1, cont = c1\<rparr> n1 = 
               YulResult \<lparr>result = r2, cont = []\<rparr>"
  assumes H2 : "evalYul' D \<lparr>result = r2, cont = c2 \<rparr> n2 = YulResult \<lparr> result = r3, cont = [] \<rparr>"
  shows "evalYul' D \<lparr> result = r1, cont = c1 @ c2\<rparr> (n1 + n2) = YulResult \<lparr> result = r3, cont = [] \<rparr>" 
  using evalYul'_seq_gen[of D r1 c1 n1 r2 "[]" c2 n2 r3] H1 H2
  by auto

(* A more familiar-looking Hoare logic of statements - but showing its relationship to the
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
       {(\<lambda> st . Q (result st))})"

(* A slightly lower-level version of these triples, talking about the continuation stack
 * directly rather than a single command
 *)
abbreviation YulStepsStackEls ::
  "('g, 'v, 't) YulDialect \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   ('g, 'v, 't) StackEl list \<Rightarrow>
   (('g, 'v, 't) result' \<Rightarrow> bool) \<Rightarrow>
   bool" 
("_ %* {_} _ {_}") where
"(D %* {P} els {Q}) \<equiv>
  (D % {(\<lambda> st . P (result st) \<and> cont st = els)}
       {(\<lambda> st . Q (result st))})"

lemma stackEls_sem_nil :
  shows "D %* {P} [] {P}"
  unfolding YulSteps_def
  by auto

(* Often it will be helpful for us to separate result and cont
 * when reasoning about Hoare triples (e.g. when using the above abbreviations)
 *)
lemma HTI' [intro]:
  assumes H :
    "\<And> res contn n st'. P1 res \<Longrightarrow> P2 contn \<Longrightarrow>
      evalYul' D \<lparr>result = res, cont = contn \<rparr> n = YulResult st' \<Longrightarrow>
      cont st' = [] \<Longrightarrow>
      Q st'"
  shows "D % {(\<lambda> st . P1 (result st) \<and> P2 (cont st))} {Q}" 
proof
  fix st st' :: "('a, 'b, 'c) result"
  fix n
  assume Assm : "P1 (result st) \<and> P2 (cont st)"
  assume Exec : "evalYul' D st n = YulResult st'"
  assume Done : "cont st' = []"

  show "Q st'" using H Assm Exec Done
    by(cases st; auto)
qed

(* a similar theorem to bisect, letting us talk about the tail of
   a larger execution *)
lemma evalYul'_subtract :
  assumes H : "evalYul' D st1 n = YulResult st2"
  assumes Htl : "evalYul' D st1 n' = YulResult st3"
  assumes Hleq : "n \<le> n'"
  shows "evalYul' D st2 (n' - n) = YulResult st3" using assms
proof(induction n' arbitrary: st1 st2 n st3)
  case 0
  then show ?case 
    by(auto)
next
  case (Suc nx)

  obtain res1 cont1 where St1 : "st1 = \<lparr> result = res1, cont = cont1 \<rparr>"
    by(cases st1; auto)

  then show ?case 
  proof(cases cont1)
    case Nil

    have Eq3 : "st3 = st1"
      using Suc St1 Nil by(auto)

    have Eq2 : "st2 = st1"
      using Suc St1 Nil by(cases n; auto)

    hence Cont2 : "cont st2 = []" using Nil St1 by auto

    show ?thesis 
    proof(cases "evalYul' D st2 (Suc nx - n)")
      case (ErrorResult msg bad)

      have False using evalYul'_steps[OF Suc.prems(1) ErrorResult] Suc.prems by auto

      thus ?thesis using ErrorResult by auto
    next
      case (YulResult fin)

      have "st3 = fin"
        using evalYul'_steps[OF Suc.prems(1) YulResult] Suc.prems
        by auto

      thus ?thesis using YulResult by auto
    qed
  next
    case (Cons c1h c1t)
    show ?thesis
    proof(cases "evalYul' D st1 1")
      case (ErrorResult msg bad)

      then have False using evalYul'_pres_fail[OF ErrorResult, of "Suc nx"] Suc
        by auto

      thus ?thesis by auto
    next
      case (YulResult st1')

      hence YR_step : "evalYulStep D st1 = YulResult st1'" using St1 Cons
        by(cases "evalYulStep D \<lparr>result = res1, cont = c1h # c1t\<rparr>"; auto simp del: evalYulStep.simps)

      have Rest : "evalYul' D st1' nx = YulResult st3" using YR_step Suc.prems(2) Cons St1
        by(auto simp del: evalYulStep.simps)

      show ?thesis
      proof(cases n)
        case Zero' : 0
        then show ?thesis using Suc.prems by auto
      next
        case Suc' : (Suc ny)

        have Rest' : "evalYul' D st1' ny = YulResult st2" using YR_step Suc.prems(1) Cons St1 Suc'
          by(auto simp del: evalYulStep.simps)

        have NyNx :  "ny \<le> nx" using Suc Suc' by auto

        then show ?thesis using Suc.IH[OF Rest' Rest NyNx] Suc.prems Suc'
          by auto
      qed
    qed
  qed
qed


lemma HTE' [elim]:
  assumes H : "D%{(\<lambda> st . P1 (result st) \<and> P2 (cont st))} {Q}"
  assumes HP1 : "P1 res"
  assumes HP2 : "P2 contn"
  assumes Hexec : "evalYul' D \<lparr> result = res, cont = contn \<rparr> n = YulResult st'"
  assumes Hdone : "cont st' = []"
  shows "Q st'"
  using HTE[OF H _ Hexec Hdone] HP1 HP2
  by(auto)

(* "Bisect" an evaluation of a smaller piece *)
lemma evalYul'_bisect' :
  assumes H : "evalYul' D \<lparr> result = r1, cont = c1@d1 \<rparr> n = YulResult \<lparr> result = r3, cont = [] \<rparr>"
  shows "\<exists>  n'  . n' = (LEAST X . \<exists> r2 .  evalYul' D \<lparr> result = r1, cont = c1@d1 \<rparr> X = YulResult \<lparr> result = r2, cont = d1 \<rparr>) \<and>
                  n' = (LEAST X . \<exists> r2 . evalYul' D \<lparr> result = r1, cont = c1 \<rparr> X = YulResult \<lparr> result = r2, cont = [] \<rparr>) \<and>
                  (\<exists> r2 .   evalYul' D \<lparr> result = r1, cont = c1@d1 \<rparr> n' = YulResult \<lparr> result = r2, cont = d1 \<rparr> \<and>
                            evalYul' D \<lparr> result = r1, cont = c1 \<rparr> n' = YulResult \<lparr> result = r2, cont = [] \<rparr>)"
  using H
proof(induction n arbitrary: r1 c1 d1 r3)
  case 0
  then show ?case 
    by(auto)
next
  case (Suc n)
  then show ?case 
  proof(cases c1)
    case Nil

    then show ?thesis using  Suc.prems by(simp)
  next

    case (Cons c1h c1t)

    obtain result1' where Eval1 :
      "evalYulStep D \<lparr>result = r1, cont = c1h # c1t @ d1\<rparr> = YulResult result1'"
      using Suc.prems Cons
      by(cases "evalYulStep D \<lparr>result = r1, cont = c1h # c1t @ d1\<rparr>"; auto simp del: evalYulStep.simps )

    obtain r1' c1' where Result1' : "result1' = \<lparr> result = r1', cont = c1' \<rparr>" by(cases result1'; auto)

    have EvalRest : "evalYul' D result1' n = YulResult \<lparr> result = r3, cont = [] \<rparr>"
      using Eval1 Cons  Suc.prems
      by(auto simp del: evalYulStep.simps)

    obtain c1'pre where C1' : "c1' = c1'pre @ c1t @ d1"
      using evalYulStep_cont_prefix_reg[OF _ Eval1, of c1h "c1t @ d1"] Result1'
      by(auto)

    show ?thesis
    proof(cases "evalYulStep D \<lparr>result = r1, cont = c1h # c1t \<rparr>")
      case (ErrorResult x21 x22)

      then have False using Eval1 Result1'
          evalYulStep_cont_extend_fail[OF ErrorResult] 
          evalYulStep_cont_extend[of D r1 c1h "c1t @ d1" r1' c1']
        by(auto simp del: evalYulStep.simps)

      thus ?thesis by auto
    next
      case (YulResult ressub)

      obtain rs1 rc1 where Ressub : "ressub = \<lparr> result = rs1, cont = rc1 \<rparr>"
        by(cases ressub; auto)

      have Rs1 : "rs1 = r1'"
        using evalYulStep_cont_extend[of D r1 c1h "c1t @ d1" r1' c1']
              evalYulStep_cont_extend[of D r1 c1h "c1t" rs1 rc1]
              Eval1 Result1' YulResult Ressub
        by(auto simp del: evalYulStep.simps)

      have Rc1 : "rc1 = c1'pre @ c1t"
        using evalYulStep_cont_extend[of D r1 c1h "c1t @ d1" r1' c1']
              evalYulStep_cont_extend[of D r1 c1h "c1t" rs1 rc1]
              Eval1 Result1' YulResult Ressub C1'
        by(auto simp del: evalYulStep.simps)

      have EvalRest' : "evalYul' D \<lparr> result = r1', cont = (c1'pre@c1t)@d1 \<rparr> n =
        YulResult \<lparr> result = r3, cont = [] \<rparr>"
        using EvalRest unfolding C1' Result1' by auto
  
      obtain r2 n' where
        EvalLeast1 : "n' = (LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) @ d1\<rparr> X = YulResult \<lparr>result = r2, cont = d1\<rparr>)" and
        EvalLeast2 : "n' = (LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) \<rparr> X = YulResult \<lparr>result = r2, cont = []\<rparr>)" and
        EvalBisect : "evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) @ d1\<rparr> n' = YulResult \<lparr>result = r2, cont = d1\<rparr>" and
        EvalBisect_Sub : "evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t)\<rparr> n' = YulResult \<lparr>result = r2, cont = []\<rparr>"
        using Suc.IH[OF EvalRest'] by blast
  
      have evalYul'1 : "evalYul' D \<lparr>result = r1, cont = c1h # c1t @ d1\<rparr> 1 = YulResult \<lparr> result = r1', cont = c1' \<rparr>"
        using Eval1 Result1'
        by(auto)
  
      have EvalFullBisect : "evalYul' D \<lparr> result = r1, cont = c1h # c1t @ d1 \<rparr> (1 + n') = YulResult \<lparr> result = r2, cont = d1 \<rparr>"
        using evalYul'_steps[OF evalYul'1, of n' "YulResult \<lparr>result = r2, cont = d1\<rparr>"] EvalBisect
        unfolding C1' Result1'
        by auto

      have evalYul'Sub1 : "evalYul' D \<lparr>result = r1, cont = c1h # c1t \<rparr> 1 = YulResult \<lparr> result = r1', cont = rc1 \<rparr>"
        using YulResult Ressub Rs1 Rc1
        by auto
  
      have EvalFullBisect_Sub : "evalYul' D \<lparr> result = r1, cont = c1h # c1t \<rparr> (1 + n') = YulResult \<lparr> result = r2, cont = [] \<rparr>"
        using evalYul'_steps[OF evalYul'Sub1, of n' "YulResult \<lparr>result = r2, cont = []\<rparr>"] EvalBisect_Sub
        unfolding Rs1 Rc1
        by auto

(*
      have Least1 : "\<And> m r2 . evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> m = YulResult \<lparr>result = r2, cont = d1\<rparr> \<Longrightarrow>
        1 + n' \<le> m"
*)
      have C1 : "(LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> X = YulResult \<lparr>result = r2, cont = d1\<rparr>) = 1 + n'"
      proof(rule Least_equality)
        show "\<exists>r2. evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> (1 + n') = YulResult \<lparr>result = r2, cont = d1\<rparr>" using EvalFullBisect unfolding Cons append.simps by blast
      next
        fix y
        assume H : "\<exists>r2. evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> y = YulResult \<lparr>result = r2, cont = d1\<rparr>"
        then obtain s2 where H' : "evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> y = YulResult \<lparr>result = s2, cont = d1\<rparr>" by blast

        obtain y' where Y' : "y = Suc y'"
          using H' unfolding Cons append.simps
          by(cases y; auto)

        show "1 + n' \<le> y"
        proof(cases "1 + n' \<le> y")
          case True
          then show ?thesis by auto
        next
          case False
          hence Ylt : "y < Suc n'" by auto
          hence Y'lt : "y' < n'" using Y' by auto
          hence Y'leq : "y' \<le> n'" using Y' by auto

          (*have YEval1 : "evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) @ d1\<rparr> y' = YulResult \<lparr>result = s2, cont = d1\<rparr>"*)
          show ?thesis
          proof(cases "evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) @ d1\<rparr> y'")
            case (ErrorResult msg bad)

            have False using EvalBisect evalYul'_pres_fail[OF ErrorResult Y'leq] by auto
            thus ?thesis by auto
          next
            case YRY : (YulResult resy)

            have EvalY : "evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> y = YulResult resy" 
                  and EvalY_res : "resy = \<lparr>result = s2, cont = d1\<rparr>"
              using evalYul'_steps[OF evalYul'1, of y' "YulResult resy"] YRY H'
              unfolding Y' C1' Cons append.simps
              by auto

            have "n' \<le> y'" unfolding EvalLeast1
            proof(rule Least_le)
              show "\<exists>r2. evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t) @ d1\<rparr> y' = YulResult \<lparr>result = r2, cont = d1\<rparr>"
                using YRY unfolding EvalY_res  by blast
            qed

            hence False using Y'lt by auto

            thus ?thesis by auto
          qed
        qed
      qed

      have C2 : "(LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1, cont = c1\<rparr> X = YulResult \<lparr>result = r2, cont = []\<rparr>) = 1 + n'"
      proof(rule Least_equality)
        show "\<exists>r2. evalYul' D \<lparr>result = r1, cont = c1\<rparr> (1 + n') = YulResult \<lparr>result = r2, cont = []\<rparr>" using EvalFullBisect_Sub unfolding Cons append.simps by blast
      next
        fix y
        assume H : "\<exists>r2. evalYul' D \<lparr>result = r1, cont = c1\<rparr> y = YulResult \<lparr>result = r2, cont = []\<rparr> "
        then obtain s2 where H' : "evalYul' D \<lparr>result = r1, cont = c1\<rparr> y = YulResult \<lparr>result = s2, cont = []\<rparr>" by blast

        obtain y' where Y' : "y = Suc y'"
          using H' unfolding Cons append.simps
          by(cases y; auto)

        show "1 + n' \<le> y"
        proof(cases "1 + n' \<le> y")
          case True
          then show ?thesis by auto
        next
          case False
          hence Ylt : "y < Suc n'" by auto
          hence Y'lt : "y' < n'" using Y' by auto
          hence Y'leq : "y' \<le> n'" using Y' by auto

          show ?thesis
          proof(cases "evalYul' D \<lparr>result = r1', cont = (c1'pre @ c1t)\<rparr> y'")
            case (ErrorResult msg bad)

            have False using EvalBisect_Sub evalYul'_pres_fail[OF ErrorResult Y'leq] by auto
            thus ?thesis by auto
          next
            case YRY : (YulResult resy)

            have EvalY : "evalYul' D \<lparr>result = r1, cont = c1 \<rparr> y = YulResult resy" 
                  and EvalY_res : "resy = \<lparr>result = s2, cont = []\<rparr>"
              using evalYul'_steps[OF evalYul'Sub1, of y' "YulResult resy"] YRY H'
              unfolding Y' C1' Cons append.simps Rc1
              by auto

            have "n' \<le> y'" unfolding EvalLeast2
            proof(rule Least_le)
              show "\<exists>r2. evalYul' D \<lparr>result = r1', cont = c1'pre @ c1t\<rparr> y' = YulResult \<lparr>result = r2, cont = []\<rparr>"
                using YRY unfolding EvalY_res  by blast
            qed

            hence False using Y'lt by auto

            thus ?thesis by auto
          qed
        qed
      qed

      show ?thesis
      proof(rule exI[of _ "1 + n'"]; step+)
        show "1 + n' = (LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> X = YulResult \<lparr>result = r2, cont = d1\<rparr>)" using sym[OF C1] by blast
      next
        show "1 + n' = (LEAST X. \<exists>r2. evalYul' D \<lparr>result = r1, cont = c1\<rparr> X = YulResult \<lparr>result = r2, cont = []\<rparr>)" using sym[OF C2] by blast
      next
        show "\<exists>r2. evalYul' D \<lparr>result = r1, cont = c1 @ d1\<rparr> (1 + n') = YulResult \<lparr>result = r2, cont = d1\<rparr> \<and> 
                    evalYul' D \<lparr>result = r1, cont = c1\<rparr> (1 + n') = YulResult \<lparr>result = r2, cont = []\<rparr>"
          using EvalFullBisect EvalFullBisect_Sub unfolding Cons append.simps by blast
      qed
    qed
  qed
qed


lemma evalYul'_bisect :
  assumes H : "evalYul' D \<lparr> result = r1, cont = c1@d1 \<rparr> n = YulResult \<lparr> result = r3, cont = [] \<rparr>"
  shows "\<exists> r2 n'  . evalYul' D \<lparr> result = r1, cont = c1@d1 \<rparr> n' = YulResult \<lparr> result = r2, cont = d1 \<rparr> \<and>
                      evalYul' D \<lparr> result = r1, cont = c1 \<rparr> n' = YulResult \<lparr> result = r2, cont = [] \<rparr>"
  using assms evalYul'_bisect' by blast

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


lemma HBlock :

  assumes H : "D %* {P} 
                    (map EnterStatement ls :: ('g, 'v, 't) StackEl list) 
                    {(\<lambda> st . Q (st \<lparr> r_funs := orig_funs
                                   , r_locals := restrict (r_locals st) orig_locals
                                   , r_vals := [] \<rparr>))}"
  shows "D % {(\<lambda> st . r_locals st = orig_locals \<and>
                      r_funs st = orig_funs \<and>
                      r_vals st = [] \<and>
                      gatherYulFunctions (r_funs st) ls = Inl f \<and>
                      P (st \<lparr> r_funs := f \<rparr> ))}
              YulBlock (ls )
              {Q}"
proof
  fix res contn n st'

  assume "r_locals res = orig_locals \<and>
       r_funs res = orig_funs \<and>
       r_vals res = [] \<and>
       gatherYulFunctions (r_funs res) ls = Inl f \<and> P (res\<lparr>r_funs := f\<rparr>)"

  hence Locals : "r_locals res = orig_locals" and
        Funs : "r_funs res = orig_funs" and
        Gather : "gatherYulFunctions (r_funs res) ls = Inl f" and
        HP : "P (res\<lparr>r_funs := f\<rparr>)" and
        Vals : "r_vals res = []"
    by auto

  assume Contn : "contn = ([EnterStatement (YulBlock ls)] :: ('g, 'v, 't) StackEl list)"

  assume Exec : "evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult st'"
  assume Hdone : "cont st' = []"

  obtain res' where Res' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult \<lparr> result = res', cont = [] \<rparr>"
    using Exec Hdone by (cases st'; auto)

  show "Q (result st')"
  proof(cases "evalYulStep D \<lparr>result = res, cont = contn\<rparr>")
    case (ErrorResult x21 x22)

    then show ?thesis using Exec Contn Gather
     by(cases "r_mode res";  simp add: updateResult_def) 
  next
    case (YulResult st2)

    have YulResult_alt : 
      "evalYul' D \<lparr>result = res, cont = contn\<rparr> 1 = 
          YulResult \<lparr>result = res\<lparr>r_funs := f\<rparr>
                    , cont = map EnterStatement ls @ [ExitStatement (YulBlock ls) (r_locals res)
                       (r_funs res)]\<rparr>"
      using YulResult Contn Gather
      by(cases "r_mode res"; auto simp add: updateResult_def)

    have Rest : 
      "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>
                    , cont = map EnterStatement ls @ [ExitStatement (YulBlock ls) (r_locals res)
                       (r_funs res)]\<rparr> (n) = YulResult \<lparr> result = res', cont = [] \<rparr>"
    proof(cases "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>
                    , cont = map EnterStatement ls @ [ExitStatement (YulBlock ls) (r_locals res)
                       (r_funs res)]\<rparr> (n)")
      case (ErrorResult msg bad)

      have False using evalYul'_pres_succeed[OF Exec Hdone, of "1 + n"]
          evalYul'_steps[OF YulResult_alt ErrorResult] by auto

      then show ?thesis by auto
    next
      case YulResult' : (YulResult st'_alt)

      have "evalYul' D \<lparr>result = res, cont = contn\<rparr> (1 + n) = YulResult st'_alt"
        using evalYul'_steps[OF YulResult_alt YulResult']
        by auto

      then have "st'_alt = st'"
        using evalYul'_pres_succeed[OF Exec, of "1 + n"] Hdone YulResult' by auto

      thus ?thesis using YulResult' using Res' Exec by auto
    qed

    obtain nl rl where
      Bisect1 : "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>
                    , cont = map EnterStatement ls @ [ExitStatement (YulBlock ls) (r_locals res)
                       (r_funs res)]\<rparr> nl = YulResult \<lparr> result = rl, cont = [ExitStatement (YulBlock ls) (r_locals res)
                       (r_funs res)] \<rparr> " and
      Bisect2 : "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls\<rparr> nl = YulResult \<lparr>result = rl, cont = []\<rparr>"
      using evalYul'_bisect[OF Rest ]
      by auto


    have LastStep : "evalYul' D \<lparr> result = rl, cont = [ExitStatement (YulBlock ls) (r_locals res)
                     (r_funs res)]\<rparr> 1 = YulResult st'"
    proof(cases "evalYul' D \<lparr> result = rl, cont = [ExitStatement (YulBlock ls) (r_locals res)
                     (r_funs res)]\<rparr> 1")
      case ErrorResult' : (ErrorResult msg bad)

      have False using evalYul'_steps[OF Bisect1 ErrorResult'] Rest
      proof(cases "nl + 1 \<le> n")
        case True
        then show ?thesis using evalYul'_pres_fail[OF evalYul'_steps[OF Bisect1 ErrorResult'] True] Rest by auto
      next
        case False

        have False_alt : "n \<le> nl + 1" using False by auto

        then show ?thesis using evalYul'_pres_succeed[OF Rest _ False_alt] evalYul'_steps[OF Bisect1 ErrorResult'] by auto
      qed

      then show ?thesis by auto
    next

      case YulResult'' : (YulResult st''_alt)

      have YulResult''_alt : "evalYul' D \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls @ [ExitStatement (YulBlock ls) (r_locals res) (r_funs res)]\<rparr> (nl + 1) = YulResult st''_alt"
        using evalYul'_steps[OF Bisect1 YulResult'']
        by auto

      have Cont_st''_alt : "cont st''_alt = []"
        using YulResult''
        by(cases "r_mode rl"; auto simp add: updateResult_def)

      then have St'_eq : "st''_alt = st'" 
        using evalYul'_steps[OF YulResult_alt YulResult''_alt] Exec
      proof(cases "1 + (nl + 1) \<le> n")
        case True
        then show ?thesis using evalYul'_pres_succeed[OF evalYul'_steps[OF YulResult_alt YulResult''_alt] _ True] Cont_st''_alt Exec by auto
      next
        case False

        have False_alt : "n \<le> 1 + (nl + 1)" using False by auto

        then show ?thesis using evalYul'_pres_succeed[OF Exec _ False_alt] evalYul'_steps[OF YulResult_alt YulResult''_alt] Hdone by auto
      qed

      then show ?thesis using YulResult'' unfolding St'_eq by auto
    qed

    have H_premise : "P (result \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls\<rparr>) \<and> cont \<lparr>result = res\<lparr>r_funs := f\<rparr>, cont = map EnterStatement ls\<rparr> = map EnterStatement ls"
      using HP by auto

    have Q1 : "Q (rl\<lparr>r_funs := r_funs res, r_locals := restrict (r_locals rl) (r_locals res), r_vals := []\<rparr>)"
      using HTE[OF H H_premise Bisect2]  Funs Locals HTE[OF H] 
      by( auto)

    have "rl\<lparr>r_funs := r_funs res, r_locals := restrict (r_locals rl) (r_locals res), r_vals := []\<rparr> = result st'"
      using LastStep  by(cases "r_mode rl"; auto simp add: updateResult_def)

    thus ?thesis using Q1 by auto
  qed
qed



lemma eval_funcall_mode :
  assumes H : "evalYul' D \<lparr> result = st, cont = [(Expression YUL_EXPR{ \<guillemotleft>name\<guillemotright>(\<guillemotleft>args\<guillemotright>) })] \<rparr> n = YulResult \<lparr> result = st', cont = [] \<rparr>"
  shows "r_mode st' = r_mode st" using H
proof(cases n)
  case 0
  then show ?thesis using H
    by auto
next
  case (Suc n')

  show ?thesis
  proof(cases "is_regular (r_mode st)")
    case False
    then show ?thesis using Suc H
      by(cases "r_mode st"; cases n'; auto)
  next
    case True

    hence Hreg : "r_mode st = Regular"
      by(cases "r_mode st"; auto)

    obtain fsig where Fsig : "map_of (r_funs st) name = Some fsig"
      using Suc H Hreg
      by(auto simp add: updateResult_def split: option.splits)
  
    have EvalStep : "evalYul' D \<lparr> result = st, cont = [(Expression YUL_EXPR{ \<guillemotleft>name\<guillemotright>(\<guillemotleft>args\<guillemotright>) })] \<rparr> 1 =
    YulResult (\<lparr> result = st
              , cont = ((map Expression (rev args) @ 
                        [EnterFunctionCall name fsig])@
                        [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig])\<rparr>)"
      using Fsig H Suc Hreg
      by(auto simp add: updateResult_def)
  
    have EvalRest :
      "evalYul' D (\<lparr> result = st
                 , cont = ((map Expression (rev args) @ 
                          [EnterFunctionCall name fsig])@
                          [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig])\<rparr>) n' =
        YulResult \<lparr> result = st', cont = [] \<rparr>"
      using Suc EvalStep H Hreg Fsig
      by(auto simp add: updateResult_def)
  
    obtain n'' r'' where
      EvalToExit :
      "evalYul' D (\<lparr> result = st
                 , cont = (map Expression (rev args) @ 
                          [EnterFunctionCall name fsig,
                           ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig])\<rparr>) n'' = 
        YulResult \<lparr> result = r'', cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig] \<rparr>"
      using evalYul'_bisect[OF EvalRest]
      by auto

    have InitToExit :
     "evalYul' D
         \<lparr>result = st, cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
         (1 + n'') =
        YulResult
         \<lparr>result = r'', cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig]\<rparr>" 
      using
        evalYul'_steps[OF EvalStep, of n'' "YulResult \<lparr> result = r'', 
                              cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig] \<rparr>"]
        EvalToExit
      by(auto simp del: evalYul'.simps)

    have ExitSucceed :
      "\<exists> resf . evalYul' D \<lparr>result = r'', cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig]\<rparr> 1 = 
        YulResult resf"
    proof(cases "evalYul' D \<lparr>result = r'', cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig]\<rparr> 1")
      case (ErrorResult msg rbad)

      have EvalBad :
      "evalYul' D
           \<lparr>result = st,
              cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
           (1 + n'' + 1) =
          ErrorResult msg rbad"
        using evalYul'_steps[OF InitToExit ErrorResult] by auto

      have False
      proof(cases "n < 1 + n'' + 1")
        case True
        then show ?thesis 
          using evalYul'_pres_succeed[OF H, of "1 + n'' + 1"] EvalBad
          by auto
      next
        case False
        then show ?thesis
          using evalYul'_pres_fail[OF EvalBad, of "n"] H by auto
      qed

      then show ?thesis by auto
    next
      case (YulResult rfin)

      then show ?thesis by auto
    qed

    then obtain resf where Resf :
      "evalYul' D \<lparr>result = r'', cont = [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig]\<rparr> 1 = 
        YulResult resf"
      by auto

    show ?thesis
    proof(cases "r_mode r''")
      case Break
      then show ?thesis using ExitSucceed by auto
    next
      case Continue
      then show ?thesis using ExitSucceed by auto
    next
      case Regular

      hence Resf_done : "cont resf = []" using Resf
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have Resf_mode : "mode resf = Regular" using Resf Regular
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have EvalGood :
      "evalYul' D
           \<lparr>result = st,
              cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
           (1 + n'' + 1) =
          YulResult resf"
        using evalYul'_steps[OF InitToExit Resf] by auto

      then show ?thesis 
      proof(cases "n < 1 + n'' + 1")
        case True
        then show ?thesis 
          using evalYul'_pres_succeed[OF H, of "1 + n'' + 1"] EvalGood Hreg Resf_mode
          by(auto)
      next
        case False
        then show ?thesis
          using evalYul'_pres_succeed[OF EvalGood, of "n"] H Hreg Resf_mode Resf_done
          by auto
      qed
    next
      case Leave

      hence Resf_almost_done : "cont resf = 
        [ExitFunctionCall name (r_vals st) (r_locals st) (r_funs st) fsig]" using Resf
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have Resf_mode : "mode resf = Regular" using Resf Leave
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have EvalGood :
      "evalYul' D
           \<lparr>result = st,
              cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
           (1 + n'' + 1) =
          YulResult resf"
        using evalYul'_steps[OF InitToExit Resf] by auto

(* TODO: this is a copy-paste of another part of the argument from above
   we should be able to streamline this.
*)
      have ExitSucceed2 :
        "\<exists> resf2 . evalYul' D resf 1 = 
          YulResult resf2"
      proof(cases " evalYul' D ( resf) 1")
        case (ErrorResult msg rbad)
  
        have EvalBad :
        "evalYul' D
             \<lparr>result = st,
                cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
             (1 + n'' + 2) =
            ErrorResult msg rbad"
          using evalYul'_steps[OF EvalGood ErrorResult] by auto
  
        have False
        proof(cases "n < 1 + n'' + 2")
          case True
          then show ?thesis 
            using evalYul'_pres_succeed[OF H, of "1 + n'' + 2"] EvalBad
            by auto
        next
          case False
          then show ?thesis
            using evalYul'_pres_fail[OF EvalBad, of "n"] H by auto
        qed
  
        then show ?thesis by auto
      next
        case (YulResult rfin)
  
        then show ?thesis by auto
      qed

      then obtain resf2 where Resf2 :
        "evalYul' D resf 1 = YulResult resf2"
        using Leave Resf ExitSucceed
        by(auto)

      have Resf2_reg : "mode resf2 = Regular"
        using Resf Resf2 Resf_mode ExitSucceed2 Resf_almost_done
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have Resf2_done : "cont resf2 = []"
        using Resf Resf2 Resf_mode ExitSucceed2  Resf_almost_done
        by(auto simp add: updateResult_def split: YulFunctionBody.splits list.splits option.splits)

      have EvalGood2 :
      "evalYul' D
           \<lparr>result = st,
              cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))]\<rparr>
           (1 + n'' + 1 + 1) =
          YulResult resf2"
        using evalYul'_steps[OF EvalGood Resf2] by auto

      then show ?thesis 
      proof(cases "n < 1 + n'' + 1 + 1")
        case True
        then show ?thesis 
          using evalYul'_pres_succeed[OF H, of "1 + n'' + 1"] EvalGood Hreg Resf_mode
          by(auto)
      next
        case False
        then show ?thesis
          using evalYul'_pres_succeed[OF EvalGood2, of "n"] H Hreg Resf2_reg Resf2_done
          by(auto)
      qed
    qed
  qed
qed
 

lemma eval_expression_mode :
  assumes H : "evalYul' D \<lparr> result = st, cont = [(Expression e)] \<rparr> n = YulResult \<lparr> result = st', cont = [] \<rparr>"
  shows "r_mode st' = r_mode st"
proof(cases e)
  case (YulFunctionCallExpression x1)

  obtain name args where H' : 
    "evalYul' D \<lparr> result = st, cont = [Expression (YulFunctionCallExpression (YulFunctionCall name args))] \<rparr> n = YulResult \<lparr> result = st', cont = [] \<rparr>"
    using H
    unfolding YulFunctionCallExpression
    by(cases x1; auto)

  show ?thesis 
    using eval_funcall_mode[OF H'] by auto
next
  case (YulIdentifier x2)
  then show ?thesis using H
    by(cases n; cases "r_mode st"; auto simp add: updateResult_def split:if_splits option.splits)
next
  case (YulLiteralExpression x3)
  then show ?thesis using H
    by(cases n; cases x3; cases "r_mode st"; auto simp add: updateResult_def split: if_splits )
qed


(* Convenience lemma: two successful, terminating executions will agree on state. *)
lemma evalYul'_agree_succeed :
  assumes H1 : "evalYul' D st n1 = YulResult \<lparr> result = st'1, cont = [] \<rparr>"
  assumes H2 : "evalYul' D st n2 = YulResult \<lparr> result = st'2, cont = [] \<rparr>"
  shows "st'1 = st'2"
proof(cases "n1 \<le> n2")
  case True
  then show ?thesis using evalYul'_pres_succeed[OF H1 _ True] H2 by auto
next
  case False

  hence False' : "n2 \<le> n1" by auto

  then show ?thesis using evalYul'_pres_succeed[OF H2 _ False'] H1 by auto
qed

lemma HIf :
  assumes Hc : "\<And> st . Qe st \<Longrightarrow> is_regular (r_mode st) \<Longrightarrow> \<exists> c . r_vals st = [c]"
  assumes HE : "D %* {P} ([Expression cond] :: ('g, 'v, 't) StackEl list) {Qe}"

  assumes HT: "D % {(\<lambda> st . \<exists> c . Qe (st \<lparr> r_vals := [c] \<rparr>) \<and> is_truthy D c)} (YulBlock body) {Q}"
  assumes HF : "\<And> c st . Qe (st) \<Longrightarrow> r_vals st =  [c] \<Longrightarrow> is_regular (r_mode st) \<Longrightarrow> \<not> is_truthy D c \<Longrightarrow>  
                Q (st \<lparr> r_vals := [] \<rparr>)"


  assumes HIrreg : "\<And> st . P st \<Longrightarrow> is_irregular (r_mode st) \<Longrightarrow> Q st"

  shows "D % {P} YulIf cond body {Q}"
proof
  fix res contn n st'

  assume HP  : "P res"
  assume Hcontn : "contn = ([EnterStatement (YulIf cond body)] :: ('g, 'v, 't) StackEl list)"

  assume Exec : "evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult st'"

  assume Done : "cont st' = []"

  obtain res' where Res' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult \<lparr> result = res', cont = [] \<rparr>"
    using Exec Done by (cases st'; auto)

  show "Q (result st')"
  proof(cases "evalYulStep D \<lparr>result = res, cont = contn\<rparr>")
    case (ErrorResult x21 x22)

    then show ?thesis using Exec Hcontn 
     by(cases "r_mode res";  simp add: updateResult_def) 
  next
    case (YulResult st2)

    show ?thesis
    proof(cases "cont st2")
      case Nil

      show ?thesis
      proof(cases "is_regular (r_mode res)")
        case Irreg : False

        have "st2 = \<lparr>result = res, cont = []\<rparr>" using YulResult Nil Irreg Hcontn
          by (cases "r_mode res"; auto)

        obtain n' where N' : "n = Suc n'" using  Nil Irreg Exec Hcontn Res'
          by(cases n; auto)

        have Eval1'_step : "evalYul' D \<lparr>result = res, cont = [Expression cond]\<rparr> 1 = YulResult \<lparr> result = res, cont = [] \<rparr>"
          using N' Exec Irreg
          by(cases "r_mode res"; auto)

        have Eval1' : "st' = \<lparr> result = res, cont = [] \<rparr>"
          using evalYul'_pres_succeed[OF Eval1'_step, of n] Exec N' Hcontn Irreg
          by(cases "r_mode res"; auto)

        (* TODO: we originally had an assumption about Qe implying Q. not sure which is better.
           i  think they are equivalent. but it is simpler this way; probably we can clean
           up this proof a bit here *)
        have Qres : "Q res" using HIrreg[OF HP] Irreg Eval1' by(auto)

        have EvalFull_step : "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulIf cond body)]\<rparr> 1 
          = YulResult \<lparr> result = res, cont = []\<rparr>"
          using YulResult Hcontn Irreg
          by(cases "r_mode res"; auto)

        have Conc' : "Q (result \<lparr> result = res, cont = []\<rparr>)"
          using Qres EvalFull_step Hcontn by auto

        thus ?thesis unfolding Eval1' by blast
      next
        case Reg : True

        hence Regular : "r_mode res = Regular" by(cases "r_mode res"; auto)

        (* contradiction: we are in Regular mode but threw away the entire computation. *)
        have False using YulResult Regular Hcontn Nil
          by(auto simp add: updateResult_def)

        thus ?thesis by auto
      qed
    next
      case (Cons cont2h cont2t)

      show ?thesis
      proof(cases "is_regular (r_mode res)")
        case Irreg : False

        (* contradiction: we should have thrown away the computation but didn't. *)
        have False using YulResult Irreg Hcontn Cons
          by(cases "r_mode res"; auto simp add: updateResult_def)

        thus ?thesis by auto
      next
        case Reg : True

        hence Regular : "r_mode res = Regular" by(cases "r_mode res"; auto)

        (* the "happy-path" case.
           idea here is that we run the expression, then (if applicable) the body
        *)

        have EvalFull_step1 :
          "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulIf cond body)]\<rparr> 1 
            = YulResult \<lparr> result = res, cont = [Expression cond, ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]\<rparr>"
          using Regular
          by(auto simp add: updateResult_def)

        obtain n' where N' : "n = Suc n'" using Exec Hcontn Done by (cases n; auto)

        have EvalFull_rest :
          "evalYul' D \<lparr> result = res, cont = [Expression cond, ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]\<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"
          using evalYul'_subtract[OF EvalFull_step1, of n st'] Exec Res' unfolding N' Hcontn
          by(auto simp del: evalYul'.simps)

        hence EvalFull_rest_alt : "evalYul' D \<lparr> result = res, cont = [Expression cond] @ [ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]\<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"
          by simp

        obtain n1 res1 where
          Res1 : "evalYul' D \<lparr> result = res, cont = [Expression cond, ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]  \<rparr> n1 =
            YulResult \<lparr> result = res1, cont = [ExitStatement (YulIf cond body) (r_locals res) (r_funs res)] \<rparr>" and
          Res1_sub : "evalYul' D \<lparr> result = res, cont = [Expression cond] \<rparr> n1 = 
            YulResult \<lparr> result = res1, cont = [] \<rparr>"
          using evalYul'_bisect[OF EvalFull_rest_alt] by auto

        have Qe : "Qe (res1)" using HTE[OF HE _ Res1_sub] HP by auto

        have Res1_reg : "is_regular (r_mode res1)"
          using eval_expression_mode[OF Res1_sub] Reg by auto

        obtain c where C: "r_vals res1 = [c]"
          using Hc[OF Qe Res1_reg] by auto

        show ?thesis
        proof(cases "is_truthy D c")
          case False

          have Qst1 : "Q ((res1 \<lparr>r_vals := []\<rparr>))" using HF[OF Qe]
              False Res1_reg Qe C 
            by(cases res1; auto) 

          have EvalFull_step3 :
            "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]\<rparr> 1 =
              YulResult \<lparr> result = (res1 \<lparr> r_vals := [] \<rparr>), cont = [] \<rparr>"
            using Regular Res1_reg C False
            by(auto simp add: updateResult_def)

          have EvalFull_steps23 :
            "evalYul' D \<lparr>result = res, cont = [Expression cond, ExitStatement (YulIf cond body) (r_locals res) (r_funs res)] \<rparr> (n1 + 1) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = []\<rparr>)"
            using evalYul'_seq[OF Res1_sub EvalFull_step3] 
            by auto

          have EvalFull_steps123 :
            "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulIf cond body)]\<rparr> (1 + (n1 + 1)) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = [] \<rparr>)"
            using evalYul'_steps[OF EvalFull_step1 EvalFull_steps23] by auto

          have Res1_eq : "(res1 \<lparr> r_vals := [] \<rparr> = result st')"
            using evalYul'_agree_succeed[OF EvalFull_steps123, of n res'] Res' Hcontn Exec
            by auto
            
          thus ?thesis using Qst1 by auto
        next
          case True

          have EvalFull_step3 :
            "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulIf cond body) (r_locals res) (r_funs res)]\<rparr> 1 =
              YulResult \<lparr> result = (res1 \<lparr> r_vals := [] \<rparr>), cont = [EnterStatement (YulBlock body)] \<rparr>"
            using Regular Res1_reg C True
            by(auto simp add: updateResult_def)

          have EvalFull_steps23 :
            "evalYul' D \<lparr>result = res, cont = [Expression cond, ExitStatement (YulIf cond body) (r_locals res) (r_funs res)] \<rparr> (n1 + 1) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = [EnterStatement (YulBlock body)]\<rparr>)"
            using evalYul'_steps[OF Res1 EvalFull_step3]
            by auto

          have EvalFull_steps123 :
            "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulIf cond body)]\<rparr> (1 + (n1 + 1)) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = [EnterStatement (YulBlock body)] \<rparr>)"
            using evalYul'_steps[OF EvalFull_step1 EvalFull_steps23] by auto

          have N_greater :
            "1 + (n1 + 1) \<le> n"
          proof(cases "1 + (n1 + 1) \<le> n")
            case True' : True
            thus ?thesis by auto
          next
            case False' : False

            hence Leq : "n \<le> 1 + (n1 + 1)" by auto

            have False 
              using evalYul'_pres_succeed[OF Res' _ Leq] Hcontn EvalFull_steps123 by auto 

            thus ?thesis by auto
          qed
          

          have EvalBody : "evalYul' D \<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = [EnterStatement (YulBlock body)] \<rparr> (n - (1 + (n1 + 1))) = 
            YulResult \<lparr> result = res', cont = [] \<rparr>"
            using evalYul'_subtract[OF EvalFull_steps123 _ N_greater, of " \<lparr> result = res', cont = [] \<rparr>" ] Res' Hcontn
            by auto


          have HT_prem1 : "\<exists>c. Qe ((result \<lparr>result = res1\<lparr>r_vals := []\<rparr>, cont = [EnterStatement (YulBlock body)]\<rparr>\<lparr>r_vals := [c]\<rparr>)) \<and> is_truthy D c"
          proof
            show "Qe ((result \<lparr>result = res1\<lparr>r_vals := []\<rparr>, cont = [EnterStatement (YulBlock body)]\<rparr>\<lparr>r_vals := [c]\<rparr>)) \<and> is_truthy D c" using Qe C True
              by(cases res1; auto)
          qed


          have "Q res'"
            using HTE[OF HT, of "\<lparr>result = res1\<lparr>r_vals := []\<rparr>, cont = [EnterStatement (YulBlock body)]\<rparr>" "(n - (1 + (n1 + 1)))" " \<lparr> result = res', cont = [] \<rparr>"]
            HT_prem1
            Qe C True N_greater EvalBody
            by(auto simp del: evalYul'.simps)

          thus ?thesis using Res' Exec by auto
        qed
      qed
    qed
  qed
qed

(*

for loop = pre, condition, post, body
--------------

Q start \<Longrightarrow>
Qp (after pre) \<Longrightarrow>
Qe (after condition) \<Longrightarrow>
Qd (after body) \<Longrightarrow>
Qp (after post) \<Longrightarrow>
Qf (after exit)

--------------

(* classic while loop rule: *)
{ P \<and> B } S {P} \<Longrightarrow>
{P} while B do S done {\<not> B \<and> P }

*)

(* 
v1. {P} (for {init}  {cond} {post} {body}) {Q}

v2. {P} (for {init} {cond}  {post} {body}) {\<not> B \<and> Q}

-- if there were no non-regular modes --

{P} init {Pi}

{Pi} cond {Pc}

Pc st \<Longrightarrow> vals st = [c]

\<not> is_truthy c \<Longrightarrow> Pi \<Longrightarrow> Pf (?)

is_truthy c \<Longrightarrow> {\<lambda> st . (Pc (st \<lparr> vals = [c] \<rparr>))} body {Pb}

{Pb} post {Pi}

then

{P} (for {init} {cond} {post} {body}) {Pf}


------

*)
lemma for_final_iteration':

assumes Hn' : "n' \<le> n"
assumes H: "evalYul' D \<lparr> result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"

shows "\<exists> nl resl c locs' funcs' .
          evalYul' D  \<lparr> result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> nl = YulResult \<lparr> result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs'] \<rparr> \<and>
          ((r_vals resl = [c] \<and> \<not> is_truthy D c \<and> r_mode resl = Regular) \<or>
           (r_mode resl = Break) \<or>
           (r_mode resl = Leave))" using assms
proof(induction n arbitrary: n' res res' cond post body locs funcs)
  case 0
  then show ?case by(auto)
next
  case (Suc n)
  show ?case
  proof(cases n')
    case 0
    then show ?thesis using Suc.prems by auto
  next
    case Suc' : (Suc n'1)

    show ?thesis
    proof(cases "r_mode res")
      case Break
      then show ?thesis using Suc.prems Suc'
          by(auto simp add: updateResult_def)
    next
      case Continue

      have Exec1 : "evalYul' D \<lparr> result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> 1 = 
        YulResult \<lparr> result = (res \<lparr> r_mode := Regular \<rparr>), cont = [EnterStatement (YulBlock post),
                               Expression cond,
                               ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>"
        using Continue
        by(auto)

      have Exec1' : "evalYul' D \<lparr> result = (res \<lparr> r_mode := Regular \<rparr>), cont = [EnterStatement (YulBlock post),
                               Expression cond,
                               ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (n'-1) = YulResult \<lparr> result = res', cont = [] \<rparr>"
        using evalYul'_subtract[OF Exec1 Suc.prems(2)] Suc' by auto

(* NB: the following is copy-pasted from the Regular case. *)

      hence Exec1'_alt : "evalYul' D
                    \<lparr>result = (res \<lparr> r_mode := Regular  \<rparr>),
                     cont = [EnterStatement (YulBlock post),
                            Expression cond] @
                            [ExitStatement (YulForLoop [] cond post body) locs funcs ]\<rparr>
                     (n' - 1) =
                     YulResult \<lparr> result = res', cont = [] \<rparr>" by simp

      obtain res1x n1x where 
          Exec1'' : 
          "evalYul' D
                    \<lparr>result = (res \<lparr> r_mode := Regular  \<rparr>),
                     cont = [EnterStatement (YulBlock post),
                             Expression cond,
                             ExitStatement (YulForLoop [] cond post body) (locs) (funcs)]\<rparr>
                     n1x =
                     YulResult \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (locs) (funcs)] \<rparr>"
           and Exec1''_sub : 
            "evalYul' D \<lparr>result = (res \<lparr> r_mode := Regular  \<rparr>),
                     cont = [EnterStatement (YulBlock post),
                            Expression cond ]\<rparr> n1x =  YulResult \<lparr> result = res1x, cont = [] \<rparr>"
        using evalYul'_bisect[OF Exec1'_alt] by auto          

      have Nlt : "n1x < n' - 1"
      proof(cases "n1x < n' - 1")
        case True
        then show ?thesis by auto
      next
        case False

        then have False' : "n' - 1 \<le> n1x" by auto

        hence False using evalYul'_pres_succeed[OF Exec1' _ False'] Exec1'' by auto

        thus ?thesis by auto
      qed

      hence Nleq : "n1x \<le> n' - 1" by auto

      have Exec1''' : 
      "evalYul' D \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (locs ) (funcs )] \<rparr> ((n' - 1) - n1x) =
        YulResult \<lparr> result = res', cont = [] \<rparr>"
        using evalYul'_subtract[OF Exec1'' Exec1' Nleq] by auto

      have Exec1Full :
        "evalYul' D \<lparr>result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + n1x) =
          YulResult \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (locs) (funcs )] \<rparr>"
        using evalYul'_steps[OF Exec1 Exec1''] by auto

      obtain n1x' where N1x': "n' - 1 - n1x = Suc n1x'"
        using Nlt
        by(cases "n' - 1 - n1x"; auto)

      have Nlt_x : "(n' - 1) - n1x \<le> n" using Suc' Suc.prems(1) Nlt
        by(simp)

      obtain nl resl c locs' funcs' where Execl :
          "evalYul' D \<lparr>result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (locs) (funcs)]\<rparr>
                nl =
               YulResult \<lparr>result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>" and
          SpecL : "(r_vals resl = [c] \<and> \<not> is_truthy D c \<and> r_mode resl = Regular \<or> r_mode resl = Break \<or> r_mode resl = Leave)"
        using Suc.IH[OF Nlt_x Exec1'''] by blast

      have Exec1L_Full : 
        "evalYul' D \<lparr>result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + n1x + nl) = 
          YulResult \<lparr>result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
        using evalYul'_steps[OF Exec1Full Execl] by auto

      show ?thesis using SpecL Exec1L_Full by blast        
    next
      case Leave
      then show ?thesis using Suc.prems Suc' Nil
        by(auto simp add: updateResult_def)
    next
      case Regular
  
      then show ?thesis
      proof(cases "r_vals res")
        case Nil

        then show ?thesis using Suc.prems Suc' Nil Regular
          by(auto simp add: updateResult_def)
      next

        case (Cons c vt)

        hence Vt : "vt = []" using Suc.prems Suc' Regular by(cases vt; auto simp add: updateResult_def)
  
        hence V : "r_vals res = [c]" using Cons by auto
  
        show ?thesis
        proof(cases "is_irregular (r_mode res)")
          case T_Irreg : True
          then show ?thesis using Regular by auto
        next
          case F_Irreg : False
          hence Reg : "r_mode res = Regular"
            by(cases "r_mode res"; auto)
  
          show ?thesis
          proof(cases "is_truthy D c")
            case F_Truthy : False
  
            have C1 : "evalYul' D
                        \<lparr>result = res,
                           cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
                        0 =
                       YulResult
                        \<lparr>result = res,
                           cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>"
              by auto
  
            have C2 : "(r_vals res = [c] \<and> \<not> is_truthy D c \<and> r_mode res = Regular)"
              using F_Truthy V Reg
              by auto
  
            show ?thesis using C1 C2 by auto
          next
            case T_Truthy : True
  
            have Exec1 : "evalYul' D
                          \<lparr>result = res,
                             cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
                          1 =
                       YulResult
                        \<lparr>result = (res \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )]\<rparr>"
              using Suc' Suc.prems T_Truthy Reg V
              by(auto simp add: updateResult_def)
  
            have Exec1' : "evalYul' D
                          \<lparr>result = (res \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )]\<rparr>
                           (n' - 1) =
                           YulResult \<lparr> result = res', cont = [] \<rparr>"
              using evalYul'_subtract[OF Exec1 Suc.prems(2)] Suc' 
              by(auto simp del: evalYul'.simps)
  
            hence Exec1'_alt : "evalYul' D
                          \<lparr>result = (res \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond] @
                                  [ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )]\<rparr>
                           (n' - 1) =
                           YulResult \<lparr> result = res', cont = [] \<rparr>" by simp
  
            obtain res1x n1x where 
                Exec1'' : 
                "evalYul' D
                          \<lparr>result = (res \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )]\<rparr>
                           n1x =
                           YulResult \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )] \<rparr>"
                 and Exec1''_sub : 
                  "evalYul' D \<lparr>result = (res \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond ]\<rparr> n1x =  YulResult \<lparr> result = res1x, cont = [] \<rparr>"
              using evalYul'_bisect[OF Exec1'_alt] by auto
  
            have Nlt : "n1x < n' - 1"
            proof(cases "n1x < n' - 1")
              case True
              then show ?thesis by auto
            next
              case False
  
              then have False' : "n' - 1 \<le> n1x" by auto
  
              hence False using evalYul'_pres_succeed[OF Exec1' _ False'] Exec1'' by auto
  
              thus ?thesis by auto
            qed
  
            hence Nleq : "n1x \<le> n' - 1" by auto
  
            have Exec1''' : 
            "evalYul' D \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )] \<rparr> ((n' - 1) - n1x) =
              YulResult \<lparr> result = res', cont = [] \<rparr>"
              using evalYul'_subtract[OF Exec1'' Exec1' Nleq] by auto
  
            have Exec1Full :
              "evalYul' D \<lparr>result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + n1x) =
                YulResult \<lparr> result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res ) (r_funs res )] \<rparr>"
              using evalYul'_steps[OF Exec1 Exec1''] by auto
  
            obtain n1x' where N1x': "n' - 1 - n1x = Suc n1x'"
              using Nlt
              by(cases "n' - 1 - n1x"; auto)

            have Nlt_x : "(n' - 1) - n1x \<le> n" using Suc' Suc.prems(1) Nlt
              by(simp)

            obtain nl resl c locs' funcs' where Execl :
                "evalYul' D \<lparr>result = res1x, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr>
                      nl =
                     YulResult \<lparr>result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>" and
                SpecL : "(r_vals resl = [c] \<and> \<not> is_truthy D c \<and> r_mode resl = Regular \<or> r_mode resl = Break \<or> r_mode resl = Leave)"
              using Suc.IH[OF Nlt_x Exec1'''] by blast

            have Exec1L_Full : 
              "evalYul' D \<lparr>result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + n1x + nl) = 
                YulResult \<lparr>result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
              using evalYul'_steps[OF Exec1Full Execl] by auto

            show ?thesis using SpecL Exec1L_Full by blast
          qed
        qed
      qed
    qed
  qed
qed

lemma for_final_iteration:
assumes H: "evalYul' D \<lparr> result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"
shows "\<exists> nl resl c locs' funcs' .
          evalYul' D  \<lparr> result = res, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> nl = YulResult \<lparr> result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs'] \<rparr> \<and>
          ((r_vals resl = [c] \<and> \<not> is_truthy D c \<and> r_mode resl = Regular) \<or>
           (r_mode resl = Break) \<or>
           (r_mode resl = Leave))" using assms for_final_iteration'[OF _ H, of n']
  by blast

lemma for_invariant' :
  assumes HN : "n1 \<le> n"
  assumes HNf : "nf \<le> n"
  assumes HE : "D %* {P} ([Expression cond] :: ('g, 'v, 't) StackEl list) {P2}"
  assumes HT : "D % {(\<lambda> st . \<exists> c . P2 (st \<lparr> r_vals := [c] \<rparr>) \<and> is_truthy D c)} YulBlock body {P3}"
  assumes HPS : "D % {P3} YulBlock post {P}"
  assumes HStart : "P2 (res1 )"
  (* TODO: it may be possible to eliminate this HCont assumption if we make use of an assumption
     that POST won't change the mode flag - see below *)
  assumes HCont : "\<And> ry . P2 ry \<Longrightarrow> r_mode ry = Continue \<Longrightarrow> P3 (ry \<lparr> r_mode := Regular \<rparr>)" 
  assumes Hloop : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> n1 =
               YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
  assumes Hhalt : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> nf =
    YulResult \<lparr> result = resf, cont = [] \<rparr>"
  (*assumes Hpost_ok : "\<And> ry ry' ny . evalYul' D \<lparr> result = ry, cont = [EnterStatement (YulBlock post)] \<rparr> ny = YulResult \<lparr> result = ry', cont = [] \<rparr> \<Longrightarrow>
r_mode ry = r_mode ry'"*)
  shows "P2 res2" using HN HNf HE HT HPS HStart HCont Hloop Hhalt
proof(induction n arbitrary: n1 nf  res1 res2 resf locs funcs locs' funcs')
  case 0
  then show ?case 
    by(simp)
next
  case (Suc n)
  then show ?case 
  proof(cases n1)
    case 0
    then show ?thesis using Suc.prems by auto
  next
    case Suc' : (Suc n'1)

    show ?thesis using Suc
    proof(cases "r_mode res1")
      case Break

      have EvalDone : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> n1 =
        YulResult \<lparr> result = res1, cont = [] \<rparr>"
        using Suc.prems Suc' Break 
        by(cases n'1; auto)

      hence False using Suc.prems by auto

      then show ?thesis by auto
    next
      case Leave

      have EvalDone : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> n1 =
        YulResult \<lparr> result = res1, cont = [] \<rparr>"
        using Suc.prems Suc' Leave
        by(cases n'1; auto)

      hence False using Suc.prems by auto

      then show ?thesis by auto
    next
      case Continue

      have Exec1 : "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> 1 = 
        YulResult \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = [EnterStatement (YulBlock post),
                               Expression cond,
                               ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>"
        using Continue
        by(auto)

      have Nf_nz : "1 \<le> nf" using Suc.prems(9)
        by(cases nf; auto)

      have Exec1_halts : "evalYul' D \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = 
      [EnterStatement (YulBlock post), Expression cond,
         ExitStatement (YulForLoop [] cond post body) locs
          funcs] \<rparr> (nf - 1) =
          YulResult \<lparr> result = resf, cont = [] \<rparr>"
        using evalYul'_subtract[OF Exec1 Suc.prems(9) Nf_nz] by auto

      hence Exec1_halts_alt :  "evalYul' D \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = 
      [EnterStatement (YulBlock post)] @ [Expression cond,
         ExitStatement (YulForLoop [] cond post body) locs
          funcs] \<rparr> (nf - 1) =
          YulResult \<lparr> result = resf, cont = [] \<rparr>"
        using evalYul'_subtract[OF Exec1 Suc.prems(9) Nf_nz] by simp

      hence Exec1_halts_alt2 :  "evalYul' D \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = 
       [EnterStatement (YulBlock post), Expression cond] @
          [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> (nf - 1) =
           YulResult \<lparr> result = resf, cont = [] \<rparr>"
         using evalYul'_subtract[OF Exec1 Suc.prems(9) Nf_nz] by simp

      obtain resp np where
        Execp : "evalYul' D \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = [EnterStatement (YulBlock post), Expression cond,
         ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> np = 
            YulResult \<lparr> result = resp, cont = [Expression cond,
             ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr>" and
        Execp_sub : "evalYul' D \<lparr> result = (res1 \<lparr> r_mode := Regular \<rparr>), cont = [EnterStatement (YulBlock post)] \<rparr> np =
         YulResult \<lparr> result = resp, cont = [] \<rparr>" 
        using evalYul'_bisect[OF Exec1_halts_alt]
        unfolding List.append.simps
        by blast

      obtain resc nc where
        Execcleast : "nc =
        (LEAST X . \<exists> r2 . evalYul' D \<lparr> result = ( res1 \<lparr> r_mode := Regular \<rparr>), 
                 cont = [EnterStatement (YulBlock post), Expression cond, ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> X =
           YulResult \<lparr> result = r2, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr>)" and
        Execcleast_sub : "nc =
        (LEAST X . \<exists> r2 . evalYul' D \<lparr> result = ( res1 \<lparr> r_mode := Regular \<rparr>), 
                 cont = [EnterStatement (YulBlock post), Expression cond] \<rparr> X =
           YulResult \<lparr> result = r2, cont = [] \<rparr>)" and
        Execc : "evalYul' D \<lparr> result = ( res1 \<lparr> r_mode := Regular \<rparr>), 
                 cont = [EnterStatement (YulBlock post), Expression cond, ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> nc =
           YulResult \<lparr> result = resc, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr>" and
        Execc_sub : "evalYul' D \<lparr> result = ( res1 \<lparr> r_mode := Regular \<rparr>), 
                 cont = [EnterStatement (YulBlock post), Expression cond] \<rparr> nc =
           YulResult \<lparr> result = resc, cont = [] \<rparr>"
        using evalYul'_bisect'[OF Exec1_halts_alt2]
        unfolding List.append.simps
        by blast

      have Exec1_nc : "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> (1 + nc) = 
        YulResult \<lparr> result = resc, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr>"
        using evalYul'_steps[OF Exec1 Execc] by auto

      have Nc_leq_nf : "1 + nc \<le> nf"
      proof(cases "1 + nc \<le> nf")
        case True then show ?thesis by auto
      next
        case False
        hence False' : "nf \<le> 1 + nc" by auto
        have False using evalYul'_pres_succeed[OF Suc.prems(9) _ False'] Exec1_nc by auto
        thus ?thesis by auto
      qed

      have Np_leq : "np \<le> nf - 1 "
      proof(cases "np \<le> nf - 1 ")
        case True thus ?thesis by auto
      next
        case False

        hence Nb_leq' : "nf - 1 \<le> np" by auto
        hence False using evalYul'_pres_succeed[OF Exec1_halts _ Nb_leq'] Execp  by auto
        thus ?thesis by auto
      qed

      have Execp_halts : 
        "evalYul' D
                    \<lparr>result = resp, cont = [
                            Expression cond,
                            ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (nf - 1 - np) =
            YulResult \<lparr>result = resf, cont = []\<rparr>"
        using evalYul'_subtract[OF Execp Exec1_halts Np_leq]
        by auto

      hence Execp_halts_alt : "evalYul' D \<lparr>result = resp, cont = [
                            Expression cond] @
                            [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (nf - 1 - np) =
            YulResult \<lparr>result = resf, cont = []\<rparr>"
        by simp

      have Execc_rest : "evalYul' D \<lparr> result = resc, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs] \<rparr> (nf - (1 + nc)) =
        YulResult \<lparr> result = resf, cont = [] \<rparr>"
        using evalYul'_subtract[OF Exec1_nc Suc.prems(9) Nc_leq_nf] by auto

      obtain resc' nc' where 
        Execpc : "evalYul' D \<lparr>result = resp,
                 cont =
                   [Expression cond, 
                    ExitStatement
                     (YulForLoop [] cond post body)
                     locs funcs]\<rparr>
              nc' =
             YulResult
              \<lparr>result = resc',
                 cont =
                   [ExitStatement
                     (YulForLoop [] cond post body)
                     locs funcs]\<rparr>" and
        Execpc_sub : 
        "evalYul' D
              \<lparr>result = resp, cont = [Expression cond]\<rparr> nc' =
             YulResult \<lparr>result = resc', cont = []\<rparr>"
        using evalYul'_bisect[OF Execp_halts_alt]
        unfolding append.simps
        by blast

      have Exec_p_c' : "evalYul' D \<lparr> result = res1\<lparr>r_mode := Regular\<rparr>,
                 cont = [EnterStatement (YulBlock post), Expression cond]\<rparr> (np + nc') =
        YulResult \<lparr> result = resc', cont = [] \<rparr>"
        using evalYul'_seq[OF Execp_sub Execpc_sub] unfolding append.simps by auto

      have P3_res1_reg : "P3 (res1 \<lparr> r_mode := Regular \<rparr>)"
        using Suc.prems(6) Suc.prems(7) Continue by auto

      have P_resp : "P resp"
        using HTE[OF Suc.prems(5) _ Execp_sub] P3_res1_reg by auto

      have P2_resc' : "P2 resc'" 
        using HTE[OF Suc.prems(3) _ Execpc_sub] P_resp
        by auto

      show ?thesis
      proof(cases "1 + nc \<le> n1")
        case True

        have Exec12_done : "evalYul' D \<lparr>result = resc, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
          (nf - (1 + nc)) = YulResult \<lparr> result = resf, cont = [] \<rparr>"
          using evalYul'_subtract[OF Exec1_nc Suc.prems(9) Nc_leq_nf] by auto

        have Exec12_res2 : "evalYul' D \<lparr>result = resc, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
          (n1 - (1 + nc)) = YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
          using evalYul'_subtract[OF Exec1_nc Suc.prems(8) True] by auto

        have Nc_leq : "n1 - (1 + nc) \<le> n"
          using Suc.prems(1) by auto

        have Nc_leq3 : "(nf - (1 + nc)) \<le> n"
          using Suc.prems(2) by auto

        have Nc_is_least : "nc \<le> np + nc'"
            using Least_le[of "(\<lambda> X . \<exists>res2' .
             evalYul' D
              \<lparr>result = res1\<lparr>r_mode := Regular\<rparr>,
                 cont = [EnterStatement (YulBlock post), Expression cond]\<rparr>
              X =
             YulResult \<lparr>result = res2', cont = []\<rparr>)" "np + nc'"] Exec_p_c'
            unfolding Execcleast_sub
            by blast

        have Resc_eq_resc' : "resc = resc'"
          using evalYul'_pres_succeed[OF Execc_sub _ Nc_is_least] Exec_p_c'
          by auto

        have P2_resc : "P2 resc" using P2_resc' unfolding Resc_eq_resc' by auto

        show ?thesis using Suc.IH[OF Nc_leq Nc_leq3 Suc.prems(3) Suc.prems(4) Suc.prems(5) P2_resc HCont Exec12_res2 Exec12_done] (*Exec12_res2 Exec12_done]*) 
          by auto
      next
        case False

        have N1_nz : "1 \<le> n1" using Suc'  by auto

        have False' : "n1 - 1 < nc" using False N1_nz by auto
        have False'' : "n1 - 1 \<le> nc" using False N1_nz by auto

        have N1_exec_iteration :
          "evalYul' D
            \<lparr>result = res1\<lparr>r_mode := Regular\<rparr>,
               cont = [EnterStatement (YulBlock post), Expression cond, ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
            (n1 - 1) =
           YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
          using evalYul'_subtract[OF Exec1 Suc.prems(8) N1_nz] 
          by blast

        show ?thesis
        proof(cases "evalYul' D
            \<lparr>result = res1\<lparr>r_mode := Regular\<rparr>,
               cont = [EnterStatement (YulBlock post), Expression cond]\<rparr>
            (n1 - 1)")
          case ER2x : (ErrorResult msg2x bad2x)

          have False using evalYul'_pres_fail[OF ER2x False''] Execc_sub  by auto

          then show ?thesis by auto
        next
          case YR2x  : (YulResult res2x)

          obtain res2x_st res2x_c where Res2x : "res2x = \<lparr> result = res2x_st, cont = res2x_c \<rparr>"
            by(cases res2x; auto)

          have Res2xc : "res2x_c = []"
          proof(cases "res2x_c")
            case Nil2x : Nil
            then show ?thesis by auto
          next
            case Cons2x : (Cons c2xh c2xt)

            have BadExec :
              "evalYul' D
                   \<lparr>result = res1\<lparr>r_mode := Regular\<rparr>,
                      cont = [EnterStatement (YulBlock post), Expression cond] @ [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
                   (n1 - 1) =
                  YulResult \<lparr>result = res2x_st, cont = (c2xh # c2xt) @ [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>"
              using evalYul'_cont_extend[of D "res1\<lparr>r_mode := Regular\<rparr>"
                  "[EnterStatement (YulBlock post), Expression cond]"
                  "n1 - 1" res2x_st res2x_c c2xh c2xt
                  "[ExitStatement (YulForLoop [] cond post body) locs funcs]"] YR2x unfolding Res2x Cons2x
              by auto

            hence False using N1_exec_iteration
              unfolding Cons2x append.simps
              by auto

            thus ?thesis by auto
          qed
              
          have Res2_eq : "res2x_st = resc" 
            using evalYul'_pres_succeed[OF YR2x _ False''] Execc_sub unfolding Res2x Res2xc
            by auto

          have Nc_is_least : "nc \<le> n1 - 1"
            using Least_le[of "(\<lambda> X . \<exists>res2' .
             evalYul' D
              \<lparr>result = res1\<lparr>r_mode := Regular\<rparr>,
                 cont = [EnterStatement (YulBlock post), Expression cond]\<rparr>
              X =
             YulResult \<lparr>result = res2', cont = []\<rparr>)" "n1 - 1"] YR2x Res2x Res2xc
            unfolding Execcleast_sub
            by blast

          hence False using False Suc'
            by(auto)

          thus ?thesis by auto
        qed
      qed

    next
      case Regular
  
      then show ?thesis
      proof(cases "r_vals res1")
        case Nil

        then show ?thesis using Suc.prems Suc' Nil Regular
          by(auto simp add: updateResult_def)
      next

        case (Cons c vt)

        hence Vt : "vt = []" using Suc.prems Suc' Regular by(cases vt; auto simp add: updateResult_def)
  
        hence V : "r_vals res1 = [c]" using Cons by auto
  
        show ?thesis
        proof(cases "is_irregular (r_mode res1)")
          case T_Irreg : True
          then show ?thesis using Regular by auto
        next
          case F_Irreg : False
          hence Reg : "r_mode res1 = Regular"
            by(cases "r_mode res1"; auto)
  
          show ?thesis
          proof(cases "is_truthy D c")
            case F_Truthy : False
  
            have C1 : "evalYul' D
                        \<lparr>result = res1,
                           cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
                        1 =
                       YulResult
                        \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = []\<rparr>"
              using F_Truthy Vt V Reg
              by(auto simp add: updateResult_def)

            show ?thesis
            proof(cases n1)
              case Zero'' : 0
              then show ?thesis using Hloop Suc.prems by auto
            next
              case Suc'' : (Suc n1')

              then have False using
                  evalYul'_pres_succeed[OF C1 _ _] Suc.prems(8)
                by(auto)
                 
              then show ?thesis by auto
            qed
          next
            case T_Truthy : True
  
            have Exec1 : "evalYul' D
                          \<lparr>result = res1,
                             cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr>
                          1 =
                       YulResult
                        \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr>"
              using Suc' Suc.prems T_Truthy Reg V
              by(auto simp add: updateResult_def)

            obtain nf' where Nf : "nf = Suc nf'"
              using Suc.prems by(cases nf; auto)

            have Exec1_halts : "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1) =
                       YulResult
                        \<lparr>result = resf, cont = []\<rparr>"
              using evalYul'_subtract[OF Exec1 Suc.prems(9)] Nf by auto

            hence Exec1_halts_alt : "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond] @
                                  [ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1) =
                       YulResult
                        \<lparr>result = resf, cont = []\<rparr>"
              by simp

            hence Exec1_halts_alt_body : "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body)]@
                                  [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1) =
                       YulResult
                        \<lparr>result = resf, cont = []\<rparr>"
              by simp


            obtain n2' res2' where
            N2least : "n2' =
           (LEAST X.
               \<exists>r2. evalYul' D
                     \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                        cont =
                          [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond] @
                          [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
                     X =
                    YulResult
                     \<lparr>result = r2,
                        cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>)"
            and
            N2least_sub : 
           "n2' =
           (LEAST X.
               \<exists>r2. evalYul' D
                     \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                        cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr>
                     X =
                    YulResult \<lparr>result = r2, cont = []\<rparr>)"
            and
            N2exec :
            "(evalYul' D
              \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
               cont =
                 [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond] @
                 [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
            n2' = YulResult \<lparr>result = res2', cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>)"
            and
            N2exec_sub :
            "evalYul' D
              \<lparr>result = res1\<lparr>r_vals := []\<rparr>, cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr> n2' =
             YulResult \<lparr>result = res2', cont = []\<rparr>"
              using evalYul'_bisect'[OF Exec1_halts_alt]
              by blast

            obtain nb resb where 
            Exec2_body :
              "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body),
                                  EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> nb =
                       YulResult
                        \<lparr>result = resb, cont = [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr>" and
              Exec2'_body_Sub :
              "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body)]\<rparr> nb =
                       YulResult
                        \<lparr>result = resb, cont = []\<rparr>"
              using evalYul'_bisect[OF Exec1_halts_alt_body]
              unfolding append.simps
              by blast

            have P3_resb : "P3 resb"
              using HTE[OF Suc.prems(4), of "\<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body)]\<rparr>" nb "\<lparr>result = resb, cont = []\<rparr>"]
                    Suc.prems(6) Exec2'_body_Sub V T_Truthy
              by(cases res1; auto)


            have Exec2_body_alt : "evalYul' D
                          \<lparr>result = (res1 \<lparr> r_vals := [] \<rparr>),
                           cont = [EnterStatement (YulBlock body)]@
                                  [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> nb =
                       YulResult
                        \<lparr>result = resb, cont = [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr>" 
              using Exec2_body by simp

            have Nb_leq : "nb \<le> nf - 1 "
            proof(cases "nb \<le> nf - 1 ")
              case True thus ?thesis by auto
            next
              case False

              hence Nb_leq' : "nf - 1 \<le> nb" by auto
              hence False using evalYul'_pres_succeed[OF Exec1_halts _ Nb_leq'] Exec2_body by auto
              thus ?thesis by auto
            qed

            have Exec3_halts : 
              "evalYul' D
                          \<lparr>result = resb, cont = [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1 - nb) =
                  YulResult \<lparr>result = resf, cont = []\<rparr>"
              using evalYul'_subtract[OF Exec2_body Exec1_halts Nb_leq]
              by auto

            hence Exec3_halts_alt :
              "evalYul' D
                          \<lparr>result = resb, cont = [EnterStatement (YulBlock post)]@
                                  [Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1 - nb) =
                  YulResult \<lparr>result = resf, cont = []\<rparr>"
              by simp

            obtain np resp where 
              Exec3_post :
              "evalYul' D
                          \<lparr>result = resb, cont = [EnterStatement (YulBlock post),
                                  Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> np =
                       YulResult
                        \<lparr>result = resp, cont = [Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr>" and
              Exec3_post_Sub :
              " evalYul' D
                    \<lparr>result = resb,
                       cont = [EnterStatement (YulBlock post)]\<rparr>
                    np =
                   YulResult \<lparr>result = resp, cont = []\<rparr>"
              using evalYul'_bisect[OF Exec3_halts_alt]
              unfolding append.simps              
              by blast

            have P_resp : "P resp"
              using HTE[OF Suc.prems(5) _ Exec3_post_Sub] P3_resb
              by(simp)

            have Np_leq : "np \<le> nf - 1 - nb "
            proof(cases "np \<le> nf - 1 - nb ")
              case True thus ?thesis by auto
            next
              case False

              hence Np_leq' : "nf - 1 - nb \<le> np" by auto
              hence False using evalYul'_pres_succeed[OF Exec3_halts _ Np_leq'] Exec3_post by auto
              thus ?thesis by auto
            qed

            have Exec4_halts : 
              "evalYul' D
                          \<lparr>result = resp, cont = [Expression cond,
                                  ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1 - nb - np) =
                  YulResult \<lparr>result = resf, cont = []\<rparr>"
              using evalYul'_subtract[OF Exec3_post Exec3_halts Np_leq]
              by auto

            hence Exec4_halts_alt : 
              "evalYul' D
                          \<lparr>result = resp, cont = [Expression cond] @
                                  [ExitStatement (YulForLoop [] cond post body) (r_locals res1 ) (r_funs res1 )]\<rparr> (nf - 1 - nb - np) =
                  YulResult \<lparr>result = resf, cont = []\<rparr>"
              by simp

            obtain resc nc where Exec4_cond : 
              "evalYul' D
              \<lparr>result = resp,
                 cont =
                   [Expression cond, 
                    ExitStatement
                     (YulForLoop [] cond post body)
                     (r_locals res1) (r_funs res1)]\<rparr>
              nc =
             YulResult
              \<lparr>result = resc,
                 cont =
                   [ExitStatement
                     (YulForLoop [] cond post body)
                     (r_locals res1) (r_funs res1)]\<rparr>" and
              Exec4_cond_Sub : 
              "evalYul' D
                    \<lparr>result = resp, cont = [Expression cond]\<rparr> nc =
                   YulResult \<lparr>result = resc, cont = []\<rparr>"
              using evalYul'_bisect[OF Exec4_halts_alt]
              unfolding append.simps
              by blast

            have P2_resc : "P2 resc"
              using HTE[OF Suc.prems(3) _ Exec4_cond_Sub] P_resp
              by auto

            have Reassoc : "(1 + (nb + (np + nc))) = 1 + nb + np + nc" by simp

            have Exec1234 : "evalYul' D
                          \<lparr>result = res1,
                             cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + nb + np + nc) = 
                        YulResult
                              \<lparr>result = resc,
                                 cont =
                                   [ExitStatement
                                     (YulForLoop [] cond post body)
                                     (r_locals res1) (r_funs res1)]\<rparr>"
              using evalYul'_steps[OF Exec1 evalYul'_steps[OF Exec2_body evalYul'_steps[OF Exec3_post Exec4_cond]]]
              unfolding Reassoc
              by simp

            have Reassoc2 : "(nb + (np + nc)) = nb + np + nc" by simp

            have Exec234 :
              "evalYul' D
                          \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                             cont = [EnterStatement  (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr> (nb + np + nc) = 
                        YulResult
                              \<lparr>result = resc,
                                 cont = []\<rparr>"
              using evalYul'_seq[OF Exec2'_body_Sub evalYul'_seq[OF Exec3_post_Sub Exec4_cond_Sub]]
              unfolding Reassoc2 by simp

            have Exec12 : "evalYul' D
                          \<lparr>result = res1,
                             cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> (1 + n2') =
                    YulResult \<lparr>result = res2', cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>" 
              using evalYul'_steps[OF Exec1] N2exec by auto

            have N2'_leq : "1 + n2' \<le> nf"
            proof(cases "1 + n2' \<le> nf")
              case True thus ?thesis by auto
            next
              case False
              hence Leq' : "nf \<le> 1 + n2'" by auto

              have False using evalYul'_pres_succeed[OF Suc.prems(9) _ Leq'] Exec12 by auto
              thus ?thesis by auto
            qed

            have N1_leq : "n1 \<le> nf"
            proof(cases "n1  \<le> nf")
              case True thus ?thesis by auto
            next
              case False
              hence Leq' : "nf \<le> n1" by auto

              have False using evalYul'_pres_succeed[OF Suc.prems(9) _ Leq'] Suc.prems(8) by auto
              thus ?thesis by auto
            qed

            show ?thesis
            proof(cases "1 + n2' \<le> n1")
              case True 

              have Exec12_done : "evalYul' D \<lparr>result = res2', cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
                (nf - (1 + n2')) = YulResult \<lparr> result = resf, cont = [] \<rparr>"
                using evalYul'_subtract[OF Exec12 Suc.prems(9) N2'_leq] by auto
  
              have Exec12_res2 : "evalYul' D \<lparr>result = res2', cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
                (n1 - (1 + n2')) = YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
                using evalYul'_subtract[OF Exec12 Suc.prems(8) True] by auto
  
              have N_leq : "n1 - (1 + n2') \<le> n"
                using Suc.prems(1) by auto

              have N_leq3 : "(nf - (1 + n2')) \<le> n"
                using Suc.prems(2) by auto

              have N2_is_least : "n2' \<le> (nb + np + nc)"
                using Least_le[of "(\<lambda> X . \<exists>res2' .
                 evalYul' D
                  \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                     cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr>
                  X =
                 YulResult \<lparr>result = res2', cont = []\<rparr>)" "(nb + np + nc)"]  Exec234
                unfolding N2least_sub
                by blast

              have Resc_eq_res2' : "resc = res2'"
                using Exec234
                  evalYul'_pres_succeed[OF N2exec_sub _ N2_is_least]
                by auto

              have P2_Res2' : "P2 res2'" using P2_resc unfolding Resc_eq_res2' by auto

              show ?thesis using Suc.IH[OF N_leq N_leq3 Suc.prems(3) Suc.prems(4) Suc.prems(5) P2_Res2' _ Exec12_res2 Exec12_done] HCont  by auto
            next
              case False 

              have N1_nz : "1 \<le> n1" using Suc'  by auto

              have False' : "n1 - 1 < n2'" using False N1_nz by auto
              have False'' : "n1 - 1 \<le> n2'" using False N1_nz by auto

              have N1_exec_iteration :
                "evalYul' D
                  \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                     cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond, ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
                  (n1 - 1) =
                 YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
                using evalYul'_subtract[OF Exec1 Suc.prems(8) N1_nz] 
                by blast

              show ?thesis
              proof(cases "evalYul' D
                  \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                     cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr>
                  (n1 - 1)")
                case ER2x : (ErrorResult msg2x bad2x)

                have False using evalYul'_pres_fail[OF ER2x False''] N2exec_sub by auto

                then show ?thesis by auto
              next
                case YR2x  : (YulResult res2x)

                obtain res2x_st res2x_c where Res2x : "res2x = \<lparr> result = res2x_st, cont = res2x_c \<rparr>"
                  by(cases res2x; auto)

                have Res2xc : "res2x_c = []"
                proof(cases "res2x_c")
                  case Nil2x : Nil
                  then show ?thesis by auto
                next
                  case Cons2x : (Cons c2xh c2xt)

                  have BadExec :
                    "evalYul' D
                         \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                            cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond] @ [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>
                         (n1 - 1) =
                        YulResult \<lparr>result = res2x_st, cont = (c2xh # c2xt) @ [ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]\<rparr>"
                    using evalYul'_cont_extend[of D "res1\<lparr>r_vals := []\<rparr>"
                        "[EnterStatement  (YulBlock body), EnterStatement (YulBlock post), Expression cond]"
                        "n1 - 1" res2x_st res2x_c c2xh c2xt
                        "[ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)]"] YR2x unfolding Res2x Cons2x
                    by auto

                  hence False using N1_exec_iteration
                    unfolding Cons2x append.simps
                    by auto

                  thus ?thesis by auto
                qed
                    
                have Res2_eq : "res2x_st = res2'" 
                  using evalYul'_pres_succeed[OF YR2x _ False''] N2exec_sub unfolding Res2x Res2xc
                  by auto

                have N2_is_least : "n2' \<le> n1 - 1"
                  using Least_le[of "(\<lambda> X . \<exists>res2' .
                   evalYul' D
                    \<lparr>result = res1\<lparr>r_vals := []\<rparr>,
                       cont = [EnterStatement (YulBlock body), EnterStatement (YulBlock post), Expression cond]\<rparr>
                    X =
                   YulResult \<lparr>result = res2', cont = []\<rparr>)" "n1 - 1"] YR2x Res2x Res2xc
                  unfolding N2least_sub
                  by blast

                hence False using False Suc'
                  by(auto)

                thus ?thesis by auto
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed 

lemma for_invariant :
  assumes HE : "D %* {P} ([Expression cond] :: ('g, 'v, 't) StackEl list) {P2}"
  assumes HT : "D % {(\<lambda> st . \<exists> c . P2 (st \<lparr> r_vals := [c] \<rparr>) \<and> is_truthy D c)} YulBlock body {P3}"
  assumes HPS : "D % {P3} YulBlock post {P}"
  assumes HStart : "P2 (res1 )"
  (* TODO: it may be possible to eliminate this HCont assumption if we make use of an assumption
     that POST won't change the mode flag - see below *)
  assumes HCont : "\<And> ry . P2 ry \<Longrightarrow> r_mode ry = Continue \<Longrightarrow> P3 (ry \<lparr> r_mode := Regular \<rparr>)" 
  assumes Hloop : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> n1 =
               YulResult \<lparr>result = res2, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>"
  assumes Hhalt : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) locs funcs]\<rparr> nf =
    YulResult \<lparr> result = resf, cont = [] \<rparr>"
  shows "P2 res2" 
proof-

  have N1_leq_nf : "n1 \<le> nf"
  proof(cases "n1 \<le> nf")
    case True
    then show ?thesis by auto
  next
    case False

    hence False' : "nf \<le> n1" by auto

    have False using evalYul'_pres_succeed[OF Hhalt _ False'] Hloop by auto

    then show ?thesis by auto
  qed
    
  show "P2 res2"
  using assms
  using for_invariant'[of n1 nf nf, OF N1_leq_nf] by blast
qed

(*
proof(induction n arbitrary: n' locs funcs locs' funcs' res1 resf)
*)
(* assuming empty init, for simplicity *)
(* we might need to strengthen this by saying
that the condition is false at the end. *)
lemma HFor :
  assumes Hc : "\<And> st . P2 st \<Longrightarrow> is_regular (r_mode st) \<Longrightarrow> \<exists> c . r_vals st = [c]"
  (*assumes HI : "D %* {P} map EnterStatementinit {P1}"*)
  assumes HE : "D %* {P} ([Expression cond] :: ('g, 'v, 't) StackEl list) {P2}"
  assumes HT : "D % {(\<lambda> st . \<exists> c . P2 (st \<lparr> r_vals := [c] \<rparr>) \<and> is_truthy D c)} YulBlock body {P3}"
  assumes HPS : "D % {P3} YulBlock post {P}"
  assumes HF : "\<And> c st . P2 st \<Longrightarrow> is_regular (r_mode st) \<Longrightarrow> r_vals st = [c] \<Longrightarrow> \<not> is_truthy D c \<Longrightarrow> Q (st \<lparr> r_vals := [] \<rparr>)"
  assumes HIrreg : "\<And> st . P st \<Longrightarrow> \<not> is_regular (r_mode st) \<Longrightarrow> Q (st)"

  assumes HBreak : "\<And> st . P2 st \<Longrightarrow> r_mode st = Break \<Longrightarrow> Q (st \<lparr> r_mode := Regular \<rparr>)"
  assumes HLeave :  "\<And> st . P2 st \<Longrightarrow> r_mode st = Leave \<Longrightarrow> Q (st )"
  assumes HCont : "(\<And>st. P2 st \<Longrightarrow> r_mode st = Continue \<Longrightarrow> P3 (st\<lparr>r_mode := Regular\<rparr>))"

  shows "D % {P} YulForLoop [] cond post body {Q}"
proof
  fix res contn n st'
  assume P : "P res"
  assume Contn : "contn = ([EnterStatement (YulForLoop [] cond post body)] :: ('g, 'v, 't) StackEl list)"
  assume Exec : "evalYul' D \<lparr> result = res, cont = contn \<rparr> n = YulResult st'"
  assume Done : "cont st' = []"

  obtain res' where Res' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> n = YulResult \<lparr> result = res', cont = [] \<rparr>"
    using Exec Done by (cases st'; auto)

  show "Q (result st')"
  proof(cases "evalYulStep D \<lparr>result = res, cont = contn\<rparr>")
    case (ErrorResult x21 x22)

    then show ?thesis using Exec Contn 
     by(cases "r_mode res";  simp add: updateResult_def) 
  next
    case (YulResult st2)

    show ?thesis
    proof(cases "cont st2")
      case Nil

      show ?thesis
      proof(cases "is_regular (r_mode res)")
        case Irreg : False

        have "st2 = \<lparr>result = res, cont = []\<rparr>" using YulResult Nil Irreg Contn
          by (cases "r_mode res"; auto)

        obtain n' where N' : "n = Suc n'" using  Nil Irreg Exec Contn Res'
          by(cases n; auto)

        have Eval1'_step : "evalYul' D \<lparr>result = res, cont = [Expression cond]\<rparr> 1 = YulResult \<lparr> result = res, cont = [] \<rparr>"
          using N' Exec Irreg
          by(cases "r_mode res"; auto)

        have Eval1' : "st' = \<lparr> result = res, cont = [] \<rparr>"
          using evalYul'_pres_succeed[OF Eval1'_step, of n] Exec N' Contn Irreg
          by(cases "r_mode res"; auto)

        have P2 : "P2 res"
          using HTE[OF HE _ Eval1'_step] P by auto

        (* TODO: we originally had an assumption about Qe implying Q. not sure which is better.
           i  think they are equivalent. but it is simpler this way; probably we can clean
           up this proof a bit here *)

        have EvalFull_step : "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulForLoop [] cond post body)]\<rparr> 1 
          = YulResult \<lparr> result = res, cont = []\<rparr>"
          using YulResult Contn Irreg
          by(cases "r_mode res"; auto)
        
        then show ?thesis using HIrreg[OF P Irreg] Eval1' by auto
      next
        case Reg : True

        hence Regular : "r_mode res = Regular" by(cases "r_mode res"; auto)

        (* contradiction: we are in Regular mode but threw away the entire computation. *)
        have False using YulResult Regular Contn Nil
          by(auto simp add: updateResult_def)

        thus ?thesis by auto
      qed
    next
      case (Cons cont2h cont2t)

      show ?thesis
      proof(cases "is_regular (r_mode res)")
        case Irreg : False

        (* contradiction: we should have thrown away the computation but didn't. *)
        have False using YulResult Irreg Contn Cons
          by(cases "r_mode res"; auto simp add: updateResult_def)

        thus ?thesis by auto
      next
        case Reg : True

        hence Regular : "r_mode res = Regular" by(cases "r_mode res"; auto)

        (* the "happy-path" case.
           idea here is that we run the expression, then (if applicable) the body
        *)

        have EvalFull_step1 :
          "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulForLoop [] cond post body)]\<rparr> 1 
            = YulResult \<lparr> result = res, cont = [Expression cond, ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr>"
          using Regular
          by(auto simp add: updateResult_def)

        obtain n' where N' : "n = Suc n'" using Exec Contn Done by (cases n; auto)

        have EvalFull_rest :
          "evalYul' D \<lparr> result = res, cont = [Expression cond, ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"
          using evalYul'_subtract[OF EvalFull_step1, of n st'] Exec Res' unfolding N' Contn
          by(auto simp del: evalYul'.simps)

        hence EvalFull_rest_alt : "evalYul' D \<lparr> result = res, cont = [Expression cond] @ [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> n' = YulResult \<lparr> result = res', cont = [] \<rparr>"
          by simp

        obtain n1 res1 where
          Res1 : "evalYul' D \<lparr> result = res, cont = [Expression cond, ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]  \<rparr> n1 =
            YulResult \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)] \<rparr>" and
          Res1_sub : "evalYul' D \<lparr> result = res, cont = [Expression cond] \<rparr> n1 = 
            YulResult \<lparr> result = res1, cont = [] \<rparr>"
          using evalYul'_bisect[OF EvalFull_rest_alt] by auto

        have Qe : "P2 (res1)" using HTE[OF HE _ Res1_sub] P by auto

        have Res1_reg : "is_regular (r_mode res1)"
          using eval_expression_mode[OF Res1_sub] Reg by auto

        obtain c where C: "r_vals res1 = [c]"
          using Hc[OF Qe Res1_reg] by auto

        show ?thesis
        proof(cases "is_truthy D c")
          case False

          have Qst1 : "Q ((res1 \<lparr>r_vals := []\<rparr>))" using HF[OF Qe]
              False Res1_reg Qe C 
            by(cases res1; auto) 

          have EvalFull_step3 :
            "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> 1 =
              YulResult \<lparr> result = (res1 \<lparr> r_vals := [] \<rparr>), cont = [] \<rparr>"
            using Regular Res1_reg C False
            by(auto simp add: updateResult_def)

          have EvalFull_steps23 :
            "evalYul' D \<lparr>result = res, cont = [Expression cond, ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)] \<rparr> (n1 + 1) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = []\<rparr>)"
            using evalYul'_seq[OF Res1_sub EvalFull_step3] 
            by auto

          have EvalFull_steps123 :
            "evalYul' D \<lparr>result = res, cont = [EnterStatement (YulForLoop [] cond post body)]\<rparr> (1 + (n1 + 1)) =
             YulResult (\<lparr> result = res1 \<lparr> r_vals := [] \<rparr>, cont = [] \<rparr>)"
            using evalYul'_steps[OF EvalFull_step1 EvalFull_steps23] by auto

          have Res1_eq : "(res1 \<lparr> r_vals := [] \<rparr> = result st')"
            using evalYul'_agree_succeed[OF EvalFull_steps123, of n res'] Res' Contn Exec
            by auto
            
          thus ?thesis using Qst1 by auto
        next
          case True

          have EvalFull_step3 :
            "evalYul' D \<lparr> result = res1, cont = [ ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> 1 =
              YulResult \<lparr> result = (res1 \<lparr> r_vals := [] \<rparr>)
                        , cont = [ EnterStatement (YulBlock body)
                                 , EnterStatement (YulBlock post)
                                 , Expression cond
                                 , ExitStatement (YulForLoop [] cond post body) (r_locals res1) (r_funs res1)] \<rparr>"
            using Regular Res1_reg C True
            by(auto simp add: updateResult_def)


          have EvalFull_step3' : "evalYul' D \<lparr>result = res, cont = contn\<rparr> (1 + n1) =
            YulResult \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)] \<rparr>"
            using evalYul'_steps[OF EvalFull_step1 Res1] Contn by auto

          have Leq1 : "1 + n1 \<le> n"
          proof(cases "1 + n1 \<le> n")
            case True
            then show ?thesis by auto
          next
            case False

            hence Leq1' : "n \<le> 1 + n1" by auto

            have False using evalYul'_pres_succeed[OF Res' _ Leq1'] EvalFull_step3' by auto

            thus ?thesis by auto
          qed

          have EvalFull_step3_rest : 
            "evalYul' D \<lparr> result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)] \<rparr> (n - (1 + n1)) =
              YulResult \<lparr> result = res', cont = [] \<rparr>"
            using evalYul'_subtract[OF EvalFull_step3' Exec Leq1] N' Done Res' Exec by auto

          have LastIteration : "\<exists>nl resl c locs' funcs'.
             evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> nl =
             YulResult \<lparr>result = resl, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> \<and>
             (r_vals resl = [c] \<and> \<not> is_truthy D c \<and> r_mode resl = Regular \<or> r_mode resl = Break \<or> r_mode resl = Leave)"
            using for_final_iteration[OF EvalFull_step3_rest]
            by auto

          obtain nf resf c' locs' funcs' where
             EvalFinal : "evalYul' D \<lparr>result = res1, cont = [ExitStatement (YulForLoop [] cond post body) (r_locals res) (r_funs res)]\<rparr> nf =
               YulResult \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr>" and
             EvalFinal_spec : "((r_vals resf = [c'] \<and> \<not> is_truthy D c' \<and> r_mode resf = Regular) \<or> r_mode resf = Break \<or> r_mode resf = Leave)" 
            using LastIteration
            by(blast)

          show ?thesis
          proof(cases "r_mode resf")
            case Regular

            have P2_final : "P2 resf" using for_invariant[OF HE HT HPS Qe HCont EvalFinal EvalFull_step3_rest] by auto

            have C' : "r_vals resf = [c']" and C'_Falsy : "\<not> is_truthy D c'" using EvalFinal_spec Regular by auto

            have Lt_nf : "nf < n - (1 + n1) "
            proof(cases "nf < n - (1 + n1)")
              case True
              then show ?thesis by auto
            next
              case False

              hence False_leq : "n - (1 + n1) \<le> nf"
                by auto

              hence False using evalYul'_pres_succeed[OF EvalFull_step3_rest _ False_leq] EvalFinal by auto

              then show ?thesis by auto
            qed
            hence Leq_nf : "nf \<le> n - (1 + n1) " by auto

            (* use subtract again to get resf \<rightarrow> res' *)
            have LastStep : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
             YulResult \<lparr> result = res', cont = [] \<rparr>"
              using evalYul'_subtract[OF EvalFinal EvalFull_step3_rest Leq_nf] by auto

            have LastStep' : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
               YulResult \<lparr> result = resf \<lparr> r_vals := [] \<rparr>, cont = [] \<rparr>"
              using Regular Lt_nf C' C'_Falsy
              by(auto simp add: updateResult_def)

            have Resf_eq : "res' = resf \<lparr> r_vals := [] \<rparr>"
              using evalYul'_agree_succeed[OF LastStep' LastStep] by auto

            have "Q (resf\<lparr>r_vals := []\<rparr>)"
              using HF[OF P2_final _ C' C'_Falsy] Regular by auto

            thus ?thesis using Exec Res' unfolding Resf_eq 
              by auto
          next
            case Break

            have P2_final : "P2 resf" using for_invariant[OF HE HT HPS Qe HCont EvalFinal EvalFull_step3_rest] by auto

            have Lt_nf : "nf < n - (1 + n1) "
            proof(cases "nf < n - (1 + n1)")
              case True
              then show ?thesis by auto
            next
              case False

              hence False_leq : "n - (1 + n1) \<le> nf"
                by auto

              hence False using evalYul'_pres_succeed[OF EvalFull_step3_rest _ False_leq] EvalFinal by auto

              then show ?thesis by auto
            qed
            hence Leq_nf : "nf \<le> n - (1 + n1) " by auto

            (* use subtract again to get resf \<rightarrow> res' *)
            have LastStep : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
             YulResult \<lparr> result = res', cont = [] \<rparr>"
              using evalYul'_subtract[OF EvalFinal EvalFull_step3_rest Leq_nf] by auto

            have LastStep' : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
               YulResult \<lparr> result = resf \<lparr> r_mode := Regular \<rparr>, cont = [] \<rparr>"
              using Break Lt_nf 
              by(auto simp add: updateResult_def)

            have Resf_eq : "res' = resf \<lparr> r_mode := Regular \<rparr>"
              using evalYul'_agree_succeed[OF LastStep' LastStep] by auto

            have "Q (resf\<lparr>r_mode := Regular \<rparr> )"
              using HBreak[OF P2_final Break] by auto

            thus ?thesis using Exec Res' unfolding Resf_eq 
              by auto
          next
            case Continue
            hence False using EvalFinal_spec by auto
            then show ?thesis by auto
          next
            case Leave

            have P2_final : "P2 resf" using for_invariant[OF HE HT HPS Qe HCont EvalFinal EvalFull_step3_rest] by auto

            have Lt_nf : "nf < n - (1 + n1) "
            proof(cases "nf < n - (1 + n1)")
              case True
              then show ?thesis by auto
            next
              case False

              hence False_leq : "n - (1 + n1) \<le> nf"
                by auto

              hence False using evalYul'_pres_succeed[OF EvalFull_step3_rest _ False_leq] EvalFinal by auto

              then show ?thesis by auto
            qed
            hence Leq_nf : "nf \<le> n - (1 + n1) " by auto

            (* use subtract again to get resf \<rightarrow> res' *)
            have LastStep : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
             YulResult \<lparr> result = res', cont = [] \<rparr>"
              using evalYul'_subtract[OF EvalFinal EvalFull_step3_rest Leq_nf] by auto

            have LastStep' : "evalYul' D \<lparr>result = resf, cont = [ExitStatement (YulForLoop [] cond post body) locs' funcs']\<rparr> (n - (1 + n1) - nf) =
               YulResult \<lparr> result = resf, cont = [] \<rparr>"
              using Leave Lt_nf 
              by(auto simp add: updateResult_def)

            have Resf_eq : "res' = resf"
              using evalYul'_agree_succeed[OF LastStep' LastStep] by auto

            have "Q (resf )"
              using HLeave[OF P2_final Leave] by auto

            thus ?thesis using Exec Res' unfolding Resf_eq 
              by auto

          qed
        qed
      qed
    qed
  qed
qed


end