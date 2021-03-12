theory EvmInterpreter imports EvmBytecode MiniEvm "HOL-Library.Adhoc_Overloading"
begin

(*
definition parse_byte_inst' :: "8 word \<Rightarrow> nat" where
"parse_byte_inst' w = unat w"
*)

lift_definition parse_byte_inst :: "8 word \<Rightarrow> inst"
is unat
proof-
  fix wd :: "8 word"
  show "unat wd \<in> set_of_ranges inst_codes"
    unfolding inst_codes_def
  proof(transfer)
    fix wd :: int
    show "(nat \<circ> take_bit LENGTH(8)) wd
          \<in> set_of_ranges' (mk_ranges' [(0, 256)])"
      using Bits_Int.bintr_lt2p[of "8" "wd"]
      by simp
  qed
qed

(* add stack, pc to estate *)
record estate_ll =
  el_e :: "estate"
  el_stack :: "eint list"
  el_pc :: "eint"
  el_crash :: bool

fun crash :: "estate_ll \<Rightarrow> estate_ll" where
"crash e = (e \<lparr> el_crash := True \<rparr>)"

(* TODO: should we model stack overflow? *)
type_synonym el_step = "estate_ll \<Rightarrow> estate_ll"

definition max_ueint :: "eint" where
"max_ueint = Word.of_int (2^256) - 1"

consts mkStep ::
  "'x \<Rightarrow> el_step"

definition mkStep_0_0 ::
"(estate, unit) State \<Rightarrow>
 el_step" where
"mkStep_0_0 f el =
  (if el_pc el = max_ueint then crash el
   else
   (case f (el_e el) of
      ((), x) \<Rightarrow> (el \<lparr> el_e := x, el_pc := el_pc el + 1\<rparr>)))"  

definition mkStep_0_1 ::
"(estate, eint) State \<Rightarrow> el_step" where
"mkStep_0_1 f el =
  (if el_pc el = max_ueint then crash el
    else
    (case f (el_e el) of
      (v, x) \<Rightarrow> (el \<lparr> el_e := x
                    , el_stack := v # (el_stack el)
                    , el_pc := el_pc el + 1 \<rparr>)))"

definition mkStep_1_0 ::
"(eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_1_0 f el =
  (if el_pc el = max_ueint then crash el
    else
    (case el_stack el of
     vi1#vt \<Rightarrow>
      (case f vi1 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt 
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

definition mkStep_1_1 ::
"(eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_1_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vt \<Rightarrow>
      (case f vi1 (el_e el) of
        (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                        , el_stack := vo1#vt
                       , el_pc := el_pc el + 1\<rparr>))
      | _ \<Rightarrow> crash el))"

definition mkStep_2_0 ::
"(eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_2_0 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vt \<Rightarrow>
      (case f vi1 vi2 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

definition mkStep_2_1 ::
"(eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_2_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vi2#vt \<Rightarrow>
      (case f vi1 vi2 (el_e el) of
        (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                        , el_stack := vo1#vt
                        , el_pc := el_pc el + 1\<rparr>))
    | _ \<Rightarrow> crash el))"

definition mkStep_2_2 ::
"(eint \<Rightarrow> eint \<Rightarrow> (estate, eint * eint) State) \<Rightarrow>
  el_step" where
"mkStep_2_2 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vi2#vt \<Rightarrow>
      (case f vi1 vi2 (el_e el) of
        ((vo1, vo2), x) \<Rightarrow> (el \<lparr> el_e := x
                               , el_stack := vo1#vo2#vt 
                               , el_pc := el_pc el + 1\<rparr>))
    | _ \<Rightarrow> crash el))"


definition mkStep_3_0 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_3_0 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vi3#vt \<Rightarrow>
      (case f vi1 vi2 vi3 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt 
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"


definition mkStep_3_1 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_3_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vi2#vi3#vt \<Rightarrow>
      (case f vi1 vi2 vi3 (el_e el) of
        (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                        , el_stack := vo1#vt
                        , el_pc := el_pc el + 1\<rparr>))
    | _ \<Rightarrow> crash el))"

definition mkStep_3_2 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint * eint) State) \<Rightarrow>
  el_step" where
"mkStep_3_2 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vi2#vi3#vt \<Rightarrow>
      (case f vi1 vi2 vi3 (el_e el) of
        ((vo1, vo2), x) \<Rightarrow> (el \<lparr> el_e := x
                               , el_stack := vo1#vo2#vt 
                               , el_pc := el_pc el + 1\<rparr>))
    | _ \<Rightarrow> crash el))"

definition mkStep_4_0 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_4_0 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vi3#vi4#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt 
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"


definition mkStep_4_1 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_4_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      vi1#vi2#vi3#vi4#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 (el_e el) of
        (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                        , el_stack := vo1#vt 
                        , el_pc := el_pc el + 1\<rparr>))
    | _ \<Rightarrow> crash el))"

definition mkStep_5_0 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_5_0 f el =
  (if el_pc el = max_ueint then crash el
   else  
    (case el_stack el of
     vi1#vi2#vi3#vi4#vi5#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 vi5 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt 
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

definition mkStep_6_0 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, unit) State) \<Rightarrow>
  el_step" where
"mkStep_6_0 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vi3#vi4#vi5#vi6#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 vi5 vi6 (el_e el) of
       ((), x) \<Rightarrow> (el \<lparr> el_e := x
                      , el_stack := vt
                      , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

definition mkStep_6_1 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_6_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vi3#vi4#vi5#vi6#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 vi5 vi6 (el_e el) of
       (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                       , el_stack := vo1#vt
                        , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

definition mkStep_7_1 ::
"(eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> (estate, eint) State) \<Rightarrow>
  el_step" where
"mkStep_7_1 f el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
     vi1#vi2#vi3#vi4#vi5#vi6#vi7#vt \<Rightarrow>
      (case f vi1 vi2 vi3 vi4 vi5 vi6 vi7 (el_e el) of
       (vo1, x) \<Rightarrow> (el \<lparr> el_e := x
                       , el_stack := vo1#vt
                       , el_pc := el_pc el + 1\<rparr>))
     | _ \<Rightarrow> crash el))"

adhoc_overloading mkStep
  mkStep_0_0
  mkStep_0_1

  mkStep_1_0
  mkStep_1_1

  mkStep_2_0
  mkStep_2_1
  mkStep_2_2

  mkStep_3_0
  mkStep_3_1
  mkStep_3_2

  mkStep_4_0
  mkStep_4_1

  mkStep_5_0

  mkStep_6_0
  mkStep_6_1

  mkStep_7_1


(*
 * Assign Yul semantics to steps for which we can
 * (That is, everything except push, pop, dup, swap, jump, jumpdest, pc, gas)
 *)

(* catch-all for unimplemented instructions *)
fun el_bad :: "el_step" where
"el_bad el =
  (el \<lparr> el_crash := True \<rparr>)"

fun el_pop :: "el_step" where
"el_pop el =
  (if el_pc el = max_ueint then crash el
   else
    (case el_stack el of
      [] \<Rightarrow> crash el
      | h#t \<Rightarrow> (el \<lparr> el_stack := t \<rparr>)))"

(* el_dup 0 <==> DUP1 *)
fun el_dup :: "nat \<Rightarrow> el_step" where
"el_dup n el =
  (if el_pc el = max_ueint then crash el
   else
    (let stack = el_stack el in
     (if length stack < n
      then crash el
      else (el \<lparr> el_stack := (stack ! n)#stack \<rparr>))))"

fun swap' :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
"swap' n l =
  (if length l < n + 1
     then None
     else
      (case l of
        [] \<Rightarrow> None
        | sth#stt \<Rightarrow>
           Some ((stt ! n) # take n stt @ (sth # (drop (n+1) stt)))))"

value "swap' 1 [(2 :: nat), 3, 4, 5]"

(* el_swap 0 <==> SWAP1 *)
fun el_swap :: "nat \<Rightarrow> el_step" where
"el_swap n el =
  (if el_pc el = max_ueint then crash el
   else
    (case swap' n (el_stack el) of
     None \<Rightarrow> (el \<lparr> el_crash := True \<rparr>)
     | Some stack' \<Rightarrow> (el \<lparr> el_stack := stack' \<rparr>)))"

(* push instructions need lookahead 
   TODO: make a more general version that actually looks at entire code buffer
   as well as at the pc? actually we do need this even here.
*)
(* push' 0 <==> PUSH1 *)

fun el_push :: "nat \<Rightarrow> el_step" where
"el_push n el =
  (let pc = el_pc el in
  (let n' = word_of_int (int n) :: eint in
  (let code = e_codedata (el_e el) in
    (if pc + n' + 1 \<ge> max_ueint then crash el
     else
      (if n' \<ge> 32 then crash el
       else
        (if n + unat pc \<ge> length code then crash el
         else
          (let bytes = take (n + 1) (drop (unat pc + 1) code) in
           (el \<lparr> el_pc := pc + n' + 2
               , el_stack := word_rcat bytes # el_stack el \<rparr>))))))))"

(* TODO *)
fun el_jump :: "el_step" where
"el_jump x = x"

fun el_jumpi :: "el_step" where
"el_jumpi x = x"

fun el_jumpdest :: "el_step" where
"el_jumpdest x = x"

fun el_getpc :: "el_step" where
"el_getpc x = x"

fun el_getgas :: "el_step" where
"el_getgas x = x"

end