theory EvmInterpreter imports EvmBytecode MiniEvm "HOL-Library.Adhoc_Overloading" "../Utils/Hex"
begin

(* parsing hex inputs 
 * because of the free constructors (I think) we can't define
   this directly, which would be the natural thing to do.
*)

(*
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

value "parse_byte_inst 0"
*)
(*
 * Begin the actual interpreter
 *)

definition parse_hex_str_eint :: "char list \<Rightarrow> eint" where
"parse_hex_str_eint l = word_rcat (hex_splits l)"

definition parse_dec_str_eint :: "char list \<Rightarrow> eint" where
"parse_dec_str_eint l = word_of_int (decread l)"


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

fun el_jump :: "el_step" where
"el_jump el = 
  (case el_stack el of
   [] \<Rightarrow> crash el
   | h#t \<Rightarrow>
     (el \<lparr> el_pc := h
         , el_stack := t \<rparr>))
"

fun el_jumpi :: "el_step" where
"el_jumpi el = 
  (case el_stack el of
    dst#cond#t \<Rightarrow>
      (if cond = 0
       then
        (if el_pc el = max_ueint then crash el
         else (el \<lparr> el_pc := el_pc el + 1
                  , el_stack := t \<rparr>))
        else (el \<lparr> el_pc := dst
                 , el_stack := t \<rparr>))
    | _ \<Rightarrow> crash el)"

fun el_jumpdest :: "el_step" where
"el_jumpdest el = 
  (if el_pc el = max_ueint then crash el
   else (el \<lparr> el_pc := el_pc el + 1 \<rparr>))"

fun el_getpc :: "el_step" where
"el_getpc el = 
  (if el_pc el = max_ueint then crash el
  else (el \<lparr> el_stack := (el_pc el) # el_stack el
           , el_pc := el_pc el + 1 \<rparr>))"

fun el_getgas :: "el_step" where
"el_getgas el = 
  (if el_pc el = max_ueint then crash el
   else (el \<lparr> el_stack := e_gas (el_e el) # el_stack el
            , el_pc := el_pc el + 1 \<rparr>))"

fun get_inst :: "estate_ll \<Rightarrow> inst" where
"get_inst el =
  (if unat (el_pc el) < length (e_codedata (el_e el)) then eSTOP
   else parse_byte_inst (e_codedata (el_e el) ! (unat (el_pc el))))"



(*
 * Semantics of a single instruction execution
 *)
fun el_step :: "inst \<Rightarrow> el_step" where
"el_step eSTOP = mkStep ei_stop"
| "el_step eADD = mkStep ei_add"
| "el_step eMUL = mkStep ei_mul"
| "el_step eSUB = mkStep ei_sub"
| "el_step eDIV = mkStep ei_div"
| "el_step eSDIV = mkStep ei_sdiv"
| "el_step eMOD = mkStep ei_mod"
| "el_step eSMOD = mkStep ei_smod"
| "el_step eADDMOD = mkStep ei_addmod"
| "el_step eMULMOD = mkStep ei_mulmod"
| "el_step eEXP = mkStep ei_exp"
| "el_step eSIGNEXTEND = mkStep ei_signextend"
| "el_step eLT = mkStep ei_lt"
| "el_step eGT = mkStep ei_gt"
| "el_step eSLT = mkStep ei_slt"
| "el_step eSGT = mkStep ei_sgt"
| "el_step eEQ = mkStep ei_eq"
| "el_step eISZERO = mkStep ei_iszero"
| "el_step eAND = mkStep ei_and"
| "el_step eOR = mkStep ei_or"
| "el_step eXOR = mkStep ei_xor"
| "el_step eNOT = mkStep ei_not"
| "el_step eBYTE = mkStep ei_byte"
| "el_step eSHL = mkStep ei_shl"
| "el_step eSHR = mkStep ei_shr"
| "el_step eSAR = mkStep ei_sar"
| "el_step eKECCAK256 = mkStep ei_keccak256"
| "el_step eADDRESS = mkStep ei_address"
| "el_step eBALANCE = mkStep ei_balance"
| "el_step eORIGIN = mkStep ei_origin"
| "el_step eCALLER = mkStep ei_caller"
| "el_step eCALLVALUE = mkStep ei_callvalue"
| "el_step eCALLDATALOAD = mkStep ei_calldataload"
| "el_step eCALLDATASIZE = mkStep ei_calldatasize"
| "el_step eCALLDATACOPY = mkStep ei_calldatacopy"
| "el_step eCODESIZE = mkStep ei_codesize"
| "el_step eCODECOPY = mkStep ei_codecopy"
| "el_step eGASPRICE = mkStep ei_gasprice"
| "el_step eEXTCODESIZE = mkStep ei_extcodesize"
| "el_step eEXTCODECOPY = mkStep ei_extcodecopy"
| "el_step eRETURNDATASIZE = mkStep ei_returndatasize"
| "el_step eRETURNDATACOPY = mkStep ei_returndatacopy"
| "el_step eEXTCODEHASH = mkStep ei_extcodehash"
| "el_step eBLOCKHASH = mkStep ei_blockhash"
| "el_step eCOINBASE = mkStep ei_coinbase"
| "el_step eTIMESTAMP = mkStep ei_timestamp"
| "el_step eNUMBER = mkStep ei_number"
| "el_step eDIFFICULTY = mkStep ei_difficulty"
| "el_step eCHAINID = mkStep ei_chainid"
| "el_step eSELFBALANCE = mkStep ei_selfbalance"
| "el_step ePOP = mkStep ei_pop"
| "el_step eMLOAD = mkStep ei_mload"
| "el_step eMSTORE = mkStep ei_mstore"
| "el_step eMSTORE8 = mkStep ei_mstore8"
| "el_step eSLOAD = mkStep ei_sload"
| "el_step eSSTORE = mkStep ei_sstore"
| "el_step eJUMP = el_jump"
| "el_step eJUMPI = el_jumpi"
| "el_step ePC = el_getpc"
| "el_step eMSIZE = mkStep ei_msize"
| "el_step eGAS = mkStep ei_gas"
| "el_step eJUMPDEST = mkStep ei_jumpdest"
| "el_step eLOG0 = mkStep ei_log0"
| "el_step eLOG1 = mkStep ei_log1"
| "el_step eLOG2 = mkStep ei_log2"
| "el_step eLOG3 = mkStep ei_log3"
| "el_step eLOG4 = mkStep ei_log4"
| "el_step eCREATE = mkStep ei_create"
| "el_step eCALL = mkStep ei_call"
| "el_step eCALLCODE = mkStep ei_callcode"
| "el_step eRETURN = mkStep ei_return"
| "el_step eDELEGATECALL = mkStep ei_delegatecall"
| "el_step eCREATE2 = mkStep ei_create2"
| "el_step eSTATICCALL = mkStep ei_staticcall"
| "el_step eREVERT = mkStep ei_revert"
| "el_step eINVALID = mkStep ei_invalid"
| "el_step eSELFDESTRUCT = mkStep ei_selfdestruct"
| "el_step _ = mkStep ei_invalid"


(* execution *)
fun evm_exec' :: "estate_ll \<Rightarrow> nat \<Rightarrow> estate_ll option" where
"evm_exec' el 0 = None"
| "evm_exec' el (Suc n) =
   (if is_Executing (e_flag (el_e el))
    then
      (if el_crash el then Some el
       else
        (let next_inst = get_inst el in
        (let next_state = el_step next_inst el in
         evm_exec' next_state n)))
    else Some el)"

definition evm_exec :: "estate_ll \<Rightarrow> estate_ll option" where
"evm_exec el = evm_exec' el 10000"

definition evm_exec_check :: "estate_ll \<Rightarrow> (estate_ll \<Rightarrow> bool) \<Rightarrow> bool" where
"evm_exec_check el P =
 (case evm_exec el of
  None \<Rightarrow> False
  | Some final \<Rightarrow> P final)"

(*
 * storage
*)
type_synonym storage_spec = "(eint * eint) list"

fun setup_storage :: "storage_spec \<Rightarrow> (eint \<Rightarrow> eint)" where
"setup_storage [] i = 0"
| "setup_storage ((k, v)#t) i =
   (if i = k then v
    else setup_storage t i)"

(*
check final storage 
   NB: this does not check that unspecified
   storage locations must be empty (0)
*)
fun check_storage :: "estate_ll \<Rightarrow> storage_spec \<Rightarrow> bool" where
"check_storage el [] = True"
| "check_storage el ((k, v)#t) =
   ((e_storage (el_e el) k = v) \<and> check_storage el t)"


(* starting state *)
definition dummy_estate_ll :: "estate_ll" where
"dummy_estate_ll =
  \<lparr> el_e = dummy_estate
  , el_stack = []
  , el_pc = 0
  , el_crash = False \<rparr>"

end