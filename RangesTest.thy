theory RangesTest imports Ranges begin

definition inst_codes :: ranges where
"inst_codes = mk_ranges [(0, 256)]"
declare inst_codes_def [simp]

typedef inst = "set_of_ranges inst_codes"
proof-
  have "(0 :: nat) \<in> {n . n < 256}" by auto
  thus "\<exists> (x :: nat) . x \<in> set_of_ranges inst_codes" 
    unfolding inst_codes_def
    apply(transfer; auto)
    apply(rule_tac x = 0 in exI)
    apply(auto)
    done
qed
setup_lifting type_definition_inst

(* stop *)
definition stop_codes  :: "ranges"  where 
"stop_codes = mk_ranges[(0, 1)]" 
declare stop_codes_def [simp add]
typedef stop_inst = "set_of_ranges stop_codes" 
  unfolding stop_codes_def by (transfer; auto)
setup_lifting type_definition_stop_inst

lift_definition STOP_INST :: "stop_inst \<Rightarrow> inst" is id 
  unfolding stop_codes_def inst_codes_def
  by(transfer; auto)

(* arith*)
definition arith_codes :: "ranges" where 
"arith_codes = mk_ranges [(0x01, 0x0c)]"

declare arith_codes_def [simp add]
typedef arith_inst = "set_of_ranges arith_codes" 
  unfolding arith_codes_def
  apply(transfer)
  apply(auto)
  done
  
setup_lifting type_definition_arith_inst

lift_definition ARITH_INST :: "arith_inst \<Rightarrow> inst" is id 
  unfolding arith_codes_def inst_codes_def
  by(transfer; auto)

(* bits *)
definition bits_codes :: ranges where
"bits_codes = mk_ranges [(0x10, 0x1e)]"

declare bits_codes_def [simp add]
typedef bits_inst = "set_of_ranges bits_codes"
  unfolding bits_codes_def
  by(transfer; auto)
setup_lifting type_definition_bits_inst

lift_definition BITS_INST :: "bits_inst => inst" is id
  unfolding bits_codes_def inst_codes_def
  by(transfer; auto)


definition keccak256_codes :: "ranges" where
"keccak256_codes = mk_ranges [(0x20, 0x21)]"

declare keccak256_codes_def [simp add]
typedef keccak256_inst = "set_of_ranges keccak256_codes"
  unfolding keccak256_codes_def
  by(transfer; auto)
setup_lifting type_definition_keccak256_inst

lift_definition KECCAK256_INST :: "keccak256_inst => inst" is id
  unfolding keccak256_codes_def inst_codes_def
  by(transfer; auto)


definition tx_data_codes :: "ranges" where
"tx_data_codes = mk_ranges [(0x30, 0x40)]"

declare tx_data_codes_def [simp add]
typedef tx_data_inst = "set_of_ranges tx_data_codes"
  unfolding tx_data_codes_def
  by(transfer; auto)
setup_lifting type_definition_tx_data_inst

lift_definition TX_DATA_INST :: "tx_data_inst => inst" is id
  unfolding tx_data_codes_def inst_codes_def
  by(transfer; auto)


definition chain_data_codes :: "ranges" where
"chain_data_codes = mk_ranges [(0x40, 0x48)]"

declare chain_data_codes_def [simp add]
typedef chain_data_inst = "set_of_ranges chain_data_codes"
  unfolding chain_data_codes_def
  by(transfer; auto)
setup_lifting type_definition_chain_data_inst

lift_definition CHAIN_DATA_INST :: "chain_data_inst => inst" is id
  unfolding chain_data_codes_def inst_codes_def
  by(transfer; auto)


definition state_control_codes :: "ranges" where
"state_control_codes = mk_ranges [(0x50, 0x5c)]"

declare state_control_codes_def [simp add]
typedef state_control_inst = "set_of_ranges state_control_codes"
  unfolding state_control_codes_def
  by(transfer; auto)
setup_lifting type_definition_state_control_inst

lift_definition STATE_CONTROL_INST :: "state_control_inst => inst" is id
  unfolding state_control_codes_def inst_codes_def
  by(transfer; auto)


definition push_codes :: "ranges" where
"push_codes = mk_ranges [(0x60, 0x80)]"

declare push_codes_def [simp add]
typedef push_inst = "set_of_ranges push_codes"
  unfolding push_codes_def
  by(transfer; auto)
setup_lifting type_definition_push_inst

lift_definition PUSH_INST :: "push_inst => inst" is id
  unfolding push_codes_def inst_codes_def
  by(transfer; auto)


definition dup_codes :: "ranges" where
"dup_codes = mk_ranges [(0x80, 0x90)]"

declare dup_codes_def [simp add]
typedef dup_inst = "set_of_ranges dup_codes"
  unfolding dup_codes_def
  by(transfer; auto)
setup_lifting type_definition_dup_inst

lift_definition DUP_INST :: "dup_inst => inst" is id
  unfolding dup_codes_def inst_codes_def
  by(transfer; auto)


definition swap_codes :: "ranges" where
"swap_codes = mk_ranges [(0x90, 0xa0)]"

declare swap_codes_def [simp add]
typedef swap_inst = "set_of_ranges swap_codes"
  unfolding swap_codes_def
  by(transfer; auto)
setup_lifting type_definition_swap_inst

lift_definition SWAP_INST :: "swap_inst => inst" is id
  unfolding swap_codes_def inst_codes_def
  by(transfer; auto)


definition log_codes :: "ranges" where
"log_codes = mk_ranges [(0xa0, 0xa5)]"

declare log_codes_def [simp add]
typedef log_inst = "set_of_ranges log_codes"
  unfolding log_codes_def
  by(transfer; auto)
setup_lifting type_definition_log_inst

lift_definition LOG_INST :: "log_inst => inst" is id
  unfolding log_codes_def inst_codes_def
by(transfer; auto)

definition comms_codes :: "ranges" where
"comms_codes = mk_ranges [(0xf0, 0xf6), (0xfa, 0xfb)]"

declare comms_codes_def [simp add]
typedef comms_inst = "set_of_ranges comms_codes"
  unfolding comms_codes_def
  by(transfer; auto)
setup_lifting type_definition_comms_inst

lift_definition COMMS_INST :: "comms_inst => inst" is id
  unfolding comms_codes_def inst_codes_def
  by(transfer; auto)


definition special_halt_codes :: "ranges" where
"special_halt_codes = mk_ranges [(0xfd, 0x100)]"

declare special_halt_codes_def [simp add]
typedef special_halt_inst = "set_of_ranges special_halt_codes"
  unfolding special_halt_codes_def
  by(transfer; auto)
setup_lifting type_definition_special_halt_inst

lift_definition SPECIAL_HALT_INST :: "special_halt_inst => inst" is id
  unfolding special_halt_codes_def inst_codes_def
by(transfer; auto)

definition good_codes :: "ranges" where
"good_codes = Union_ranges
  [stop_codes, 
  arith_codes,
  bits_codes,
  keccak256_codes,
  tx_data_codes,
  chain_data_codes,
  state_control_codes,
  push_codes,
  dup_codes,
  swap_codes,
  log_codes,
  comms_codes,
  special_halt_codes]"

value "good_codes"

typedef good_inst = "set_of_ranges good_codes"
  apply(simp add: good_codes_def)
  apply(transfer) apply(auto)
  done
setup_lifting type_definition_good_inst

lift_definition GOOD_INST :: "good_inst \<Rightarrow> inst" is id
  apply(simp add: good_codes_def)
  apply(transfer) apply(auto)
  done

definition bad_codes :: "ranges" where
"bad_codes = diff_ranges inst_codes good_codes"
typedef bad_inst = "set_of_ranges bad_codes"
  apply(simp add: bad_codes_def good_codes_def)
  apply(transfer) apply(simp)
  apply(auto)
  done
setup_lifting type_definition_bad_inst

lift_definition BAD_INST :: "bad_inst \<Rightarrow> inst" is id
  unfolding bad_codes_def good_codes_def inst_codes_def
  apply(simp)
  apply(transfer) apply(simp)
  apply(auto)
  done

value "union_ranges good_codes bad_codes"

lemma good_bad_all :
  "union_ranges good_codes bad_codes = inst_codes"
  unfolding bad_codes_def good_codes_def
  by(transfer; simp; transfer; auto)

lemma good_bad_all' :
  "Union_ranges [
  stop_codes, 
  arith_codes,
  bits_codes,
  keccak256_codes,
  tx_data_codes,
  chain_data_codes,
  state_control_codes,
  push_codes,
  dup_codes,
  swap_codes,
  log_codes,
  comms_codes,
  special_halt_codes,
  bad_codes] = inst_codes"
  unfolding bad_codes_def good_codes_def
  by(simp; transfer; auto)

lemma cases_inst_helper :
assumes H : "y \<in> set_of_ranges inst_codes"
assumes H1 :  "(\<And>x1. x1 \<in> set_of_ranges stop_codes \<Longrightarrow>
                  y = id x1 \<Longrightarrow> P)"
assumes H2 : "(\<And>x2. x2 \<in> set_of_ranges arith_codes \<Longrightarrow>
                  y = id x2 \<Longrightarrow> P)"
assumes H3 : "(\<And>x3. x3 \<in> set_of_ranges bits_codes \<Longrightarrow>
                  y = id x3 \<Longrightarrow> P)"
assumes H4: "(\<And>x4. x4 \<in> set_of_ranges keccak256_codes \<Longrightarrow>
                  y = id x4 \<Longrightarrow> P)"
assumes H5 : "(\<And>x5. x5 \<in> set_of_ranges tx_data_codes \<Longrightarrow>
                  y = id x5 \<Longrightarrow> P)"
assumes H6 : "(\<And>x6. x6 \<in> set_of_ranges chain_data_codes \<Longrightarrow>
                  y = id x6 \<Longrightarrow> P)"
assumes H7 : "(\<And>x7. x7 \<in> set_of_ranges state_control_codes \<Longrightarrow>
                  y = id x7 \<Longrightarrow> P)"
assumes H8 : "(\<And> x8. x8 \<in> set_of_ranges push_codes \<Longrightarrow>
                  y = id x8 \<Longrightarrow> P)"
assumes H9 : "(\<And>x9. x9 \<in> set_of_ranges dup_codes \<Longrightarrow>
                  y = id x9 \<Longrightarrow> P)"
assumes H10 : "(\<And>x10. x10 \<in> set_of_ranges swap_codes \<Longrightarrow>
                   y = id x10 \<Longrightarrow> P)"
assumes H11 : "(\<And>x11. x11 \<in> set_of_ranges log_codes \<Longrightarrow>
                   y = id x11 \<Longrightarrow> P)"
assumes H12 : "(\<And>x12. x12 \<in> set_of_ranges comms_codes \<Longrightarrow>
                   y = id x12 \<Longrightarrow> P)"
assumes H13 : "(\<And>x13. x13 \<in> set_of_ranges special_halt_codes \<Longrightarrow>
                   y = id x13 \<Longrightarrow> P)"
assumes H14 : "(\<And>x14. x14 \<in> set_of_ranges bad_codes \<Longrightarrow>
                   y = id x14 \<Longrightarrow> P)"
shows P
proof-

  have H' : "member_ranges y (Union_ranges [
          stop_codes, 
          arith_codes,
          bits_codes,
          keccak256_codes,
          tx_data_codes,
          chain_data_codes,
          state_control_codes,
          push_codes,
          dup_codes,
          swap_codes,
          log_codes,
          comms_codes,
          special_halt_codes,
          bad_codes])"
    using H unfolding sym[OF good_bad_all'] member_ranges_spec by(auto)

  have Conc' : "(y = y \<longrightarrow> P)"
  proof(rule Union_ranges_cases[OF _ H', of "\<lambda> x . (y = x \<longrightarrow> P)"] )
    fix r x
    assume R_cases :
    "r \<in> set [stop_codes, arith_codes, bits_codes,
                    keccak256_codes, tx_data_codes,
                    chain_data_codes, state_control_codes,
                    push_codes, dup_codes, swap_codes, log_codes,
                    comms_codes, special_halt_codes,
                    bad_codes]"
    assume R_mem : "member_ranges x r"
    consider (1) "r = stop_codes" | 
             (2) "r = arith_codes" |
             (3) "r = bits_codes" |
             (4) "r = keccak256_codes" |
             (5) "r = tx_data_codes" |
             (6) "r = chain_data_codes" |
             (7) "r = state_control_codes" |
             (8) "r = push_codes" |
             (9) "r = dup_codes" |
             (10) "r = swap_codes" |
             (11) "r = log_codes" |
             (12) "r = comms_codes" |
             (13) "r = special_halt_codes" |
             (14) "r = bad_codes"
      using R_cases by(auto)
    thus "y = x \<longrightarrow> P"
    proof cases
    case 1
      then show ?thesis using H1 R_mem unfolding member_ranges_spec by(auto)
    next
      case 2
      then show ?thesis using H2 R_mem unfolding member_ranges_spec by(auto)
    next
      case 3
      then show ?thesis using H3 R_mem unfolding member_ranges_spec by(auto)
    next
      case 4
      then show ?thesis using H4 R_mem unfolding member_ranges_spec by(auto)
    next
      case 5
      then show ?thesis using H5 R_mem unfolding member_ranges_spec by(auto)
    next
      case 6
      then show ?thesis using H6 R_mem unfolding member_ranges_spec by(auto)
    next
      case 7
      then show ?thesis using H7 R_mem unfolding member_ranges_spec by(auto)
    next
      case 8
      then show ?thesis using H8 R_mem unfolding member_ranges_spec by(auto)
    next
      case 9
      then show ?thesis using H9 R_mem unfolding member_ranges_spec by(auto)
    next
      case 10
      then show ?thesis using H10 R_mem unfolding member_ranges_spec by(auto)
    next
      case 11
      then show ?thesis using H11 R_mem unfolding member_ranges_spec by(auto)
    next
      case 12
      then show ?thesis using H12 R_mem unfolding member_ranges_spec by(auto)
    next
      case 13
      then show ?thesis using H13 R_mem unfolding member_ranges_spec by(auto)
    next
      case 14
      then show ?thesis using H14 R_mem unfolding member_ranges_spec by(auto)
    qed
  qed
  thus ?thesis by auto
qed

(*
  consider
  (1) "y \<in> set_of_ranges stop_codes" |
  (2) "y \<in> set_of_ranges arith_codes" |
  (3) "y \<in> set_of_ranges bits_codes" |
  (4) "y \<in> set_of_ranges keccak256_codes" |
  (5) "y \<in> set_of_ranges tx_data_codes" |
  (6) "y \<in> set_of_ranges chain_data_codes" |
  (7) "y \<in> set_of_ranges state_control_codes" |
  (8) "y \<in> set_of_ranges push_codes" |
  (9) "y \<in> set_of_ranges dup_codes" |
  (10) "y \<in> set_of_ranges swap_codes" |
  (11) "y \<in> set_of_ranges log_codes" |
  (12) "y \<in> set_of_ranges comms_codes" |
  (13) "y \<in> set_of_ranges special_halt_codes" |
  (14) "y \<in> set_of_ranges bad_codes"
    apply(simp add: good_codes_def bad_codes_def)
    apply(transfer)
    apply(auto)
    done
  then show P
  proof cases
    case 1
  then show ?thesis usin
next
  case 2
  then show ?thesis sorry
next
  case 3
  then show ?thesis sorry
next
  case 4
  then show ?thesis sorry
next
  case 5
  then show ?thesis sorry
next
  case 6
  then show ?thesis sorry
next
  case 7
  then show ?thesis sorry
next
    case 8
    then show ?thesis sorry
  next
    case 9
    then show ?thesis sorry
  next
    case 10
    then show ?thesis sorry
  next
    case 11
    then show ?thesis sorry
  next
    case 12
    then show ?thesis sorry
  next
    case 13
    then show ?thesis sorry
  next
    case 14
    then show ?thesis sorry
  qed
*)
(*
free_constructors cases_inst for
STOP_INST
| ARITH_INST
| BITS_INST
| KECCAK256_INST
| TX_DATA_INST
| CHAIN_DATA_INST
| STATE_CONTROL_INST
| PUSH_INST
| DUP_INST
| SWAP_INST
| LOG_INST
| COMMS_INST
| SPECIAL_HALT_INST
| BAD_INST
  apply(transfer)
  apply(rule cases_inst_helper; blast)
  apply(transfer; simp add: bad_codes_def good_codes_def; transfer; force; fail)+
  done
*)
end