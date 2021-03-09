theory GlobalEvm
  imports MiniEvm
begin

(* need global EVM stack elements. *)

(* 

EVM global state (as needed for transaction execution)
- global metadata: gasprice, blockhash, coinbase, timestamp, blocknumber,
  difficulty, gaslimit, chainid
- accounts: 2 types
  - wallet = just balance
  - contract = code (binary + semantic), balance

- ok, how do we deal with cross-contract calls?
  - there is a weird kind of circularity
  - because in order to implement the call builtin, we need global state
  - but, in order to imple
*)

(* TODO: consolidate this with MinEvm estate_metadata *)
(* global metadata *)
record emeta =
  em_gasprice :: eint
  em_blockhash :: eint
  em_coinbase :: eint
  em_timestamp :: eint
  em_blocknumber :: eint
  em_difficulty :: eint
  em_gaslimit :: eint
  em_chainid :: eint
  em_selfbalance :: eint

(* external contract state *)
record eacct =
  ea_balance :: eint
  ea_nonce :: eint

record eacct_smart = eacct +
  ea_codedata :: "8 word list"
  (* is this type correct? *)
  ea_codesem :: "eint \<Rightarrow> (estate, unit) State"
  ea_storage :: "eint \<Rightarrow> eint"

datatype Acct =
  Acct eacct
  | SmartAcct eacct_smart

record eglobal =
  eg_accts :: "eint \<Rightarrow> Acct option"
  eg_meta :: emeta

(* when transitioning between smart contracts, we need to create
   a new local state from a combination of local and global. *)
(* TODO: need to correctly update caller, callvalue *)
fun update_estate_with_acct :: 
  "eacct_smart \<Rightarrow> estate \<Rightarrow> estate" where
"update_estate_with_acct a e =
  (e \<lparr> e_memory := []
     , e_msize := 0
     , e_selfbalance := (ea_balance a)
     , e_codedata := ea_codedata a
     , e_storage := (ea_storage a)
     , e_log := [] \<rparr>)"

fun update_acct_with_estate ::
  "estate \<Rightarrow> eacct_smart \<Rightarrow> eacct_smart" where
"update_acct_with_estate e a =
  (a \<lparr> ea_balance := e_selfbalance e
     , ea_storage := e_storage e \<rparr> )"

(* to invoke a transaction, we submit
   address, calldata, value, gas,  *)
(* TODO: nonce, GasPrice, GasLimit, v/r/s (EIP155) *)
(*
   idea:
   - get code from address
   - construct estate
   - run until we hit a flag/end
   - potential problem: dealing with
     termination issues inside contracts this way
*)

(*
fun eval_global_step ::
  "eaddr \<Rightarrow> 
   ebyte list \<Rightarrow>
   eint \<Rightarrow>
   eint \<Rightarrow>
   eglobal \<Rightarrow> 
   nat \<Rightarrow>
   eglobal" where
"eval_global_step addr calldata value gas state =
 *)


end