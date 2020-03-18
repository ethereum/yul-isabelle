theory AbiDecode imports AbiTypes Hex
begin
(* NB the caller of these functions will pass in a long
   enough list *)
fun decode_uint :: "8 word list \<Rightarrow> int" where
"decode_uint l =
  (Word.uint (Word.word_rcat (take 32 l) :: 256 word))"

lemma decode_uint_max :
"\<And> (x :: 256 word) . Word.uint x \<le>  max_u256"
  apply(cut_tac x = "x :: 256 word" in Word.uint_range')
  apply(auto simp add:max_u256_def)
  done

fun decode_sint :: "8 word list \<Rightarrow> int" where
"decode_sint l =
  (Word.sint (Word.word_rcat (take 32 l) :: 256 word))"

fun decode_bool :: "8 word list \<Rightarrow> bool option" where
"decode_bool l =
  (let i = decode_uint l in
   (if i = 0 then Some False
              else if i = 1 then Some True
              else None))"

fun decode_ufixed :: "nat \<Rightarrow> 8 word list \<Rightarrow> rat" where
"decode_ufixed n l =
  (let i = decode_uint l in (Rat.of_int i / (10 ^ n)))"

fun decode_fixed :: "nat \<Rightarrow> 8 word list \<Rightarrow> rat" where
"decode_fixed n l =
  (let i = decode_sint l in (Rat.of_int i / (10 ^ n)))"

(* extract byte strings of known length *)
fun decode_fbytes :: "nat \<Rightarrow> 8 word list \<Rightarrow> 8 word list" where
"decode_fbytes n l = (take n l)"


(* for dynamic types we need to use the input list to calculate size *)
(*
fun abi_type_measure_dyn :: "abi_type \<Rightarrow> int"
and abi_type_list_measure_dyn :: "abi_type list \<Rightarrow> nat" where
"abi_type_measure_dyn (Ttuple ts) = 
  1 + abi_type_list_measure_dyn ts"
| "abi_type_measure_dyn (Tfarray t n) = 1 + n + (abi_type_measure_dyn t)"
| "abi_type_measure_dyn (Tarray t) = 
    1 + (2 ^ 256) + abi_type_measure_dyn t" (* curious about this one *)
| "abi_type_measure_dyn _ _ = 1"

| "abi_type_list_measure_dyn [] l = 1"
| "abi_type_list_measure_dyn (th#tt) l =
    abi_type_measure_dyn th + 
    abi_type_list_measure_dyn + 1"
*)
(* here, again, we assume we have been passed a correct length byte string
   other than booleans, we aren't doing value checks here *)
(* TODO: enforce that correct size word list was passed in?
   otherwise we risk discarding data *)
abbreviation Ok :: "'a \<Rightarrow> 'a orerror" where
"Ok \<equiv> Inl"

abbreviation Err :: "char list \<Rightarrow> 'a orerror" where
"Err \<equiv> Inr"


lemma abi_type_list_measure_replicate :
  "\<And> t . abi_type_list_measure (replicate n t)
           =  1 + n + (n * abi_type_measure t)"
proof(induction n)
  case 0
  then show ?case
    apply(simp)
    done
next
  case (Suc n)
  then show ?case 
    apply(simp)
    done
qed

fun locate_err :: "char list \<Rightarrow> (int * 8 word list) \<Rightarrow> char list"
  where
"locate_err s (ix, l) =
  s @ '' at byte '' @ decwrite (nat ix) @ '' of '' @ decwrite (length l) @ ''.''"

function (sequential) decode_static :: "abi_type \<Rightarrow> (int * 8 word list) \<Rightarrow> abi_value orerror" 
(*and decode_static_arr :: "abi_type \<Rightarrow> nat \<Rightarrow> 8 word list \<Rightarrow> abi_value list option"*)
and decode_static_tup :: "abi_type list \<Rightarrow> (int * 8 word list) \<Rightarrow> abi_value list orerror" where
"decode_static (Tuint n) (ix, l) =
   (let l' = drop (nat ix) l in
   (let res = decode_uint l' in
    (if uint_value_valid n res then Ok (Vuint n res)
     else Err (locate_err ''Invalid uint'' (ix, l)))))"
| "decode_static (Tsint n) (ix, l) =
   (let l' = drop (nat ix) l in
   (let res = decode_sint l' in
    (if sint_value_valid n res then Ok (Vsint n res)
     else Err (locate_err ''Invalid sint'' (ix, l)))))"
| "decode_static Taddr (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_uint l' in
    (if addr_value_valid res then Ok (Vaddr res)
     else Err (locate_err ''Invalid address'' (ix, l)))))"
| "decode_static Tbool (ix, l) =
  (let l' = drop (nat ix) l in
   (case decode_bool l' of
      None \<Rightarrow> Err (locate_err ''Invalid bool'' (ix, l))
      | Some b \<Rightarrow> Ok (Vbool b)))"
| "decode_static (Tfixed m n) (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_fixed m l' in
    (if fixed_value_valid m n res then Ok (Vfixed m n res)
     else Err (locate_err ''Invalid fixed'' (ix, l)))))"
| "decode_static (Tufixed m n) (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_ufixed m l' in
    (if ufixed_value_valid m n res then Ok (Vufixed m n res)
     else Err (locate_err ''Invalid ufixed'' (ix, l)))))"
| "decode_static (Tfbytes n) (ix, l) =
  (let l' = drop (nat ix) l in
   (let res = decode_fbytes n l' in
    (if fbytes_value_valid n res then Ok (Vfbytes n res)
     else Err (locate_err ''Invalid fbytes'' (ix, l)))))"
| "decode_static (Tfarray t n) (ix, l) =
  (case decode_static_tup (List.replicate n t) (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok vs \<Rightarrow> 
        (if farray_value_valid_aux t n vs then Ok (Vfarray t n vs)
         else Err (locate_err ''Invalid farray'' (ix, l))))"
| "decode_static (Ttuple ts) (ix, l) = 
  (case decode_static_tup ts (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok vs \<Rightarrow> 
      (if tuple_value_valid_aux ts vs then Ok (Vtuple ts vs)
       else Err (locate_err ''Invalid tuple'' (ix, l))))"
| "decode_static _ (ix, l) = Err (locate_err ''Ran static parser on dynamic array'' (ix, l))"
(*
| "decode_static_arr t 0 l = Some []"
| "decode_static_arr t (Suc n) l =
    (case decode_static t 
                   (take (nat (abi_static_size t)) l) of
      None \<Rightarrow> None
      | Some v \<Rightarrow> (case decode_static_arr t n
                       (drop (nat (abi_static_size t)) l) of
          None \<Rightarrow> None
          | Some vs \<Rightarrow> Some (v#vs)))"
*)
| "decode_static_tup [] (ix, l) = Ok []"

(* i don't think the "take" that is done here actually matters. *)
(*
| "decode_static_tup (t#ts) (ix, l) =
    (case decode_static t 
                   (take (nat (abi_static_size t)) l) of
      Err s \<Rightarrow> Err s
      | Ok v \<Rightarrow> (case decode_static_tup ts 
                       (drop (nat (abi_static_size t)) l) of
          Err s \<Rightarrow> Err s
          | Ok vs \<Rightarrow> Ok (v#vs)))"
*)

| "decode_static_tup (t#ts) (ix, l) =
    (case decode_static t (ix, l) of
      Err s \<Rightarrow> Err s
      | Ok v \<Rightarrow> (case decode_static_tup ts 
                       (ix + (abi_static_size t), l) of
          Err s \<Rightarrow> Err s
          | Ok vs \<Rightarrow> Ok (v#vs)))"


  by pat_completeness auto

termination
(*
apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> abi_type_measure t + length l
      | Inr (Inl (t, n, l)) \<Rightarrow> abi_type_measure t + n + length l
      | Inr (Inr (ts, l)) \<Rightarrow> abi_type_list_measure ts + length l))")
        apply(auto)
*)
apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> 1 + abi_type_measure t
      | Inr (ts, l) \<Rightarrow> abi_type_list_measure ts))")
      apply(simp) apply(simp)
  apply(simp add:abi_type_list_measure_replicate)
  apply(simp) apply(simp)
   apply(case_tac ts; auto)
   apply(case_tac a; auto)
  done
  
(*
termination
  apply(relation
    "

  apply(relation 
"measure (\<lambda> x .
    (case x of
      Inl (t, l) \<Rightarrow> abi_type_empties t + length l
      | Inr (Inl (t, n, l)) \<Rightarrow> (n * abi_type_empties t) + length l
      | Inr (Inr (ts, l)) \<Rightarrow> abi_type_list_empties ts + length l))")       
        apply(fastforce)
       apply(fastforce) apply(clarsimp)
  apply(case_tac ts) apply(clarsimp) apply(clarsimp)
     apply(clarsimp)
  apply(case_tac t, auto)
  apply(case_tac n) apply(auto)
     apply(case_tac l, auto)
  done
*)

fun bytes_to_string :: "8 word list \<Rightarrow> char list" where
"bytes_to_string bs =
  List.map (\<lambda> b . char_of_integer (integer_of_int (Word.uint b))) bs"

fun tails_measure :: "(abi_value + (abi_type * nat)) list \<Rightarrow> nat" where
"tails_measure [] = 1"
| "tails_measure ((Inl _)#ts) = 1 + tails_measure ts"
| "tails_measure ((Inr (t, _))#ts) =
    abi_type_measure t + tails_measure ts"

(* TODO: need to deal with padding bytes to 256-words *)
fun skip_padding :: "nat \<Rightarrow> nat" where
"skip_padding n =
  (case divmod_nat n 32 of
    (_, 0) \<Rightarrow> n
    | (_, rem) \<Rightarrow> n + 32 - rem)" (* was n + rem *)

(* in order to support negative offsets, we need to keep the entire list around always. *)

function (sequential) decode' :: "abi_type \<Rightarrow> (int * 8 word list) \<Rightarrow> (abi_value * int) orerror"

(*
and decode'_dyn_array :: "abi_type \<Rightarrow> int \<Rightarrow> (int * 8 word list) \<Rightarrow> (abi_value list * int) orerror"
*)
(* first returned nat is the length of all the heads (used for computing offsets); 
   second returned nat is number of bytes consumed;
   input nat is running count of head length. *)
and decode'_dyn_tuple_heads :: "abi_type list \<Rightarrow> int \<Rightarrow> (int * 8 word list) \<Rightarrow> 
                (abi_value option list *  (nat option) list * int * int) orerror"
(* list parameter gives an offset for each field that still needs to be parsed
   the nat parameter is an index of how many bytes into our overall tuple encoding we are *)
and decode'_dyn_tuple_tails :: "(nat option) list \<Rightarrow> abi_type list \<Rightarrow> abi_value option list \<Rightarrow> int \<Rightarrow> (int * 8 word list) \<Rightarrow> 
                (abi_value list * int) orerror"
where
(* we need to zip earlier. *)
"decode' t (ix, l) =
 (let l' = drop (nat ix) l in
  (let decode'_dyn_array  = (\<lambda> t (n :: int) (ixl :: (int * 8 word list)) .
    (case ixl of (ix, l) \<Rightarrow>
    (let ts = List.replicate (nat n) t in
    (case decode'_dyn_tuple_heads ts 0 (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
\<^cancel>\<open>this used to drop bytes parsed\<close>
            (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vs, bytes_parsed') \<Rightarrow> (Ok (vs, bytes_parsed + bytes_parsed') :: (abi_value list * int) orerror))))))
  in
  (if abi_type_isstatic t
    then
      if int (length l) < (abi_static_size t) + ix then Err (locate_err ''Too few bytes for given static type'' (ix, l))
      else (case decode_static t (ix, l) of
            Err s \<Rightarrow> Err s
            | Ok v \<Rightarrow> Ok (v, (abi_static_size t)))
   else
    (case t of
      Tfarray t n \<Rightarrow>
        (case decode'_dyn_array t n (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vs, bytes_parsed) \<Rightarrow> Ok (Vfarray t n vs, bytes_parsed))
      | Tarray t \<Rightarrow>
       if int (length l) < 32 + ix then Err (locate_err ''Too few bytes; could not read array size'' (ix, l))
        else let n = (decode_uint (take 32 l')) in
        (case decode'_dyn_array t n (ix + 32, l) of
          Err s \<Rightarrow> Err s
          | Ok (vs, bytes_parsed) \<Rightarrow> Ok (Varray t vs, bytes_parsed + 32))
      | Ttuple ts \<Rightarrow>
        (case decode'_dyn_tuple_heads ts 0 (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
\<^cancel>\<open>this used to drop bytes parsed\<close>
            (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vs, bytes_parsed') \<Rightarrow> Ok (Vtuple ts vs, bytes_parsed + bytes_parsed')))
      | Tbytes \<Rightarrow>
        if int (length l) < 32 + ix then Err (locate_err ''Too few bytes; could not read bytestream size'' (ix, l))
        else let sz = (decode_uint (take 32 l')) in
             if int (length l) < sz + 32 + ix then Err (locate_err ''Fewer bytes remaining than bytestream size'' (ix, l))
             else Ok (Vbytes (take (nat sz) (drop 32 l')), int(skip_padding (nat sz)) + 32)
      | Tstring \<Rightarrow> 
        if int(length l) < 32 + ix then Err (locate_err ''Too few bytes; could not read string size'' (ix, l))
        else let sz = (decode_uint (take 32 l')) in
             if int (length l) < sz + 32 + ix then Err (locate_err ''Fewer bytes remaining than string size'' (ix, l))
             else Ok (Vstring (bytes_to_string (take (nat sz) (drop 32 l'))), int (skip_padding (nat sz)) + 32)
      | _ \<Rightarrow> Err (locate_err ''This should be dead code'' (ix, l))))))"

(*| "decode_dyn_array t 0 [] = Some ([], [])"
| "decode_dyn_array t n [] = None" *)
(* TODO: error messages for the array will be confusing in that they will talk
about tuples *)
(* TODO: make this not mutually recursive.
*)
(*
| "decode'_dyn_array t n (ix, l) =
    (let ts = List.replicate (nat n) t in
    (case decode'_dyn_tuple_heads ts 0 (ix, l) of
          Err s \<Rightarrow> Err s
          | Ok (vos, idxs, byteoffset, bytes_parsed) \<Rightarrow>
\<^cancel>\<open>this used to drop bytes parsed\<close>
            (case decode'_dyn_tuple_tails idxs ts vos byteoffset (ix, l) of
              Err s \<Rightarrow> Err s
              | Ok (vs, bytes_parsed') \<Rightarrow> Ok (vs, bytes_parsed + bytes_parsed'))))"
*)
| "decode'_dyn_tuple_heads [] n (ix, l) = Ok ([], [], n, 0)"
| "decode'_dyn_tuple_heads (th#tt) n (ix, l) =
  (let l' = drop (nat ix) l in
    (if abi_type_isstatic th
      then (case decode' th (ix, l) of
        Err s \<Rightarrow> Err s
        | Ok (v, bytes_parsed) \<Rightarrow>
          (case decode'_dyn_tuple_heads tt (n + (abi_static_size th)) (ix + bytes_parsed, l) of
            Err s \<Rightarrow> Err s
            | Ok (vos, idxs, n', bytes_parsed') \<Rightarrow> Ok (Some v # vos, None#idxs, n', bytes_parsed + bytes_parsed')))
    else
      (if length l' < 32 then Err (locate_err ''Too few bytes; could not read tuple head'' (ix, l))
       else let sz = (decode_uint (take 32 l)) in
            (case decode'_dyn_tuple_heads tt (n + 32) (ix + 32, l) of
              Err s \<Rightarrow> Err s
\<^cancel>\<open>Some n + sz used to be Some n\<close>

              | Ok (vos, idxs, n', bytes_parsed) \<Rightarrow> Ok (None # vos, (Some (nat sz))#idxs, n', bytes_parsed + 32)))))"

| "decode'_dyn_tuple_tails [] [] []  _ (ix, l) = Ok ([], 0)"
| "decode'_dyn_tuple_tails (None#t) (th#tt) (Some vh#vt) offset (ix, l) = 
   (case decode'_dyn_tuple_tails t tt vt offset (ix, l) of
    Err s \<Rightarrow> Err s
    | Ok (vs, bytes_parsed) \<Rightarrow> Ok (vh#vs, bytes_parsed))"

(*
| "decode'_dyn_tuple_tails ((Some toffset)#t) (th#tt) (None#vt) offset l =
   (let l' = drop toffset l in
       (case decode' th l' of
              Err s \<Rightarrow> Err s
              | Ok (v, bytes_parsed) \<Rightarrow>
                     let offset' = offset + bytes_parsed in
                     (case decode'_dyn_tuple_tails t tt vt offset' (l) of
                           Err s \<Rightarrow> Err s
                           | Ok (vs, bytes_parsed') \<Rightarrow> Ok (v#vs, bytes_parsed + bytes_parsed'))))                          
      "
*)


| "decode'_dyn_tuple_tails ((Some toffset)#t) (th#tt) (None#vt) offset (ix, l) =
   (let ix' = ix + int (toffset) in
       (case decode' th (ix', l) of
              Err s \<Rightarrow> Err s
              | Ok (v, bytes_parsed) \<Rightarrow>
                     let offset' = offset + bytes_parsed in
                     (case decode'_dyn_tuple_tails t tt vt offset' (ix, l) of
                           Err s \<Rightarrow> Err s
                           | Ok (vs, bytes_parsed') \<Rightarrow> Ok (v#vs, bytes_parsed + bytes_parsed'))))                          
      "

| "decode'_dyn_tuple_tails _ _ _ _ (ix, l) = Err (locate_err ''Should be dead code'' (ix, l))"

(*
| "decode_dyn_tuple_tails (Inl v # t) n l =
   (case decode_dyn_tuple_tails t n l of
      None \<Rightarrow> None
      | Some (vs, bytes_parsed) \<Rightarrow> Some (v#vs, bytes_parsed))"
(* is it too strict to force offset to equal n? *)
| "decode_dyn_tuple_tails (Inr (typ, offset) # t) n l =
  (if offset \<noteq> n then None
   else (case decode typ l of
          None \<Rightarrow> None
          | Some (v, bytes_parsed) \<Rightarrow>
            let n' = n + (length l - bytes_parsed) in
            (case decode_dyn_tuple_tails t n' (drop bytes_parsed l) of
              None \<Rightarrow> None
              | Some (vs, bytes_parsed') \<Rightarrow> Some (v#vs, bytes_parsed + bytes_parsed'))))"
*)
  by pat_completeness auto

(*
abbreviation decode_nocheck_dom where
"decode_nocheck_dom \<equiv>
decode_nocheck_decode_dyn_nocheck_array_decode_dyn_nocheck_tuple_heads_decode_dyn_nocheck_tuple_tails_dom"

lemma decode_dyn_suffix :
  fixes t
  shows "\<And> l v l' . 
          decode_nocheck_dom (Inl (Inl (t, l))) \<Longrightarrow>
          decode_nocheck t l = Some (v, l') \<Longrightarrow>
          \<exists> n . l' = drop n l"
  apply(induction t)
              apply(auto simp add: decode_nocheck.psimps split:if_splits option.splits)
      apply(case_tac t, auto split:option.splits)
  
  apply(case_tac l, auto)
*)
(*
lemma tails_measure_bound [rule_format] :
fixes x
shows "\<forall> n l a aa b .
      (decode_dyn_nocheck_tuple_heads x n l = Some (a, aa, b) \<longrightarrow>
       decode_nocheck_decode_dyn_nocheck_array_decode_dyn_nocheck_tuple_heads_decode_dyn_nocheck_tuple_tails_dom
        (Inr (Inl (x, n, l))) \<longrightarrow>
      tails_measure a \<le> abi_type_list_measure x)" 
  apply(induction x)
   apply(auto simp add:decode_dyn_nocheck_tuple_heads.psimps)
  apply(auto split: if_splits option.splits prod.splits)
   apply(drule_tac x = "(n + nat (abi_static_size a))" in spec)
   apply(drule_tac x = "(drop x2a l)" in spec)
   apply(drule_tac x = x1a in spec)
   apply(auto)
  apply(case_tac n)
apply(frule_tac decode_dyn_nocheck_tuple_heads.psimps) apply(auto)
*)

fun somes :: "'a option list \<Rightarrow> 'a list" where
"somes [] = []"
| "somes (None#t) = somes t"
| "somes (Some h#t) = h # somes t"

lemma abi_type_measure_nonzero :
  "\<And> t . abi_type_measure t > 0"
  apply(induct_tac t; auto)
  done

termination decode'

  
(*
  apply(relation 
"measure (\<lambda> x .
    (case x of
       Inl (Inl (t, l)) \<Rightarrow> abi_type_measure t + length l 
      | Inl (Inr (t, n, l)) \<Rightarrow> n * abi_type_measure t + length l
      | Inr (Inl (ts,  n, l)) \<Rightarrow> abi_type_list_measure ts + length l
      | Inr (Inr (idxs, ts, vs, n, l)) \<Rightarrow> abi_type_list_measure ts + length l))")   
             apply(auto)
  (* array case: length < 2^256 - 1 *)
  apply(cut_tac w = "(word_rcat (take 32 l) :: 256 word)" in Word.uint_lt)
    apply(simp add:max_u256_def) 
   defer
  sorry
*)
(* this one works for "hard" case *)
(*
  apply(relation 
"measure (\<lambda> x .
    (case x of
       Inl (Inl (t, (ix, l))) \<Rightarrow> 2 + abi_type_measure t
      | Inl (Inr (t, n, (ix, l))) \<Rightarrow> 1 + abi_type_list_measure (replicate (nat n) t)
      | Inr (Inl (ts,  n, (ix, l))) \<Rightarrow>  abi_type_list_measure ts
      | Inr (Inr (idxs, ts, vs, n, (ix, l))) \<Rightarrow> abi_type_list_measure ts))")   
*)

  apply(relation 
"measure (\<lambda> x .
    (case x of
       (Inl (t, (ix, l))) \<Rightarrow> 1 + abi_type_measure t
      | Inr (Inl (ts,  n, (ix, l))) \<Rightarrow> abi_type_list_measure ts
      | Inr (Inr (idxs, ts, vs, n, (ix, l))) \<Rightarrow> abi_type_list_measure ts))")   

              apply(clarsimp)
             apply(clarsimp)
  apply(simp add: abi_type_list_measure_replicate)
            apply(clarsimp)
           apply(clarsimp)
(* first case we get stuck on
decode' vs decode'_dyn_array *)
          apply(clarsimp)
  apply(cut_tac w = "(word_rcat (take 32 (drop (nat ix) l)) :: 256 word)" in Word.uint_lt)
          apply(simp add:max_u256_def)
          apply(cut_tac t = x13 in abi_type_measure_nonzero)
          apply(simp add: abi_type_list_measure_replicate)
    apply(cut_tac w = "uint (word_rcat (take 32 (drop (nat ix) l)))" and z = "max_u256 + 1" in Int.nat_mono_iff) apply(simp add:max_u256_def)
          apply(simp add:max_u256_def)

  apply(drule_tac
Q = "uint (word_rcat (take 32 (drop (nat ix) l)))
       < 115792089237316195423570985008687907853269984665640564039457584007913129639936"
and
P = "(nat (uint (word_rcat (take 32 (drop (nat ix) l))))
        < 115792089237316195423570985008687907853269984665640564039457584007913129639936)"
in
HOL.rev_iffD2)
  apply(fastforce)
          apply(clarsimp)
          apply(rotate_tac -1)

          apply(rule_tac Nat.add_less_mono) apply(simp)
          apply(simp)

(* whew *)


(* next up: tuple heads vs tuple tails. *)
  apply(clarsimp)

  apply(clarsimp)

  apply(clarsimp)
(*
  apply(relation 
"measure (\<lambda> x .
    (case x of
       Inl (Inl (t, (ix, l))) \<Rightarrow> abi_type_measure t
      | Inl (Inr (t, n, (ix, l))) \<Rightarrow> nat n * abi_type_measure t
      | Inr (Inl (ts,  n, (ix, l))) \<Rightarrow> abi_type_list_measure ts
      | Inr (Inr (idxs, ts, vs, n, (ix, l))) \<Rightarrow> abi_type_list_measure ts))")   
              apply(clarsimp)
             apply(clarsimp)
            apply(clarsimp)
           apply(clarsimp)
(* first case we get stuck on
decode' vs decode'_dyn_array *)
          apply(clarsimp)
  (* array case: length < 2^256 - 1 *)
  apply(cut_tac w = "(word_rcat (take 32 (drop (nat ix) l)) :: 256 word)" in Word.uint_lt)
    apply(simp add:max_u256_def) apply(cut_tac t = x13 in abi_type_measure_nonzero)
    apply(cut_tac w = "uint (word_rcat (take 32 (drop (nat ix) l)))" and z = "max_u256 + 1" in Int.nat_mono_iff) apply(simp add:max_u256_def)

          apply(rotate_tac -1)
          apply(case_tac "(nat (uint (word_rcat (take 32 (drop (nat ix) l)))) < nat (int (max_u256 + 1)))")
           apply(rotate_tac -1)
           apply(drule_tac k = "abi_type_measure x13" in Nat.mult_less_mono1) apply(simp)
           apply(rotate_tac -1)
  apply(drule_tac m = 1 in Nat.trans_less_add2)
           apply(simp add:max_u256_def)
  apply(arith)
          apply(simp add:max_u256_def)

         apply(clarsimp)
  apply(simp add: abi_type_list_measure_replicate)
         apply(case_tac t, auto)
  apply(case_tac
  apply(arith)
   defer
  sorry
*)
(*  done *)

(*
fun decode :: "abi_type \<Rightarrow> 8 word list \<Rightarrow> abi_value orerror" where
"decode t l =
  (case decode' t l of
    Err s \<Rightarrow> Err s
    | Some (v, _) \<Rightarrow>
    (if abi_value_valid v then Some v else None))"
*)
fun decode :: "abi_type \<Rightarrow> 8 word list \<Rightarrow> abi_value orerror" where
"decode t l =
  (case decode' t l of
    Err s \<Rightarrow> Err s
    | Ok (v, _) \<Rightarrow> Ok v)"
(* head = offset at which tail can be found
   tail = encoding of dynamic object *)

(* functions: TODO *)

(* fun abi_encode ::
    abi_value \<Rightarrow> 8 word list option *)
(* fun abi_decode ::
    8 word list \<Rightarrow> abi_value option *)

(* need an ABI types data type*)
(* do we represent these here as words, or
   as abstract types? *)

(*
datatype AbiValueWord =
  Uint "nat" "256 word"
  | Sint "nat" "256 word"
  | Addr "160 word"
  (* uint, sint : synonyms for uint256/sint256 *)
  | Bl "8 word"
  | Fixed "nat" "nat" "256 word"
  | Ufixed "nat" "nat" "256 word"
  | Bytes "nat" "256 word"
  | Function "160 word" "32 word"
*)

(* encoder *)
(* encode :: abi_value \<Rightarrow> 8 word list *)

end