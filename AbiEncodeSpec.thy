theory AbiEncodeSpec imports AbiTypes AbiEncode Hex

begin

(* Inductive specification of ABI encoding. Aim is to capture all encodings including non-canonical ones *)


(* TODO: need to augment this predicate with
    sizes? *)
inductive abi_descend :: "abi_value \<Rightarrow> abi_value \<Rightarrow> bool" where
(* reflexive *)
"\<And> v . abi_descend v v"

(* farray *)
| "\<And> t n vs v .
   v \<in> set vs \<Longrightarrow>
   abi_descend (Vfarray t n vs) v"

(* array *)
| "\<And> t vs v .
   v \<in> set vs \<Longrightarrow>
   abi_descend (Varray t vs) v"

(* tuple *)

| "\<And> ts vs v .
   v \<in> set vs \<Longrightarrow>
   abi_descend (Varray ts vs) v"

(* transitive *)
| "\<And> v v' v'' .
   abi_descend v v' \<Longrightarrow>
   abi_descend v' v'' \<Longrightarrow>
   abi_descend v v''"

(*
inductive is_static_type :: "abi_type \<Rightarrow> bool" where
"\<And> n . is_static_type (Tuint n)"
| "\<And> n . is_static_type (Tsint n)"
| " is_static_type (Taddr)"
| " is_static_type (Tbool)"
| "\<And> m n . is_static_type (Tfixed m n)"
| "\<And> m n . is_static_type (Tufixed m n )"
| "\<And> l . is_static_type (Tfbytes l)"
| "is_static_type (Tfunction)"
| "\<And> t n . is_static_type t \<Longrightarrow>
    is_static_type (Tfarray t n)"
| "\<And> ts .
    (\<forall> t . t \<in> set ts \<longrightarrow> is_static_type t) \<Longrightarrow>
    is_static_type (Ttuple ts)"
*)

(*
inductive typecheck_value :: "abi_value \<Rightarrow> bool" where
" \<And> n i . uint_value_valid n i \<Longrightarrow> typecheck_value (Vuint n i)"
| "\<And> n i . sint_value_valid n i \<Longrightarrow> typecheck_value (Vsint n i)"
| "\<And> a . addr_value_valid a \<Longrightarrow> typecheck_value (Vaddr a)"
| "\<And> b . typecheck_value (Vbool b)"
| "\<And> m n r . fixed_value_valid m n r \<Longrightarrow> typecheck_value (Vfixed m n r)"
| "\<And> m n r . ufixed_value_valid m n r \<Longrightarrow> typecheck_value (Vufixed m n r)"
| "\<And> n l . fbytes_value_valid n l \<Longrightarrow>
   can_encode_as (Vfbytes n l) (encode_fbytes n l)"
*)

(*  TODO: for simple data types, we are using the same encoders as the implementation -
this is not ideal but it's also not clear if they can be separately specified in a useful way. *)

(* integers are encoding's start and end indices *)

inductive can_encode_as :: "abi_value \<Rightarrow> 8 word list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" 
and       can_encode_as_list :: "abi_value list \<Rightarrow> 8 word list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool"
and       can_encode_as_list_dyn :: "abi_value list \<Rightarrow> 8 word list \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
(* static cases *)
Euint: " \<And> n i pre post code . abi_value_valid (Vuint n i) \<Longrightarrow>
  code = (encode_int i) \<Longrightarrow>
  can_encode_as (Vuint n i) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Esint : "\<And> n i pre post code . abi_value_valid (Vsint n i) \<Longrightarrow>
  code = (encode_int i) \<Longrightarrow>
  can_encode_as (Vsint n i) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Eaddr : "\<And> a pre post code . abi_value_valid (Vaddr a) \<Longrightarrow>
  code = (encode_int a) \<Longrightarrow>
  can_encode_as (Vaddr a) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Ebool : "\<And> b pre post code . 
  code = (encode_bool b) \<Longrightarrow>
  can_encode_as (Vbool b) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Efixed : "\<And> m n r pre post code .
  abi_value_valid (Vfixed m n r) \<Longrightarrow>
  code = (encode_fixed n r) \<Longrightarrow>
  can_encode_as (Vfixed m n r) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Eufixed : "\<And> m n r pre post code. abi_value_valid (Vufixed m n r) \<Longrightarrow>
  code = (encode_fixed n r) \<Longrightarrow>
  can_encode_as (Vufixed m n r) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Efbytes : "\<And> n l pre post code . abi_value_valid (Vfbytes n l) \<Longrightarrow>
    code = (encode_fbytes n l) \<Longrightarrow>
   can_encode_as (Vfbytes n l) (pre @ code @ post) (int (length pre)) (int (length (pre @ code)))"
| Efarray_static : "\<And> t n vs pre_len pre_and_code_len full_code .
    abi_value_valid (Vfarray t n vs) \<Longrightarrow>
    abi_type_isstatic t \<Longrightarrow>
    can_encode_as_list vs full_code pre_len pre_and_code_len \<Longrightarrow>
    can_encode_as (Vfarray t n vs) full_code pre_len pre_and_code_len"
| Etuple_static : "\<And> ts vs pre_len pre_and_code_len full_code .
    abi_value_valid (Vtuple ts vs) \<Longrightarrow>
    (\<forall> t . t \<in> set ts \<longrightarrow> abi_type_isstatic t) \<Longrightarrow>
    can_encode_as_list vs full_code pre_len pre_and_code_len \<Longrightarrow>
    can_encode_as (Vtuple ts vs) full_code pre_len pre_and_code_len"

(* helper for static fixed arrays/tuples *)
| Elnil_static :  "\<And> n full_code . can_encode_as_list [] full_code n n"
| Elcons_static : "\<And> v vs pre_len pre_and_v_code_len pre_v_and_vs_code_len full_code .
    can_encode_as v full_code pre_len pre_and_v_code_len \<Longrightarrow>
    can_encode_as_list vs full_code pre_and_v_code_len pre_v_and_vs_code_len \<Longrightarrow>
    can_encode_as_list (v#vs) full_code pre_len pre_v_and_vs_code_len"

(* dynamic cases *)
| Etuple_dyn : "\<And> ts vs t pre_len pre_and_vs_code_len full_code . abi_value_valid (Vtuple ts vs) \<Longrightarrow>
      t \<in> set ts \<Longrightarrow>
      (abi_type_isdynamic t) \<Longrightarrow>
      can_encode_as_list_dyn vs full_code pre_len pre_and_vs_code_len \<Longrightarrow>
      can_encode_as (Vtuple ts vs) full_code pre_len pre_and_vs_code_len"

| Efarray_dyn : "\<And> t n vs pre_len pre_and_vs_code_len full_code .
    abi_value_valid (Vfarray t n vs) \<Longrightarrow>
    (\<not> abi_type_isstatic t) \<Longrightarrow>
    can_encode_as_list_dyn vs full_code pre_len pre_and_vs_code_len \<Longrightarrow>
    can_encode_as (Vfarray t n vs) full_code pre_len pre_and_vs_code_len"

| Earray : "\<And> t vs pre_len pre_and_count_len pre_count_and_vs_code_len full_code . 
     abi_value_valid (Varray t vs) \<Longrightarrow>
     can_encode_as (Vuint 256 (length vs)) full_code pre_len pre_and_count_len \<Longrightarrow>
     can_encode_as_list_dyn vs full_code pre_and_count_len pre_count_and_vs_code_len \<Longrightarrow>
     can_encode_as (Varray t vs) full_code pre_len pre_count_and_vs_code_len"

| Elnil_dyn : "\<And> n full_code . can_encode_as_list_dyn [] full_code n n"
(* NB: the integer parameters here consider the size of the head *)
(* first, the static case *)

| Elcons_dyn_t : "\<And> v vs pre_len pre_and_head_len pre_and_heads_len .
  (abi_type_isstatic (abi_get_type v)) \<Longrightarrow>
  can_encode_as v full_code head_pre_len head_pre_and_head_len \<Longrightarrow>
  can_encode_as_list_dyn vs full_code pre_and_head_len pre_and_heads_len \<Longrightarrow>
  can_encode_as_list_dyn (v #vs) full_code pre_len pre_and_heads_len"

(* now, the case where the value to encode is dynamic  *)
| Elcons_dyn_h : "\<And> v vs offset absolute absolute_and_v_len
                pre_len pre_and_head_len
                pre_and_heads_len .
  (abi_type_isdynamic (abi_get_type v)) \<Longrightarrow>
  can_encode_as (Vsint 256 offset) full_code pre_len pre_and_head_len \<Longrightarrow>
  absolute = offset + pre_len \<Longrightarrow>
  can_encode_as v full_code absolute absolute_and_v_len \<Longrightarrow>
  can_encode_as_list_dyn vs full_code pre_and_head_len pre_and_heads_len \<Longrightarrow>
  can_encode_as_list_dyn (v #vs) full_code pre_len pre_and_heads_len"

| Ebytes : "\<And> l pre post count code .
     abi_value_valid (Vbytes l) \<Longrightarrow>
     code = pad_bytes l \<Longrightarrow>
     can_encode_as (Vuint 256 (length l)) (pre @ count @ code @ post) (int (length pre)) (int (length (pre @ count)))\<Longrightarrow>
     can_encode_as (Vbytes l) (pre @ count @ code @ post) (int (length pre)) (int (length (pre @ count @ code)))"
| Estring : "\<And> s l pre_len pre_and_code_len . abi_value_valid (Vstring s) \<Longrightarrow> 
     l = (string_to_bytes s) \<Longrightarrow>
     can_encode_as (Vbytes l) full_code pre_len pre_and_code_len \<Longrightarrow>
     can_encode_as (Vstring s) full_code pre_len pre_and_code_len "

 

end