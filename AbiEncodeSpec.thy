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


(* should be isstatic *)
(*
primrec has_value_type :: "abi_value \<Rightarrow> bool" where
  "has_value_type (Vuint x y) = True"
| "has_value_type (Vsint x y) = True"
| "has_value_type (Vaddr x) = True"
| "has_value_type (Vbool x) = True"
| "has_value_type (Vfixed x y z) = True"
| "has_value_type (Vufixed x y z) = True"
| "has_value_type (Vfbytes x y) = True"
| "has_value_type (Vfunction x y) = True"
| "has_value_type (Vfarray x y z) = False"
| "has_value_type (Vtuple x y) = False"
| "has_value_type (Vbytes x) = False"
| "has_value_type (Vstring x) = False"
| "has_value_type (Varray x y) = False"
*)

(*
inductive is_head_and_tail :: "abi_value list \<Rightarrow> abi_value list \<Rightarrow> (int\<times>abi_value) set \<Rightarrow> bool" where
  "is_head_and_tail [][]{}"
| "\<And> xs ys x tails . 
   is_head_and_tail xs ys tails \<Longrightarrow>
   abi_type_isstatic (abi_get_type x) \<Longrightarrow>
   is_head_and_tail (x#xs) (x#ys) tails"
| "\<And> xs ys x tails .
   is_head_and_tail xs ys tails \<Longrightarrow>
   abi_type_isdynamic (abi_get_type x) \<Longrightarrow>
   is_head_and_tail (x#xs) (Vuint 256 ptr#ys) (insert (ptr,x) tails)"
*)

(* first parameter is the list of values as "input" (to be encoded)
   second parameter is list of head values
   third parameter is list of types for head values so we can run the static encoder *)
inductive is_head_and_tail :: "abi_value list \<Rightarrow> abi_value list \<Rightarrow> abi_type list \<Rightarrow> (int\<times>abi_value) set \<Rightarrow> bool" where
iht_nil :  "is_head_and_tail [] [] [] {}"
| iht_static :"\<And> xs ys ts tails x v . 
   is_head_and_tail xs ys ts tails \<Longrightarrow>
   abi_get_type x = v \<Longrightarrow>
   abi_type_isstatic v \<Longrightarrow>
   is_head_and_tail (x#xs) (x#ys) (v#ts) tails"
| iht_dynamic : "\<And> xs ys ts tails x  .
   is_head_and_tail xs ys ts tails \<Longrightarrow>
   abi_type_isdynamic (abi_get_type x) \<Longrightarrow>
   is_head_and_tail (x#xs) ((Vuint 256 ptr) # ys) ((Tuint 256) # ts) (insert (ptr,x) tails)"

(*

data (1, 2, 3, 4)

\<Rightarrow>

{(1, X); (2, Y); (3, Z); (4, W)}

*)

(*  TODO: for simple data types, we are using the same encoders as the implementation -
this is not ideal but it's also not clear if they can be separately specified in a useful way. *)

(* integers are encoding's start and end indices *)

inductive can_encode_as :: "abi_value \<Rightarrow> 8 word list \<Rightarrow> int \<Rightarrow> bool" 
  where
(* static cases *)

Estatic: " \<And> v pre post code . 
  abi_type_isstatic (abi_get_type v) \<Longrightarrow>
  abi_value_valid v \<Longrightarrow>
  encode_static v = Ok code \<Longrightarrow>
  can_encode_as v (pre @ code @ post) (int (length pre))"

(* dynamic cases *)
(* need an abi type list to be able to talk about encoding of heads without a separate predicate *)
| Etuple_dyn : "\<And> ts vs t heads head_types tails start full_code . 
      abi_value_valid (Vtuple ts vs) \<Longrightarrow>
      t \<in> set ts \<Longrightarrow>
      (abi_type_isdynamic t) \<Longrightarrow>
      is_head_and_tail vs heads head_types tails \<Longrightarrow>
      can_encode_as (Vtuple head_types heads) full_code start \<Longrightarrow>
      (\<And> offset v . (offset, v) \<in>  tails \<Longrightarrow> can_encode_as v full_code offset) \<Longrightarrow>
      can_encode_as (Vtuple ts vs) full_code start"

| Efarray_dyn : "\<And> t n vs heads head_types tails start full_code .
    abi_value_valid (Vfarray t n vs) \<Longrightarrow>
    (abi_type_isdynamic t) \<Longrightarrow>
    is_head_and_tail vs heads head_types tails \<Longrightarrow>
    can_encode_as (Vtuple head_types heads) full_code start \<Longrightarrow>
    (\<And> offset v . (offset, v) \<in>  tails \<Longrightarrow> can_encode_as v full_code offset) \<Longrightarrow>
    can_encode_as (Vfarray t n vs) full_code start"

| Earray : "\<And> t vs heads head_types tails start full_code . 
     abi_value_valid (Varray t vs) \<Longrightarrow>
     is_head_and_tail vs heads head_types tails \<Longrightarrow>
     can_encode_as (Vuint 256 (length vs)) full_code start \<Longrightarrow>
     can_encode_as (Vtuple head_types heads) full_code (start + 32) \<Longrightarrow>
     (\<And> offset v . (offset, v) \<in>  tails \<Longrightarrow> can_encode_as v full_code offset) \<Longrightarrow>
     can_encode_as (Varray t vs) full_code start"

| Ebytes : "\<And> l pre post count code .
     abi_value_valid (Vbytes l) \<Longrightarrow>
     code = pad_bytes l \<Longrightarrow>
     can_encode_as (Vuint 256 (length l)) (pre @ count @ code @ post) (int (length pre)) \<Longrightarrow>
     can_encode_as (Vbytes l) (pre @ count @ code @ post) (int (length pre) + 32)"
| Estring : "\<And> s l start . abi_value_valid (Vstring s) \<Longrightarrow> 
     l = (string_to_bytes s) \<Longrightarrow>
     can_encode_as (Vbytes l) full_code start \<Longrightarrow>
     can_encode_as (Vstring s) full_code start"

 

end