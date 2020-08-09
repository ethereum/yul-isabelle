theory AbiEncodeSpec imports AbiTypes AbiEncode Hex

begin

(* Inductive specification of ABI encoding.
   This specification captures _all_ encodings, including
   non-canonical ones*)

(* is_head_and_tail predicate captures the structure 
   of dynamic tuples/arrays as they are being encoded

   first parameter is the list of values as "input" (to be encoded)
   second parameter is list of head values
   third parameter is list of types for head values (needed to run the static encoder) *)
inductive is_head_and_tail :: "abi_value list \<Rightarrow> abi_value list \<Rightarrow> abi_type list \<Rightarrow> (int\<times>abi_value) list \<Rightarrow> bool" where
iht_nil :  "is_head_and_tail [] [] [] []"
| iht_static :"\<And> xs ys ts tails x v . 
   is_head_and_tail xs ys ts tails \<Longrightarrow>
   abi_get_type x = v \<Longrightarrow>
   abi_type_isstatic v \<Longrightarrow>
   is_head_and_tail (x#xs) (x#ys) (v#ts) tails"
| iht_dynamic : "\<And> xs ys ts tails x ptr  .
   is_head_and_tail xs ys ts tails \<Longrightarrow>
   abi_type_isdynamic (abi_get_type x) \<Longrightarrow>
   is_head_and_tail (x#xs) ((Vsint 256 ptr) # ys) ((Tsint 256) # ts) ((ptr, x)#tails)"

(*  NB: for static data types, we are using the same encoders as the implementation -
    this is not ideal but it's also not clear if they can be separately specified in a useful way. *)

(* predicate specifying correct encoding
   first parameter is a (decoded) datum
   second parameter is a byte-string corresponding to
     a buffer in which the encoding of the datum can be found
   third parameter is the offset in the buffer at which the encoding begins *)
inductive can_encode_as :: "abi_value \<Rightarrow> 8 word list \<Rightarrow> int \<Rightarrow> bool" 
  where

(* static data use the static encoder *)
Estatic: " \<And> v pre post code . 
  abi_type_isstatic (abi_get_type v) \<Longrightarrow>
  abi_value_valid v \<Longrightarrow>
  encode_static v = Ok code \<Longrightarrow>
  can_encode_as v (pre @ code @ post) (int (length pre))"

(* dynamic cases *)
| Etuple_dyn : "\<And> ts vs t heads head_types tails start full_code . 
      abi_value_valid (Vtuple ts vs) \<Longrightarrow>
      t \<in> set ts \<Longrightarrow>
      (abi_type_isdynamic t) \<Longrightarrow>
      is_head_and_tail vs heads head_types tails \<Longrightarrow>
      can_encode_as (Vtuple head_types heads) full_code start \<Longrightarrow>
      (\<And> offset v . (offset, v) \<in>  set tails \<Longrightarrow> can_encode_as v full_code (offset + start)) \<Longrightarrow>
      can_encode_as (Vtuple ts vs) full_code start"

| Efarray_dyn : "\<And> t n vs heads head_types tails start full_code .
    abi_value_valid (Vfarray t n vs) \<Longrightarrow>
    (abi_type_isdynamic t) \<Longrightarrow>
    is_head_and_tail vs heads head_types tails \<Longrightarrow>
    can_encode_as (Vtuple head_types heads) full_code start \<Longrightarrow>
    (\<And> offset v . (offset, v) \<in>  set tails \<Longrightarrow> can_encode_as v full_code (offset + start)) \<Longrightarrow>
    can_encode_as (Vfarray t n vs) full_code start"

| Earray : "\<And> t vs heads head_types tails start full_code . 
     abi_value_valid (Varray t vs) \<Longrightarrow>
     is_head_and_tail vs heads head_types tails \<Longrightarrow>
     can_encode_as (Vuint 256 (length vs)) full_code start \<Longrightarrow>
     can_encode_as (Vtuple head_types heads) full_code (start + 32) \<Longrightarrow>
     (\<And> offset v . (offset, v) \<in>  set tails \<Longrightarrow> can_encode_as v full_code (offset + start + 32)) \<Longrightarrow>
     can_encode_as (Varray t vs) full_code start"

| Ebytes : "\<And> l pre post count code .
     abi_value_valid (Vbytes l) \<Longrightarrow>
     code = pad_bytes l \<Longrightarrow>
     length count = 32 \<Longrightarrow>
     can_encode_as (Vuint 256 (length l)) (pre @ count @ code @ post) (int (length pre)) \<Longrightarrow>
     can_encode_as (Vbytes l) (pre @ count @ code @ post) (int (length pre))"
| Estring : "\<And> s l start . abi_value_valid (Vstring s) \<Longrightarrow> 
     l = (string_to_bytes s) \<Longrightarrow>
     can_encode_as (Vbytes l) full_code start \<Longrightarrow>
     can_encode_as (Vstring s) full_code start"

 

end