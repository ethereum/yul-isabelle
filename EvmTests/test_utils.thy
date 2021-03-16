theory test_utils
imports Main "../Utils/Hex" "../EVM/MiniEvm"
begin

(* read in data blocks from hex *)

(* read in code from hex *)


fun check_expect_storage :: "((eint * eint) list) \<Rightarrow> estate \<Rightarrow> bool" where
"check_expect_storage [] st = True"
| "check_expect_storage ((idx,val)#t) st =
   ((e_storage st idx = val) \<and>
    check_expect_storage t st)"

fun create_storage :: "((eint * eint) list) \<Rightarrow> eint \<Rightarrow> eint" where
"create_storage [] = (\<lambda> _ . 0)"
| "create_storage ((k,v)#t) =
  (\<lambda> k' . (if k = k' then v else create_storage t k'))"

end