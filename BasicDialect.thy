theory BasicDialect
imports
  YulDialect "HOL-Word.Word"
begin

(* see if type_synonym vs record helps *)
record basic_state =
  b_flag :: YulFlag
  b_trace :: "256 word list"
(*  b_mem :: int list
*)

definition basic_add :: 
  "256 word \<Rightarrow> 256 word \<Rightarrow> (basic_state, 256 word) State" where
"basic_add i1 i2 s =
  (plus_word_inst.plus_word i1 i2, s)"

definition basic_sub ::
  "256 word \<Rightarrow> 256 word \<Rightarrow>  (basic_state, 256 word) State" where
"basic_sub i1 i2 s =
  (i1 - i2, s)"

definition basic_mul ::
  "256 word \<Rightarrow> 256 word \<Rightarrow>  (basic_state, 256 word) State" where
"basic_mul i1 i2 s =
  (i1 * i2, s)"

definition basic_div ::
  "256 word \<Rightarrow> 256 word \<Rightarrow>  (basic_state, 256 word) State" where
"basic_div i1 i2 s =  
  (divide_word_inst.divide_word i1 i2, s)"

definition basic_lt ::
  "256 word \<Rightarrow> 256 word \<Rightarrow>  (basic_state, 256 word) State" where
"basic_lt i1 i2 s =
  (if i1 < i2 then 1 else 0, s)"

definition basic_gt ::
  "256 word \<Rightarrow> 256 word \<Rightarrow>  (basic_state, 256 word) State" where
"basic_gt i1 i2 s =
  (if i1 > i2 then 1 else 0, s)"

definition basic_eq ::
  "256 word \<Rightarrow> 256 word \<Rightarrow> (basic_state, 256 word) State" where
"basic_eq i1 i2 s = 
  (if i1 = i2 then 1 else 0, s)"

definition basic_print ::
  "256 word \<Rightarrow> (basic_state, unit) State" where
"basic_print i1 s =
  ((), (s \<lparr> b_trace := i1#b_trace s \<rparr>))"

definition basicBuiltins :: 
  "(basic_state, 256 word, unit) function_sig locals" where
"basicBuiltins = make_locals
  [ ( (STR ''add'')
    , mkBuiltin basic_add)
  , ( (STR ''sub'')
    , mkBuiltin basic_sub)
  , ( (STR ''mul'')
    , mkBuiltin basic_mul)
  , ( (STR ''div'')
    , mkBuiltin basic_div)
  , ( (STR ''lt'')
    , mkBuiltin basic_lt)
  , ( (STR ''gt'')
    , mkBuiltin basic_gt)
  , ( (STR ''eq'')
    , mkBuiltin basic_eq)
  , ( (STR ''print'')
    , mkBuiltin basic_print)]"
    
definition basicDialect ::
  "(basic_state, 256 word, unit) YulDialect" where
  "basicDialect =
    \<lparr> is_truthy = (\<lambda> i . i \<noteq> 0)
    , init_state = (\<lparr> b_flag = Executing, b_trace = []\<rparr>)
    , default_val = 0
    , builtins = basicBuiltins
    , set_flag = 
      (\<lambda> f x . (x \<lparr> b_flag := f \<rparr>))
    , get_flag =
      (\<lambda> x . b_flag x)\<rparr>"

end