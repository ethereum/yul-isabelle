theory MiniEvm
  imports YulSemanticsCommon
    "HOL-Library.Adhoc_Overloading"
    "HOL-Word.Word"
begin

(* EVM is unityped; everything is 256-bit word *)
type_synonym eint = "256 word"

consts keccak256 :: "eint \<Rightarrow> eint"

record estate =
  memory :: "eint \<Rightarrow> eint"
  storage :: "eint \<Rightarrow> eint"
  flag :: YulFlag
  calldata :: "eint list"

(* *)
consts mkBuiltin ::
  "'x \<Rightarrow> ('v list \<Rightarrow> (('g, 'v list) State) Result)"

(* 1st number = number of arguments
   2nd number = number of returns *)

definition mkBuiltin_0_0 ::
"('g, unit) State \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_0_0 f vs =
  (case vs of
    [] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f g of
                ((), g') \<Rightarrow> ([], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_1_0 ::
"('v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_1_0 f vs =
  (case vs of
    [v] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v g of
                ((), g') \<Rightarrow> ([], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_1_1 ::
"('v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_1_1 f vs =
  (case vs of
    [v] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v g of
                (v', g') \<Rightarrow> ([v'], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_2_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_2_0 f vs =
  (case vs of
    [v1, v2] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 g of
                ((), g') \<Rightarrow> ([], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_2_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_2_1 f vs =
  (case vs of
    [v1, v2] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 g of
                (v', g') \<Rightarrow> ([v'], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_2_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_2_2 f vs =
  (case vs of
    [v1, v2] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 g of
                ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"


definition mkBuiltin_3_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_3_0 f vs =
  (case vs of
    [v1, v2, v3] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 v3 g of
                ((), g') \<Rightarrow> ([], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_3_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_3_1 f vs =
  (case vs of
    [v1, v2, v3] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 v3 g of
                (v', g') \<Rightarrow> ([v'], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

definition mkBuiltin_3_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('v list \<Rightarrow> (('g, 'v list) State) Result)" where
"mkBuiltin_3_2 f vs =
  (case vs of
    [v1, v2, v3] \<Rightarrow> Result 
            (\<lambda> g . 
              (case f v1 v2 v3 g of
                ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
    | _ \<Rightarrow> Error (STR ''Argument arity error'') None)"

adhoc_overloading mkBuiltin
  mkBuiltin_0_0
  mkBuiltin_1_0
  mkBuiltin_1_1
  mkBuiltin_2_0
  mkBuiltin_2_1
  mkBuiltin_2_2
  mkBuiltin_3_0
  mkBuiltin_3_1
  mkBuiltin_3_2

end
