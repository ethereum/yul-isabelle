(* 
 * Utilities for constructing Yul dialects
 * (esp. builtins)
 *)

theory YulDialect
  imports
    YulSemanticsCommon
    "HOL-Library.Adhoc_Overloading"
begin

consts mkBuiltin ::
  "'x \<Rightarrow> ('g, 'v, 't) function_sig"

(* 1st number = number of arguments
   2nd number = number of returns *)

fun mkNames :: "String.literal list \<Rightarrow> (unit YulTypedName list)"
  where
"mkNames [] = []"
| "mkNames (s1 # st) =
  YulTypedName s1 YulDefaultType # mkNames st"

(* TODO: have a version of these thast lifts from
  ('g, unit) State Result
  (useful for handling builtins that can fail)
*)
definition mkBuiltin_0_0 ::
"('g, unit) State \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_0_0 f =
  \<lparr> f_sig_arguments = mkNames []
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . case vs of
      [] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_0_1 ::
"('g, 'v) State \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_0_1 f =
  \<lparr> f_sig_arguments = mkNames []
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . case vs of
      [] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f g of
                  (v, g') \<Rightarrow> ([v], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_1_0 ::
"('v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_1_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'']
    , f_sig_returns = mkNames []
    , f_sig_body = YulBuiltin
      (\<lambda> vs . case vs of
        [v] \<Rightarrow> Result 
                (\<lambda> g . 
                  (case f v g of
                    ((), g') \<Rightarrow> ([], g')))
        | _ \<Rightarrow> Error (STR ''Argument arity error'') None)
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_1_1 ::
"('v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_1_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_2_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_2_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_2_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_2_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_2_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_2_2 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'']
  , f_sig_returns = mkNames [STR ''r1'', STR ''r2'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 g of
                  ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None)) 
  , f_sig_visible = [] \<rparr>"


definition mkBuiltin_3_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_3_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_3_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_3_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_3_2 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, ('v * 'v)) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_3_2 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'']
  , f_sig_returns = mkNames [STR ''r1'', STR ''r2'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 g of
                  ((v'1, v'2), g') \<Rightarrow> ([v'1, v'2], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>" 

definition mkBuiltin_4_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_4_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'', STR ''a4'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_4_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_4_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'', STR ''a4'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_5_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_5_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'', STR ''a4'', STR ''a5'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4, v5] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 v5 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_6_0 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, unit) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_6_0 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'',
                               STR ''a4'', STR ''a5'', STR ''a6'']
  , f_sig_returns = mkNames []
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4, v5, v6] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 v5 v6 g of
                  ((), g') \<Rightarrow> ([], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_6_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_6_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'',
                               STR ''a4'', STR ''a5'', STR ''a6'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4, v5, v6] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 v5 v6 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"

definition mkBuiltin_7_1 ::
"('v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> ('g, 'v) State) \<Rightarrow>
 ('g, 'v, unit) function_sig" where
"mkBuiltin_7_1 f =
  \<lparr> f_sig_arguments = mkNames [STR ''a1'', STR ''a2'', STR ''a3'',
                               STR ''a4'', STR ''a5'', STR ''a6'', STR ''a7'']
  , f_sig_returns = mkNames [STR ''r1'']
  , f_sig_body = YulBuiltin
    (\<lambda> vs . (case vs of
      [v1, v2, v3, v4, v5, v6, v7] \<Rightarrow> Result 
              (\<lambda> g . 
                (case f v1 v2 v3 v4 v5 v6 v7 g of
                  (v', g') \<Rightarrow> ([v'], g')))
      | _ \<Rightarrow> Error (STR ''Argument arity error'') None))
  , f_sig_visible = [] \<rparr>"



adhoc_overloading mkBuiltin
  mkBuiltin_0_0
  mkBuiltin_0_1

  mkBuiltin_1_0
  mkBuiltin_1_1

  mkBuiltin_2_0
  mkBuiltin_2_1
  mkBuiltin_2_2

  mkBuiltin_3_0
  mkBuiltin_3_1
  mkBuiltin_3_2

  mkBuiltin_4_0
  mkBuiltin_4_1

  mkBuiltin_5_0

  mkBuiltin_6_0
  mkBuiltin_6_1

  mkBuiltin_7_1


end