theory YulSyntax
  imports Main "HOL-Word.Word"
begin


type_synonym YulIdentifier = String.literal
(* type_synonym YulType = String.literal *)
(* TODO: in the future we may need to change this type. *)
type_synonym 'v YulLiteralValue = 'v
datatype ('v, 't) YulLiteral = YulLiteral 'v 't
datatype 't YulTypedName = YulTypedName String.literal 't
datatype 
  ('v, 't) YulFunctionCall =
  YulFunctionCall (YulFunctionCallName: YulIdentifier) 
                  (YulFunctionCallArguments: "('v, 't) YulExpression list")
and ('v, 't) YulExpression = YulFunctionCallExpression "('v, 't) YulFunctionCall"
     | YulIdentifier YulIdentifier
     | YulLiteralExpression "('v, 't) YulLiteral"

datatype ('v, 't) YulAssignment = YulAssignment "YulIdentifier list" "('v, 't) YulExpression"
datatype ('v, 't) YulVariableDeclaration = YulVariableDeclaration
                                           "'t YulTypedName list" "('v, 't) YulExpression option"

datatype ('v, 't) YulStatement =
  YulFunctionCallStatement "('v, 't) YulFunctionCall" |
  YulAssignmentStatement "('v, 't) YulAssignment" |
  YulVariableDeclarationStatement "('v, 't) YulVariableDeclaration" |
  YulFunctionDefinitionStatement "('v, 't) YulFunctionDefinition" |
  YulIf (YulIfCondition: "('v, 't) YulExpression") (YulIfBody: "('v, 't) YulStatement list") |
  YulSwitch (YulSwitchExpression: "('v, 't) YulExpression") 
            (YulSwitchCases: "('v, 't) YulSwitchCase list") |
  YulForLoop (YulForLoopPre: "('v, 't) YulStatement list") 
             (YulForLoopCondition: "('v, 't) YulExpression") 
             (YulForLoopPost: "('v, 't) YulStatement list") 
             (YulForLoopBody: "('v, 't) YulStatement list")|
  YulBreak |
  YulContinue |
  YulLeave |
  YulBlock (YulBlockStatements: "('v, 't) YulStatement list")
and ('v, 't) YulSwitchCase = YulSwitchCase (YulSwitchCaseValue: "('v, 't) YulLiteral option")
                                           (YulSwitchCaseBody: "('v, 't) YulStatement list")
and ('v, 't) YulFunctionDefinition = YulFunctionDefinition
                                      (YulFunctionDefinitionName: YulIdentifier)
                                      (YulFunctionDefinitionArguments: "'t YulTypedName list")
                                      (YulFunctionDefinitionReturnValues: "'t YulTypedName list")
                                      (YulFunctionDefinitionBody: "('v, 't) YulStatement list")



(*
consts YulAssignment :: "YulIdentifier list \<Rightarrow> YulExpression \<Rightarrow> YulStatement"
consts YulVariableDeclaration :: "YulTypedName list \<Rightarrow> YulExpression option \<Rightarrow> YulStatement"
consts YulFunctionCall :: "YulIdentifier \<Rightarrow> YulExpression list \<Rightarrow> YulExpression"
consts YulExpressionStatement :: "YulExpression \<Rightarrow> YulStatement"
consts YulBlock :: "YulStatement list \<Rightarrow> YulStatement"
consts YulIf :: "YulExpression \<Rightarrow> YulStatement list \<Rightarrow> YulStatement"
consts YulFor :: "YulStatement list \<Rightarrow> YulExpression \<Rightarrow> YulStatement list \<Rightarrow> YulStatement list \<Rightarrow> YulStatement"
consts YulLeave :: "YulStatement"
consts YulBreak :: "YulStatement"
consts YulContinue :: "YulStatement"
consts YulLiteral :: "YulLiteralValue \<Rightarrow> YulType \<Rightarrow> YulLiteral"
consts YulLiteralExpression :: "YulLiteral \<Rightarrow> YulExpression"
consts YulFunctionDefinition :: "YulIdentifier \<Rightarrow> YulTypedName list \<Rightarrow> YulTypedName list \<Rightarrow> YulStatement list \<Rightarrow> YulStatement"
consts YulIdentifier :: "YulIdentifier \<Rightarrow> YulExpression"
consts YulSwitch :: "YulExpression \<Rightarrow> YulSwitchCase list \<Rightarrow> YulStatement"
consts YulCase :: "YulLiteral \<Rightarrow> YulStatement list \<Rightarrow> YulSwitchCase" *)
consts YulDefaultCase :: "('v, 't) YulStatement list \<Rightarrow> ('v, 't) YulSwitchCase"
(* consts YulTypedName :: "YulIdentifier \<Rightarrow> YulType \<Rightarrow> YulTypedName" *)
abbreviation (input) YulZero where "YulZero \<equiv> 0"
abbreviation (input) YulOne where "YulOne \<equiv> 1"
consts YulLiteralNumber :: "256 word \<Rightarrow> 'v YulLiteralValue"
consts YulUserDefinedType :: "String.literal \<Rightarrow> 't"
consts YulTypeUint256 :: 't
consts YulTypeBool :: 't
consts YulDefaultType :: 't
consts YulStringLiteral :: "String.literal \<Rightarrow> 'v YulLiteralValue"
consts YulBoolTrueLiteral :: "'v YulLiteralValue"
consts YulBoolFalseLiteral :: "'v YulLiteralValue"


nonterminal yul_typed_literal
nonterminal yul_literal
nonterminal yul_literal_number
nonterminal yul_typed_identifier
nonterminal yul_typed_identifiers
nonterminal yul_function_declaration_argument_list
nonterminal yul_function_declaration_return_value_list
nonterminal yul_name
nonterminal yul_identifier
nonterminal yul_identifiers
nonterminal yul_statement
nonterminal yul_statements
nonterminal yul_block
nonterminal yul_function_call
nonterminal yul_expression
nonterminal yul_function_call_argument_list
nonterminal yul_expressions
nonterminal yul_switch_case
nonterminal yul_switch_cases
nonterminal yul_type
nonterminal yul_id_part
nonterminal yul_id
nonterminal yul_assignment
nonterminal yul_variable_declaration
nonterminal yul_function_definition

abbreviation (input) YulNegativeLiteralNumber where "YulNegativeLiteralNumber \<equiv> (\<lambda> x . YulLiteralNumber (-x))"

syntax YulBlock :: "yul_statements \<Rightarrow> ('v, 't) YulStatement" ("YUL{_}")
syntax "" :: "yul_statement \<Rightarrow> any" ("YUL'_STMT'{_'}")
syntax "" :: "yul_expression \<Rightarrow> any" ("YUL'_EXPR'{_'}")


abbreviation (input) Singleton where "Singleton \<equiv> \<lambda> x . x#[]"
syntax "" :: "yul_id \<Rightarrow> yul_identifier" ("_")
syntax "" :: "yul_id \<Rightarrow> yul_identifier" ("_")
syntax "" :: "yul_id \<Rightarrow> yul_name" ("_")
syntax "_YulUntypedIdentifier" :: "yul_identifier \<Rightarrow> yul_typed_identifier" ("_")
syntax YulTypedName :: "yul_name \<Rightarrow> yul_type \<Rightarrow> yul_typed_identifier" ("_:_")
syntax Nil :: "yul_statements" ("")
syntax Cons :: "yul_statement \<Rightarrow> yul_statements \<Rightarrow> yul_statements" ("_ _")
syntax YulIdentifier :: "yul_identifier \<Rightarrow> yul_expression" ("_")
syntax Singleton :: "yul_identifier \<Rightarrow> yul_identifiers" ("_")
syntax Cons :: "yul_identifier \<Rightarrow> yul_identifiers \<Rightarrow> yul_identifiers" ("_,_")
syntax Singleton :: "yul_typed_identifier \<Rightarrow> yul_typed_identifiers" ("_")
syntax Cons :: "yul_typed_identifier \<Rightarrow> yul_typed_identifiers \<Rightarrow> yul_typed_identifiers" ("_,_")
syntax YulAssignment :: "yul_identifiers \<Rightarrow> yul_expression \<Rightarrow> yul_assignment" ("_ := _")
syntax YulAssignmentStatement :: "yul_assignment \<Rightarrow> yul_statement" ("_")
syntax "_YulVariableDeclarationWithoutValue" :: "yul_typed_identifiers \<Rightarrow> yul_variable_declaration" ("let _")
syntax "_YulVariableDeclarationWithValue" :: "yul_typed_identifiers \<Rightarrow> yul_expression \<Rightarrow> yul_variable_declaration" ("let _ := _")
syntax "YulVariableDeclarationStatement" :: "yul_variable_declaration \<Rightarrow> yul_statement" ("_")
syntax "" :: "yul_expressions \<Rightarrow> yul_function_call_argument_list" ("'(_')")
syntax Nil :: "yul_function_call_argument_list" ("'(')")
syntax YulFunctionCall :: "yul_name \<Rightarrow> yul_function_call_argument_list \<Rightarrow> yul_function_call" ("__")
syntax YulFunctionCallExpression :: "yul_function_call \<Rightarrow> yul_expression" ("_")
syntax YulFunctionCallStatement :: "yul_function_call \<Rightarrow> yul_statement" ("_")
syntax Cons :: "yul_expression \<Rightarrow> yul_expressions \<Rightarrow> yul_expressions" ("(1_,/ _)")
syntax Singleton :: "yul_expression \<Rightarrow> yul_expressions" ("_")
syntax "" :: "yul_statements \<Rightarrow> yul_block" ("'{_'}")
syntax YulBlock :: "yul_block \<Rightarrow> yul_statement" ("_")
syntax YulIf :: "yul_expression \<Rightarrow> yul_block \<Rightarrow> yul_statement" ("if _ _")
syntax YulForLoop :: "yul_block \<Rightarrow> yul_expression \<Rightarrow> yul_block \<Rightarrow> yul_block \<Rightarrow> yul_statement" ("for _ _ _ _")
syntax YulBreak :: "yul_statement" ("break")
syntax YulContinue :: "yul_statement" ("continue")
syntax YulLeave :: "yul_statement" ("leave")
syntax YulSwitch :: "yul_expression \<Rightarrow> yul_switch_cases \<Rightarrow> yul_statement" ("switch _ _")
abbreviation (input) YulNonDefaultCase where "YulNonDefaultCase \<equiv> \<lambda> x y . YulSwitchCase (Some x) y"
syntax YulNonDefaultCase :: "yul_typed_literal \<Rightarrow> yul_block \<Rightarrow> yul_switch_case" ("case _ _")
abbreviation (input) YulDefaultCaseList where "YulDefaultCaseList \<equiv> \<lambda> x . [YulSwitchCase None x]"
syntax YulDefaultCaseList :: "yul_block \<Rightarrow> yul_switch_cases" ("default _")
syntax Cons :: "yul_switch_case \<Rightarrow> yul_switch_cases \<Rightarrow> yul_switch_cases" ("__")
syntax Nil :: "yul_switch_cases" ("")
syntax "" :: "yul_typed_identifiers \<Rightarrow> yul_function_declaration_argument_list" ("'(_')")
syntax Nil :: "yul_function_declaration_argument_list" ("'(')")
syntax Nil :: "yul_function_declaration_return_value_list" ("")
syntax "" :: "yul_typed_identifiers \<Rightarrow> yul_function_declaration_return_value_list" ("-> _")
syntax YulFunctionDefinition :: "yul_name \<Rightarrow> yul_function_declaration_argument_list \<Rightarrow> yul_function_declaration_return_value_list \<Rightarrow> yul_block \<Rightarrow> yul_function_definition" ("function ____")
syntax YulFunctionDefinitionStatement :: "yul_function_definition \<Rightarrow> yul_statement" ("_")
syntax "_YulEmptyBlock" :: "yul_block" ("'{'}")

syntax "_Numeral" :: "num_const \<Rightarrow> yul_literal_number" ("_")
syntax YulZero :: "yul_literal_number" ("0")
syntax YulOne :: "yul_literal_number" ("1")
syntax YulLiteralNumber :: "yul_literal_number \<Rightarrow> yul_literal" ("_")
syntax YulNegativeLiteralNumber :: "yul_literal_number \<Rightarrow> yul_literal" ("-_")
syntax "_YulUntypedLiteral" :: "yul_literal \<Rightarrow> yul_typed_literal" ("_")
syntax YulLiteral :: "yul_literal \<Rightarrow> yul_type \<Rightarrow> yul_typed_literal" ("_:_")
syntax YulLiteralExpression :: "yul_typed_literal \<Rightarrow> yul_expression" ("_")
syntax YulBoolTrueLiteral :: "yul_literal" ("true")
syntax YulBoolFalseLiteral :: "yul_literal" ("false")

nonterminal yul_type_name
syntax "_YulIdentifierLiteral" :: "id \<Rightarrow> yul_type_name" ("_")
syntax "YulUserDefinedType" :: "yul_type_name \<Rightarrow> yul_type" ("_")
syntax YulTypeUint256 :: "yul_type" ("uint256")
(* this line causes problems due to overlap with Isabelle builtin bool *)
syntax YulTypeBool :: "yul_type" ("bool")
(* this is a partial fix *)
type_notation bool ("bool")
nonterminal yul_string_YulLiteral
syntax "_Literal" :: "str_position \<Rightarrow> yul_string_YulLiteral" ("_")
syntax YulStringLiteral :: "yul_string_YulLiteral \<Rightarrow> yul_literal" ("_")

syntax "" :: "any \<Rightarrow> yul_statement" ("\<guillemotleft>_\<guillemotright>")
syntax "" :: "any \<Rightarrow> yul_name" ("\<guillemotleft>_\<guillemotright>")
syntax "" :: "any \<Rightarrow> yul_identifiers" ("\<guillemotleft>_\<guillemotright>")
syntax "" :: "any \<Rightarrow> yul_expression" ("\<guillemotleft>_\<guillemotright>")
syntax "" :: "any \<Rightarrow> yul_function_call_argument_list" ("'(\<guillemotleft>_\<guillemotright>')")

term Pair

translations
  "_YulUntypedLiteral x" => "CONST YulLiteral x (CONST YulDefaultType)"
  "_YulUntypedIdentifier x" => "CONST YulTypedName x (CONST YulDefaultType)"
  "_YulVariableDeclarationWithoutValue x" => "CONST YulVariableDeclaration x (CONST None)"
  "_YulVariableDeclarationWithValue x y" => "CONST YulVariableDeclaration x (CONST Some y)"
  "_YulEmptyBlock" => "CONST Nil"
(*
parse_ast_translation\<open>
[("_YulIdentifierLiteral", K (fn [Ast.Variable name] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''"^name^"''")]))]
\<close>
*)

syntax "_YulIdentifierLiteral" :: "id \<Rightarrow> yul_id_part" ("_")
syntax "" :: "yul_id_part \<Rightarrow> yul_id" ("_")
syntax "_YulIdPartMerge" :: "yul_id_part \<Rightarrow> yul_id \<Rightarrow> yul_id" ("__")
syntax "_YulNamePartDollarSign" :: "yul_id_part" ("$")
syntax "_YulNamePartUnderscore" :: "yul_id_part" ("'_")
syntax "_YulNamePartDot" :: "yul_id_part" (".")
syntax "_YulNamePartUnderscores" :: "yul_id_part" ("'_'_")
(*syntax "_YulIdentifierNumConst" :: "num_const \<Rightarrow> yul_id_part" ("_")*)
                
parse_ast_translation\<open>
[
("_YulIdentifierLiteral", K (fn [Ast.Variable name] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''"^name^"''")])),
("_YulIdentifierNumConst", K (fn [Ast.Appl [Ast.Constant "_constrain", Ast.Constant name, _]] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''"^name^"''")])),
("_YulNamePartDollarSign", K (fn [] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''$''")])),
("_YulNamePartDot", K (fn [] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''.''")])),
("_YulNamePartUnderscore", K (fn [] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''_''")])),
("_YulNamePartUnderscores", K (fn [] => Ast.Appl [Ast.Constant "_Literal", Ast.Variable ("''__''")])),
("_YulIdPartMerge", K (fn [Ast.Appl [Ast.Constant "_Literal", Ast.Variable name1], Ast.Appl [Ast.Constant "_Literal", Ast.Variable name2]] =>
  Ast.Appl [Ast.Constant "_Literal", Ast.Variable (String.extract (name1, 0, SOME (String.size name1 - 2))^String.extract (name2, 2, NONE))]
 | s => (@{print} s; Ast.Appl [Ast.Constant "_Literal", Ast.Variable "''test''"]))
)
]
\<close>

term \<open>YUL{
 let x,y:uint256 := f(\<guillemotleft>[z,z,z,z]\<guillemotright>)
 z := f( \<guillemotleft>xy\<guillemotright>, \<guillemotleft>YulIdentifier (STR ''a'')\<guillemotright>, \<guillemotleft>z\<guillemotright> )
 b := d
 c := ''x''
 switch x
 case 1:uint256 {}
 case 0xffff { x := y }
 default { x := -1 }
 { x := y }
}\<close>

term \<open>YUL{
 function \<guillemotleft>g\<guillemotright>(_a$3$_.b, b:uint256, c, d) { mstore(a,b) leave }
 function f(a, b, c, d) -> x,y { \<guillemotleft>[if complexInnerSyntaxCondition then STR ''x'' else STR ''y'']\<guillemotright> := a }
 function h() { \<guillemotleft>g\<guillemotright>() }
 let x,y:uint256 := f(\<guillemotleft>[z,z,z,z]\<guillemotright>)
 z := f( \<guillemotleft>xy\<guillemotright>, \<guillemotleft>YulIdentifier (STR ''a'')\<guillemotright>, \<guillemotleft>z\<guillemotright> )
 b := d
 c := ''x''
 switch x
 case 1:uint256 {}
 case 0xffff { x := y }
 default { x := -1 }
 { x := y }
 if x { x := y }
 for { let i:someType := 0 } lt(i, 4:uint256) { i := add(i,1) } {
  if x { y := z }
  if y { break continue break }
 }
}\<close>

term \<open>YUL{
{
	for {} true:bool { let x := 1 } { let x := 1 }
}
}\<close>

term "YUL_EXPR{ f(a,1) }"
term "YUL_STMT{ f(a,1) }"
term "YUL_STMT{ \<guillemotleft>f\<guillemotright>(\<guillemotleft>args\<guillemotright>) }"

end