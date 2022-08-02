theory BigStep
  imports Main "HOL-Library.Word" "HOL-Library.State_Monad"
begin

type_synonym uint256 = "256 word"

type_synonym Identifier = string
type_synonym Value = uint256


datatype Expression = FunctionCall (FunctionName: Identifier) (Arguments: \<open>Expression list\<close>) |
                      Identifier Identifier |
                      Literal Value

datatype Statement = ExpressionStatement (Expression: Expression) |
                     Assignment (Variables: \<open>Identifier list\<close>) (Value: \<open>Expression option\<close>) | (* Value is mainly  an "option" for consistency with solc's Yul AST. Could also just be plain \<open>Expression\<close> *)
                     VariableDeclaration (Variables: \<open>Identifier list\<close>) (Value: \<open>Expression option\<close>) |
                     FunctionDefinition (Name: Identifier)
                                        (Parameters: \<open>Identifier list\<close>)
                                        (ReturnVariables: \<open>Identifier list\<close>)
                                        (Body: \<open>Statement list\<close>) |
                     If (Condition: Expression) (Body: \<open>Statement list\<close>) |
                     Switch (Expression: Expression) (Cases: \<open>Case list\<close>) |
                     ForLoop (Pre: \<open>Statement list\<close>)
                             (Condition: Expression)
                             (Post: \<open>Statement list\<close>)
                             (Body: \<open>Statement list\<close>) |
                     Break |
                     Continue |
                     Leave |
                     Block (Body: \<open>Statement list\<close>)
    and Case = Case (CaseLiteral: \<open>Value option\<close>) (Body: \<open>Statement list\<close>)
type_synonym Block = \<open>Statement list\<close>

datatype Result = Success | Error (Reason: \<open>string list\<close>) | OutOfGas
datatype Mode = RegularMode | BreakMode | ContinueMode | LeaveMode

type_synonym 'g BuiltinFunction = \<open>Value list \<Rightarrow> ('g, Value list) state\<close>

record 'g yulcontext =
  GlobalState :: 'g
  BuiltinFunctions :: \<open>Identifier \<Rightarrow> ('g BuiltinFunction) option\<close>
  Functions :: \<open>(Identifier\<times> (Statement \<times> Identifier list)) list\<close>
  LocalVariables :: \<open>(Identifier \<times> Value) list\<close>
  Status :: Result

type_synonym ('g, 'a) yulstate = \<open>('g yulcontext, 'a) state\<close>

abbreviation return where \<open>return \<equiv> State_Monad.return\<close>


definition errorState :: \<open>'a \<Rightarrow> string \<Rightarrow> ('g, 'a) yulstate\<close> where
  \<open>errorState defaultValue reason \<equiv> State (\<lambda> s .
        (defaultValue, s\<lparr>Status := Error (reason#(case Status s of Error oldError \<Rightarrow> oldError | _ \<Rightarrow> []))\<rparr>)
      )\<close>

term List.map

definition isDeclared :: \<open>'g yulcontext \<Rightarrow> Identifier \<Rightarrow> bool\<close> where
  \<open>isDeclared context identifier \<equiv> \<not>list_all (\<lambda> (declaredName,_) . declaredName \<noteq> identifier) (LocalVariables context)\<close>
definition getLocalVariable :: \<open>'g yulcontext \<Rightarrow> Identifier \<Rightarrow> Value option\<close> where
  \<open>getLocalVariable context identifier \<equiv> map_option snd (find (\<lambda> (declaredName,_) . declaredName = identifier) (LocalVariables context))\<close>
definition setLocalVariable :: \<open>Identifier \<Rightarrow> Value \<Rightarrow> ('g, unit) yulstate\<close> where
  \<open>setLocalVariable identifier value \<equiv> do {
    context \<leftarrow> State_Monad.get;
    if isDeclared context identifier
    then State_Monad.update (LocalVariables_update (List.map (\<lambda> (declaredName,declaredValue) . 
          (declaredName, if declaredName = identifier then value else declaredValue)
      )))
    else errorState () ''attempt to set undeclared variable''
   }\<close>
definition declareLocalVariable :: \<open>Identifier \<Rightarrow> ('g, unit) yulstate\<close> where
  \<open>declareLocalVariable identifier \<equiv> do {
    context \<leftarrow> State_Monad.get;
    if isDeclared context identifier
    then errorState () ''variable already declared''
    else State_Monad.update (LocalVariables_update (\<lambda> vars . vars @ [(identifier,0)]))
   }\<close>

primrec list_contains :: \<open>'a list \<Rightarrow> 'a \<Rightarrow> bool\<close> where
  \<open>list_contains [] _ = False\<close>
| \<open>list_contains (x#xs) y = (x = y \<or> list_contains xs y)\<close>


definition ValueOfIdentifier :: \<open>Identifier \<Rightarrow> ('g, Value) yulstate\<close> where
  \<open>ValueOfIdentifier identifier \<equiv> do {
      context \<leftarrow> State_Monad.get;
      case getLocalVariable context identifier of
        Some v \<Rightarrow> return v | _ \<Rightarrow> errorState 0 ''unknown identifier''
   }\<close>


definition BuiltinFunctionOfIdentifier :: \<open>Identifier \<Rightarrow> ('g, 'g BuiltinFunction option) yulstate\<close> where
  \<open>BuiltinFunctionOfIdentifier identifier \<equiv> State (\<lambda> state .
      case BuiltinFunctions state identifier of Some f \<Rightarrow> (Some f,state)
      | _ \<Rightarrow> (None, state)
    )\<close>
definition FunctionDefinitionOfIdentifier :: \<open>Identifier \<Rightarrow> ('g, Statement\<times>Identifier list) yulstate\<close> where
  \<open>FunctionDefinitionOfIdentifier identifier \<equiv> State (\<lambda> state .
      case find (\<lambda>(name,_). name = identifier) (Functions state) of Some (_,f) \<Rightarrow> (f, state)
      | _ \<Rightarrow> ((FunctionDefinition identifier [] [] [],[]), state\<lparr>Status := Error (''unknown function''#(
          case Status state of Error oldError \<Rightarrow> oldError | _ \<Rightarrow> []
        ))\<rparr>)
    )\<close>
definition IsTruthy :: \<open>Value \<Rightarrow> bool\<close> where
  \<open>IsTruthy value \<equiv> (value \<noteq> 0)\<close>

(*
(* TODO: already declared error *)
definition DeclareVariable :: \<open>Identifier \<Rightarrow> ('g, unit) yulstate\<close> where
  \<open>DeclareVariable identifier \<equiv> State (\<lambda> state .
      ((), state\<lparr> LocalVariables := (LocalVariables state)(identifier \<mapsto> 0)\<rparr>)
    )\<close>
definition SetVariableValue :: \<open>Identifier \<Rightarrow> Value \<Rightarrow> ('g, unit) yulstate\<close> where
  \<open>SetVariableValue identifier value \<equiv> State (\<lambda> state .
      ((), state\<lparr> LocalVariables := (LocalVariables state)(identifier \<mapsto> value)\<rparr>)
    )\<close>
*)

fun traverse_list_mode :: "('a \<Rightarrow> ('b, Mode) state) \<Rightarrow> 'a list \<Rightarrow> ('b, Mode) state" where
"traverse_list_mode _ [] = return RegularMode" |
"traverse_list_mode f (x # xs) = do {
  x \<leftarrow> f x;
  if x = RegularMode then traverse_list_mode f xs
  else return x
}"

definition TODO :: \<open>string \<Rightarrow> ('a, unit) yulstate\<close> where
  \<open>TODO _ \<equiv> return ()\<close>

function evalStatement :: \<open>nat \<Rightarrow> Mode \<Rightarrow> Statement \<Rightarrow> ('g, Mode) yulstate\<close>
  and evalExpression :: \<open>nat \<Rightarrow> Expression \<Rightarrow> ('g, Value list) yulstate\<close>
  and evalUnaryExpression :: \<open>nat \<Rightarrow> Expression \<Rightarrow> ('g, Value) yulstate\<close> where
  \<open>evalStatement (Suc n) RegularMode (ExpressionStatement expr) = do {
    results \<leftarrow> evalExpression n expr;
    case results of [] \<Rightarrow> return RegularMode |
      _ \<Rightarrow> errorState RegularMode ''expression statement returns values''
   }\<close> |
  \<open>evalStatement (Suc n) RegularMode (Assignment vars None) =
      errorState RegularMode ''assignment without value''\<close> |
  \<open>evalStatement (Suc n) RegularMode (Assignment vars (Some val)) = do {
      values \<leftarrow> evalExpression n val;
      if length values = length vars
      then do {
         context \<leftarrow> State_Monad.get;
         traverse_list (case_prod setLocalVariable) (zip vars values);
         return RegularMode
      }
      else errorState RegularMode ''unbalanced assignment''
   }\<close> |
  \<open>evalStatement (Suc n) RegularMode (VariableDeclaration vars (Some val)) = do {
      evalStatement n RegularMode (VariableDeclaration vars None);
      evalStatement n RegularMode (Assignment vars (Some val));
      return RegularMode
   }\<close> |
  \<open>evalStatement (Suc n) RegularMode (VariableDeclaration vars None) = do {   
         context \<leftarrow> State_Monad.get;
         if \<not>list_all (Not o isDeclared context) vars then
           errorState RegularMode ''redeclaration of variable''
         else do {
           traverse_list declareLocalVariable vars;
           return RegularMode
         }
  }\<close> |
  \<open>evalStatement (Suc n) RegularMode (FunctionDefinition _ _ _ _) = return RegularMode\<close> |
  \<open>evalStatement (Suc n) RegularMode (If condition body) = do {
      value \<leftarrow> evalUnaryExpression n condition;
      if IsTruthy value
      then evalStatement n RegularMode (Block body)
      else return RegularMode
  }\<close> |
  \<open>evalStatement (Suc n) RegularMode (Switch expression cases) = do {
      value \<leftarrow> evalUnaryExpression n expression;
      case (find (\<lambda> c . CaseLiteral c = Some value) cases) of
           (Some c) \<Rightarrow> evalStatement n RegularMode (Block (Body c))
         | None \<Rightarrow> (case (find (\<lambda> c . CaseLiteral c = None) cases) of
                          (Some defaultCase) \<Rightarrow> evalStatement n RegularMode (Block (Body defaultCase))
                         | _ \<Rightarrow> return RegularMode)
  }\<close> |
  \<open>evalStatement (Suc n) RegularMode (ForLoop [] condition post body) = do {
      value \<leftarrow> evalUnaryExpression n condition;
      if IsTruthy value
      then do {
        mode \<leftarrow> evalStatement n RegularMode (Block body);
        case mode of BreakMode \<Rightarrow> return RegularMode
        | LeaveMode \<Rightarrow> return LeaveMode 
        | _ \<Rightarrow> do {
           mode \<leftarrow> evalStatement n RegularMode (Block post);
           if mode = BreakMode \<or> mode = ContinueMode
           then errorState RegularMode ''break or continue in for loop post''
           else evalStatement n mode (ForLoop [] condition post body)
          }
      }
      else return RegularMode
    }\<close> |
  (* TODO: continue and break invalid in pre - although also fine to ignore *)
  \<open>evalStatement (Suc n) RegularMode (ForLoop (pre#pres) condition post body) =
      evalStatement n RegularMode (Block ((pre#pres)@[ForLoop [] condition post body]))\<close> |
  \<open>evalStatement (Suc n) RegularMode Break = return BreakMode\<close> |
  \<open>evalStatement (Suc n) RegularMode Continue = return ContinueMode\<close> |
  \<open>evalStatement (Suc n) RegularMode Leave = return LeaveMode\<close> |
  \<open>evalStatement (Suc n) RegularMode (Block stmts) = 
      (let functionDefinitions = filter is_FunctionDefinition stmts in
       let statements = filter (Not o is_FunctionDefinition) stmts in
       if functionDefinitions = []
       then do {
        oldState \<leftarrow> State_Monad.get;
        mode  \<leftarrow> traverse_list_mode (evalStatement n RegularMode) statements;
        State_Monad.update (\<lambda> state . state\<lparr>
            LocalVariables := filter (\<lambda>(v,_) . isDeclared oldState v) (LocalVariables state)\<rparr>);
        return mode
       }
       else do {
        oldState \<leftarrow> State_Monad.get;
        (let visibleFunctions = (map fst (Functions oldState))@map Name functionDefinitions in
          State_Monad.update (Functions_update (\<lambda> fns . fns@map (\<lambda> def . (Name def, (def, visibleFunctions))) functionDefinitions)));
        evalStatement n RegularMode (Block statements);
        State_Monad.update (Functions_update (\<lambda>_. Functions oldState));
        return RegularMode
      }
      )
  \<close> |
  \<open>evalExpression (Suc n) (Literal lit) = return [lit]\<close> |
  \<open>evalExpression (Suc n) (Identifier identifier) = do {
    x \<leftarrow> ValueOfIdentifier identifier;
    return [x]
  }\<close> |
  \<open>evalExpression (Suc n) (FunctionCall functionName args) = do {
      values \<leftarrow> traverse_list (evalUnaryExpression n) (List.rev args);
      builtinFunction \<leftarrow> BuiltinFunctionOfIdentifier functionName;
      case builtinFunction of
          Some f \<Rightarrow> State (\<lambda> g . case (State_Monad.run_state (f (List.rev values)) (GlobalState g)) of (a,b) \<Rightarrow> (a,g\<lparr>GlobalState := b\<rparr>))
        | None \<Rightarrow> do {
            (functionDefinition,declaredFunctions) \<leftarrow> FunctionDefinitionOfIdentifier functionName;
            case functionDefinition of
              FunctionDefinition name parameters returnValues body \<Rightarrow>
               if length parameters = length args
               then do {
                 oldContext \<leftarrow> State_Monad.get;
                 State_Monad.set (oldContext\<lparr>
                    LocalVariables := (zip parameters (List.rev values))@map (\<lambda> v . (v,0)) returnValues,
                    Functions := filter (\<lambda> (name,_) . list_contains declaredFunctions name) (Functions oldContext)
                 \<rparr>);
                 evalStatement n RegularMode (Block body);
                 values \<leftarrow> traverse_list ValueOfIdentifier returnValues;
                 newContext \<leftarrow> State_Monad.get;
                 State_Monad.set (newContext\<lparr>LocalVariables := LocalVariables oldContext, Functions := Functions oldContext\<rparr>);
                 return values
                }
                else errorState (replicate (length returnValues) 0) ''invalid number of arguments to function call''
            | _ \<Rightarrow>  errorState [] ''expected function definition''
        }
  }\<close> |
  \<open>evalUnaryExpression  (Suc n) expression = do {
    results \<leftarrow> evalExpression n expression;
    case results of [x] \<Rightarrow> return x
        | _ \<Rightarrow> errorState 0 ''expected unary expression''
  }\<close> |
  \<open>evalUnaryExpression 0 _ = errorState 0 ''out of gas''\<close> |
  \<open>evalExpression 0 _ = errorState [] ''out of gas''\<close> |
  \<open>evalStatement 0 RegularMode _ = errorState RegularMode ''out of gas''\<close> |
  \<open>evalStatement _ LeaveMode _ = return LeaveMode\<close> |
  \<open>evalStatement _ ContinueMode _ = return ContinueMode\<close> |
  \<open>evalStatement _ BreakMode _ = return BreakMode\<close>
  by pat_completeness auto

termination by (relation \<open>measure (case_sum fst (case_sum fst fst))\<close>) auto

definition BinaryBuiltinPureFunction :: \<open>(Value \<Rightarrow> Value \<Rightarrow> Value) \<Rightarrow> (Value list \<Rightarrow> ('g, Value list) state)\<close> where
  \<open>BinaryBuiltinPureFunction f args \<equiv>
      case args of [a, b] \<Rightarrow> return [f a b]
                  | _ \<Rightarrow> return []\<close>

definition UnaryBuiltinPureFunction :: \<open>(Value \<Rightarrow> Value) \<Rightarrow> (Value list \<Rightarrow> ('g, Value list) state)\<close> where
  \<open>UnaryBuiltinPureFunction f args \<equiv>
      case args of [a] \<Rightarrow> return [f a]
                  | _ \<Rightarrow> return []\<close>

record EVMState =
  memory :: \<open>uint256 \<Rightarrow> 8 word\<close>
  msize :: uint256
  storage :: \<open>uint256 \<Rightarrow> uint256\<close>
  Log :: \<open>string list\<close>

definition emptyEVMState :: EVMState where
  \<open>emptyEVMState \<equiv> \<lparr> memory = (\<lambda>_. 0), msize = 0, storage = (\<lambda>_. 0), Log = []\<rparr>\<close>

definition BinaryBuiltinEVMFunction ::
  \<open>(Value \<Rightarrow> Value \<Rightarrow> (EVMState, Value list) state) \<Rightarrow> (Value list \<Rightarrow> (EVMState, Value list) state)\<close> where
  \<open>BinaryBuiltinEVMFunction f args \<equiv>
      case args of [a, b] \<Rightarrow> (f a b)
                  | _ \<Rightarrow> return []\<close>

context includes bit_operations_syntax
begin
(* TODO: logging needs to decode 256 bit words into strings and actually append them *)
definition emptyContext :: \<open>EVMState yulcontext\<close> where
  \<open>emptyContext \<equiv> \<lparr>
    GlobalState = emptyEVMState,
    BuiltinFunctions = [
      ''eq'' \<mapsto> BinaryBuiltinPureFunction (\<lambda> a b . if a = b then 1 else 0),
      ''lt'' \<mapsto> BinaryBuiltinPureFunction (\<lambda> a b . if a < b then 1 else 0),
      ''gt'' \<mapsto> BinaryBuiltinPureFunction (\<lambda> a b . if a > b then 1 else 0),
      ''iszero'' \<mapsto> UnaryBuiltinPureFunction (\<lambda> a . if a = 0 then 1 else 0),
      ''add'' \<mapsto> BinaryBuiltinPureFunction (+),
      ''sub'' \<mapsto> BinaryBuiltinPureFunction (-),
      ''mul'' \<mapsto> BinaryBuiltinPureFunction (*),
      ''and'' \<mapsto> BinaryBuiltinPureFunction (AND),
      ''not'' \<mapsto> UnaryBuiltinPureFunction (NOT),
      ''or'' \<mapsto> BinaryBuiltinPureFunction (OR),
      ''div'' \<mapsto> BinaryBuiltinPureFunction (div),
      ''mod'' \<mapsto> BinaryBuiltinPureFunction (mod),
      ''mstore8'' \<mapsto> BinaryBuiltinEVMFunction
          (\<lambda> offset value  . do {
            State_Monad.update (memory_update (\<lambda> mem . mem(offset := ucast value)));
            State_Monad.update (msize_update (\<lambda> size . max size (offset + 1)));
            return []
          }),
      ''log'' \<mapsto> (\<lambda> x . do {
                    State_Monad.update (Log_update (\<lambda> log . log@[]));
                    return []
                 })
    ],
    Functions = [],
    LocalVariables = [],
    Status = Success
  \<rparr>\<close>
end

nonterminal statement
nonterminal statements
nonterminal expression
nonterminal arguments
nonterminal parameters
nonterminal identifier
nonterminal block
nonterminal literal_number
nonterminal functioncall
nonterminal switchcase
nonterminal switchcases

syntax ExpressionStatement :: \<open>functioncall \<Rightarrow> statement\<close> (\<open>_\<close>)
syntax "_YulZero" :: "literal_number" ("0")
syntax "_YulOne" :: "literal_number" ("1")
syntax "_Numeral" :: \<open>num_const \<Rightarrow> literal_number\<close> (\<open>_\<close>)
syntax "_Name" :: \<open>id_position \<Rightarrow> identifier\<close> (\<open>_\<close>)
syntax "_Identifier" :: \<open>identifier \<Rightarrow> expression\<close> (\<open>_\<close>)
syntax "_VarDecl" :: \<open>parameters \<Rightarrow> expression \<Rightarrow> statement\<close> (\<open>let _ := _\<close>)
syntax "_VarDeclNoValue" :: \<open>parameters \<Rightarrow> statement\<close> (\<open>let _\<close>)
syntax "_Assignment" :: \<open>parameters \<Rightarrow> expression \<Rightarrow> statement\<close> (\<open>_ := _\<close>)
abbreviation (input) singleton :: \<open>'a \<Rightarrow> 'a list\<close> where \<open>singleton a \<equiv> [a]\<close>
syntax "singleton" :: \<open>expression \<Rightarrow> arguments\<close> (\<open>_\<close>)
syntax "Cons" :: \<open>expression \<Rightarrow> arguments \<Rightarrow> arguments\<close> (\<open>_,_\<close>)
syntax "_FunctionCall" :: \<open>identifier \<Rightarrow> arguments \<Rightarrow> functioncall\<close> (\<open>_'(_')\<close>)
syntax "" :: \<open>functioncall \<Rightarrow> expression\<close> (\<open>_\<close>)
syntax "singleton" :: \<open>identifier \<Rightarrow> parameters\<close> (\<open>_\<close>)
syntax "Cons" :: \<open>identifier \<Rightarrow> parameters \<Rightarrow> parameters\<close> (\<open>_,_\<close>)

syntax "Nil" :: \<open>statements\<close> (\<open>\<close>)
syntax "Cons" :: \<open>statement \<Rightarrow> statements \<Rightarrow> statements\<close> (\<open>_ _\<close>)

syntax "Block" :: \<open>block \<Rightarrow> Statement\<close> (\<open>YUL _\<close>)

syntax "Block" :: \<open>block \<Rightarrow> statement\<close> (\<open>_\<close>)
syntax "" :: \<open>statements \<Rightarrow> block\<close> (\<open>{_}\<close>)
syntax "_EmptyBlock" :: \<open>block\<close> (\<open>{}\<close>)
syntax "ForLoop" :: \<open>block \<Rightarrow> expression \<Rightarrow> block \<Rightarrow> block \<Rightarrow> statement\<close>
 (\<open>for _ _ _ _\<close>)
syntax "If" :: \<open>expression \<Rightarrow> block \<Rightarrow> statement\<close>
 (\<open>if _ _\<close>)


syntax "_FunctionNoReturn" :: \<open>identifier \<Rightarrow> parameters \<Rightarrow> block \<Rightarrow> statement\<close> (\<open>function _ '(_') _\<close>)
syntax "FunctionDefinition" :: \<open>identifier \<Rightarrow> parameters \<Rightarrow> parameters \<Rightarrow> block \<Rightarrow> statement\<close> (\<open>function _ '(_') -> _ _\<close>)

syntax "Literal" :: \<open>literal_number \<Rightarrow> expression\<close> (\<open>_\<close>)

syntax "Leave" :: \<open>statement\<close> (\<open>leave\<close>)
syntax "Break" :: \<open>statement\<close> (\<open>break\<close>)
syntax "Continue" :: \<open>statement\<close> (\<open>continue\<close>)
syntax Switch :: "expression \<Rightarrow> switchcases \<Rightarrow> statement" ("switch _ _")
syntax "_defaultcase" :: "block \<Rightarrow> switchcase" ("default _")
syntax Cons :: "switchcase \<Rightarrow> switchcases \<Rightarrow> switchcases" ("__")
syntax Nil :: "switchcases" ("")
syntax "_switchcase" :: "literal_number \<Rightarrow> block \<Rightarrow> switchcase" ("case _ _")

translations
  "_YulZero" == "CONST zero_class.zero"
  "_YulOne" == "CONST one_class.one"
  "_Identifier x" == "CONST Identifier x"
  "_VarDecl x v" == "CONST VariableDeclaration x (CONST Some v)"
  "_VarDeclNoValue x" == "CONST VariableDeclaration x (CONST None)"
  "_Assignment x v" == "CONST Assignment x (CONST Some v)"
  "_FunctionCall f args" == "CONST FunctionCall f args"
  "_EmptyBlock" == "CONST Nil"
  "_FunctionNoReturn name params body" == "CONST FunctionDefinition name params (CONST Nil) body"
  "_defaultcase body" == "CONST Case (CONST None) body"
  "_switchcase n body" == "CONST Case (CONST Some n) body"

parse_ast_translation\<open>
[(\<^syntax_const>\<open>_Name\<close>, fn ctxt => fn [Ast.Appl [Ast.Constant "_constrain", Ast.Variable x, Ast.Variable pos]] =>
    (Ast.mk_appl (Ast.Constant "_String") [Ast.mk_appl (Ast.Constant "_constrain") [Ast.Variable ("''"^x^"''"), Ast.Variable pos]]))]
\<close>

syntax "_div" :: identifier ("div")
abbreviation (input) divId :: \<open>string\<close> where \<open>divId \<equiv> ''div''\<close>
translations
  "_div" == "CONST divId"

definition dumpMemory :: \<open>EVMState \<Rightarrow> 8 word list\<close> where
  \<open>dumpMemory state \<equiv> map (\<lambda> offset . memory state (word_of_nat offset)) [0..<unat (msize state)]\<close>

definition dumpContext :: \<open>EVMState yulcontext \<Rightarrow> Result\<times>8 word list\<times>string list\<close> where
  \<open>dumpContext context \<equiv> (Status context, dumpMemory (GlobalState context), Log (GlobalState context))\<close>

definition run where \<open>run gas stmt \<equiv> dumpContext (snd (run_state (evalStatement gas RegularMode stmt)  emptyContext))\<close>

value \<open>run 1000 YUL{
    {
      let x := 2
      let y := 8
      function f(from, to, v) {
          let v2
          for {} lt(from, to) {} {
                v,v2 := g(from,v)
                from := add(from,v)
            }
      }
      f(0,y,x)
      y := mul(div(128, y),2)
      mstore8(1,y)
      function g(a,b) -> v,v2 {
          mstore8(a,b)
          v := b
      }
    }
  }
\<close>

value \<open>run 1000 YUL{
  let x := 0
  function f(x) -> v {
      if iszero(gt(x,4)) {
        mstore8(x,mul(x,2))
        v := f(add(x,1))
        leave
      }
      v := x
  }
  mstore8(10,f(x))
}\<close>

value \<open>run 1000 YUL{
  function f(a, v) {
    mstore8(a, v)
    switch a
    case 2 { mstore8(add(a,1), mul(v,2)) log(a, a) }
    case 4 { mstore8(add(a,1), mul(v,4)) }
  }
  f(0, 1)
  f(2, 1)
  f(4, 1)
  f(7, 1)
}\<close>

end
