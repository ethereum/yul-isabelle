theory YulSemanticsCommon imports YulSyntax     "HOL-Library.Word"

begin

(* Primitives common to both small and big step Yul semantics *)
datatype mode =
  Regular
  | Break
  | Continue
  | Leave

(* result type for builtins *)
datatype 'a Result = Result 'a | Error "String.literal" "'a option"

(* state monad for builtins *)
type_synonym ('g, 'r) State =
"'g \<Rightarrow> ('r * 'g)"

(* TODO: allow direct access to locals? *)
datatype ('g, 'v, 't) YulFunctionBody =
  YulBuiltin "'v list \<Rightarrow> (('g, 'v list) State) Result"
  | YulFunction "('v, 't) YulStatement list"

(* function signature data *)
record ('g, 'v, 't) function_sig' =
  f_sig_arguments ::"'t YulTypedName list"
  f_sig_returns :: "'t YulTypedName list"
  f_sig_body :: "('g, 'v, 't) YulFunctionBody"

(* function signature data + list of visible functions at that function's definition
   site *)
record ('g, 'v, 't) function_sig = "('g, 'v, 't) function_sig'" +
  f_sig_visible :: "YulIdentifier list"

type_synonym 'v locals = "(YulIdentifier * 'v) list"

type_synonym vset = "unit locals"

type_synonym 'v frame =
  "('v list * 'v locals)"

definition locals_empty :: "'v locals" where
"locals_empty = []"

(* restrict e1 to the identifiers of e2 
   note that v2 need not be the same type - we can use this to store
   variable-name sets as unit locals
*)
fun restrict :: "'v1 locals \<Rightarrow> 'v2 locals \<Rightarrow> 'v1 locals" where
"restrict [] e2 = []"
| "restrict ((k1, v1)#e1t) (e2) =
  (case map_of e2 k1 of
    None \<Rightarrow> restrict e1t e2
    | Some _ \<Rightarrow> (k1, v1) # restrict e1t e2)"

fun strip_id_type :: "'t YulTypedName \<Rightarrow> YulIdentifier" where
"strip_id_type (YulTypedName name type) = name"

fun strip_id_types :: "'t YulTypedName list \<Rightarrow> YulIdentifier list" where
"strip_id_types l =
  List.map strip_id_type l"

fun del_value :: "'v locals \<Rightarrow> YulIdentifier \<Rightarrow> 'v locals" where
"del_value [] _ = []"
| "del_value ((k, v)#e1t) k' =
   (if k = k' then del_value e1t k'
    else (k, v)#del_value e1t k')"

(* insert a value into locals, fail if already present *)
fun insert_value :: "'v locals \<Rightarrow> YulIdentifier \<Rightarrow> 'v \<Rightarrow> 'v locals option" where
"insert_value L k v =
  (case map_of L k of
    Some _ \<Rightarrow> None
    | None \<Rightarrow> Some ((k, v) # L))"

fun insert_values :: "'v locals \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list \<Rightarrow> 'v locals option" where
"insert_values L [] [] = Some L"
| "insert_values L (ih#it) (vh#vt) =
   (case insert_values L it vt of
    None \<Rightarrow> None
    | Some L' \<Rightarrow> insert_value L' ih vh)"
| "insert_values L _ _ = None"


(* update (or insert if not present) a value into locals *)
fun put_value :: "'v locals \<Rightarrow> YulIdentifier \<Rightarrow> 'v \<Rightarrow> 'v locals" where
"put_value L k v =
  (k, v) # (del_value L k)"

fun put_values :: "'v locals \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list \<Rightarrow> 'v locals option" where
"put_values L [] [] = Some L"
| "put_values L (ih#it) (vh#vt) =
   (case put_values L it vt of
    None \<Rightarrow> None
    | Some L' \<Rightarrow> Some (put_value L' ih vh))"
| "put_values L _ _ = None"

(* insert a value into locals, leaving it unchanged if present *)
fun probe_value :: "'v locals \<Rightarrow> YulIdentifier \<Rightarrow> 'v \<Rightarrow> 'v locals" where
"probe_value L k v =
  (case map_of L k of
    Some _ \<Rightarrow> L
    | None \<Rightarrow> (k, v)#L)"

(* retrieving a value is just map_of *)
fun get_value :: "'v locals \<Rightarrow> YulIdentifier  \<Rightarrow> 'v option" where
"get_value L idn = map_of L idn"

fun get_values :: "'v locals \<Rightarrow> YulIdentifier list \<Rightarrow> 'v list option" where
"get_values L ids =
   List.those (List.map (map_of L) (ids))"

(* convert an association list into a locals, removing duplicates *)
fun make_locals :: "(YulIdentifier * 'v) list \<Rightarrow> 'v locals" where
"make_locals [] = locals_empty"
| "make_locals ((ih, vh)#t) =
    put_value (make_locals t) ih vh"

(* convert an association list into a locals
   this version fails if there is a duplicate key *)
fun make_locals_strict :: "(YulIdentifier * 'v) list \<Rightarrow> 'v locals option" where
"make_locals_strict [] = Some locals_empty"
| "make_locals_strict ((ih, vh)#t) =
  (case make_locals_strict t of
    None \<Rightarrow> None
    | Some t' \<Rightarrow> insert_value t' ih vh)"


(* combine two locals environments, ensuring that
   there is no overlap in keys. *)
fun combine :: "'v locals \<Rightarrow> 'v locals \<Rightarrow> 'v locals option" where
"combine [] l2 = Some l2"
| "combine ((k1, v1)#l1) l2 =
   (case map_of l2 k1 of
    Some _ \<Rightarrow> None
    | None \<Rightarrow>
      (case combine l1 l2 of
        None \<Rightarrow> None
        | Some l \<Rightarrow> Some ((k1, v1) # l)))"

(* combine two locals environments,
   if there is an overlap in keys, keep the value already there *)
fun combine_keep :: "'v locals \<Rightarrow> 'v locals \<Rightarrow> 'v locals" where
"combine_keep l1 [] = l1"
| "combine_keep l1 ((k2, v2)#l2) =
   (case map_of l1 k2 of
    Some _ \<Rightarrow> combine_keep l1 l2
    | None \<Rightarrow> ((k2, v2) # combine_keep l1 l2))"

fun strip_locals :: "'v locals \<Rightarrow> unit locals" where
"strip_locals [] = []"
| "strip_locals ((k, _)#t) =
   (k, ())#strip_locals t"

syntax plus_literal_inst.plus_literal :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal"
  ("_ @@ _")

(* store results of yul statements *)
record ('g, 'v, 't) result =
  global :: "'g"
  locals :: "'v locals"
  (* value stack, used within expression evaluation, as well as
     for assignments and function arguments *)
  vals :: "'v list"  
  (* which functions are currently visible *)
  funs :: "('g, 'v, 't) function_sig locals"

datatype ('g, 'v, 't, 'z) YulResult =
  YulResult "('g, 'v, 't, 'z) result_scheme"
  (* errors can optionally carry failed state *)
  | ErrorResult "String.literal" "('g, 'v, 't, 'z) result_scheme option"

(* pre-passes for constructing function signature environments *)
(* first, construct an environment of function_sigs *)
(* this will return the conflicting name, if there is a name conflict. *)
fun gatherYulFunctions' :: "('g, 'v, 't) function_sig' locals \<Rightarrow>
                           ('v, 't) YulStatement list \<Rightarrow> 
                           (('g, 'v, 't) function_sig' locals + YulIdentifier)" where
"gatherYulFunctions' F [] = Inl F"
| "gatherYulFunctions' F
    ((YulFunctionDefinitionStatement (YulFunctionDefinition name args rets body))#t) =
    (case gatherYulFunctions' F t of
      Inr msg \<Rightarrow> Inr msg
      | Inl F' \<Rightarrow>
      (case insert_value F' name
            \<lparr> f_sig_arguments = args, f_sig_returns = rets, f_sig_body = (YulFunction body) \<rparr> of
        None \<Rightarrow> Inr name
        | Some F'' \<Rightarrow> Inl F''))"
        
| "gatherYulFunctions' F (_#t) =
    gatherYulFunctions' F t"

(* By using combine_keep here,
   we avoid overwriting the visible-names field of existing functions
   (not in the current block) *)
fun gatherYulFunctions :: "('g, 'v, 't) function_sig locals \<Rightarrow>
                           ('v, 't) YulStatement list \<Rightarrow> 
                           (('g, 'v, 't) function_sig locals + YulIdentifier)" where
"gatherYulFunctions F st =
 (let F0 = map (\<lambda> nfs . (case nfs of
                (n, fs) \<Rightarrow> (n, function_sig'.truncate fs))) F in
 (case gatherYulFunctions' F0 st of
  Inr msg \<Rightarrow> Inr msg
  | Inl funcs \<Rightarrow>
   (let names = map fst funcs in
     Inl (combine_keep F (map (\<lambda> nfs . (case nfs of
                    (n, fs) \<Rightarrow> (n, (function_sig'.extend fs \<lparr> f_sig_visible = names \<rparr>)))) funcs)))))"


(* EVM is unityped; everything is 256-bit word *)
type_synonym eint = "256 word"

(* ethereum addresses are 160 bits *)
type_synonym eaddr = "160 word"

type_synonym ebyte = "8 word"


(* data type capturing whether Yul program has terminated, and why *)
datatype YulFlag =
  (* program is executing as normal *)
  is_Executing : Executing
  (* interpreter fuel (not gas) has run out *)
  | FuelOut
  (* EVM gas has run out (does this need to be its own flag?) *)
  | GasOut
  (* execution halted without return value *)
  | Halt
  (* execution halted with value *)
  | Return "8 word list"
  (* gas, target address, value, input data, output memory offset, output size *)
  | Call "eint" "eint" "eint" "8 word list" "eint" "eint"
  (* gas, target address, value, input data, output memory offset, output size *)
  | CallCode "eint" "eint" "eint" "8 word list" "eint" "eint"
  (* gas, target address, input data, output memory offset, output size *)
  | StaticCall "eint" "eint" "8 word list" "eint" "eint"
  (* gas, target address, input data, output memory offset, output size *)
  | DelegateCall "eint" "eint" "8 word list" "eint" "eint"
  (* value, byte-array of contract to create (plus optional semantics) *)
  | Create "eint" "8 word list"
  (* same as create, but with provided salt *)
  | Create2 "eint" "8 word list" "eint"
  (* program has halted and its transaction needs to be reverted;
     refund gas and return a value *)
  | Revert
  (* program has halted and its transaction needs to be reverted;
     do not refund gas and do not return a value*)
  | Throw
  (* program has halted; the smart contract to which it corresponds should be destroyed *)
  | SelfDestruct

(* "locale parameters" passed to Yul semantics
   (capture behaviors needed by certain control primitives) *)
record ('g, 'v, 't) YulDialect =
  is_truthy :: "'v \<Rightarrow> bool"
  init_state :: "'g"
  default_val :: "'v"
  builtins :: "('g, 'v, 't) function_sig locals"
  set_flag :: "YulFlag \<Rightarrow> 'g \<Rightarrow> 'g"
  get_flag :: "'g \<Rightarrow> YulFlag"

end