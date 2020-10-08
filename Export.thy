theory Export
 imports AbiDecode AbiEncode "HOL.String" "HOL-Library.IArray" "HOL.Code_Numeral"
begin

datatype TypeToken = LParen | RParen | LBrack | RBrack | Comma | Elem string

primrec typeTokenExplode :: "string \<Rightarrow> TypeToken list" where
  "typeTokenExplode (x#tail) = Elem [x]#typeTokenExplode tail"
| "typeTokenExplode [] = []"

fun typeTokenScanParens :: "TypeToken list \<Rightarrow> TypeToken list" where
  "typeTokenScanParens (Elem ''(''#tail) = LParen#typeTokenScanParens tail"
| "typeTokenScanParens (Elem '')''#tail) = RParen#typeTokenScanParens tail"
| "typeTokenScanParens (z#tail) = z#typeTokenScanParens tail"
| "typeTokenScanParens [] = []"

fun typeTokenScanBrackets :: "TypeToken list \<Rightarrow> TypeToken list" where
  "typeTokenScanBrackets (Elem ''[''#tail) = LBrack#typeTokenScanBrackets tail"
| "typeTokenScanBrackets (Elem '']''#tail) = RBrack#typeTokenScanBrackets tail"
| "typeTokenScanBrackets (z#tail) = z#typeTokenScanBrackets tail"
| "typeTokenScanBrackets [] = []"

fun typeTokenScanCommas :: "TypeToken list \<Rightarrow> TypeToken list" where
  "typeTokenScanCommas (Elem '',''#tail) = Comma#typeTokenScanCommas tail"
| "typeTokenScanCommas (z#tail) = z#typeTokenScanCommas tail"
| "typeTokenScanCommas [] = []"

fun typeTokenCombine :: "TypeToken list \<Rightarrow> TypeToken list" where
  "typeTokenCombine (Elem a#Elem b#tail) = typeTokenCombine (Elem (a@b)#tail)"
| "typeTokenCombine (y#tail) = y#typeTokenCombine tail"
| "typeTokenCombine [] = []"

definition scanTypeTokens :: "string \<Rightarrow> TypeToken list" where
  "scanTypeTokens \<equiv> typeTokenCombine o typeTokenScanCommas o typeTokenScanBrackets o typeTokenScanParens o typeTokenExplode"

definition is_digit :: "char \<Rightarrow> bool" where
  "is_digit \<equiv> \<lambda> c . ((of_char c)::nat) \<ge> ((of_char (CHR ''0''))) \<and> ((of_char c)::nat) \<le> ((of_char (CHR ''9'')))"

definition parseDigit :: "char \<Rightarrow> nat option" where
  "parseDigit x \<equiv> if is_digit x then Some (of_char x - of_char (CHR ''0'')) else None"


fun parseNatRev :: "string \<Rightarrow> nat option" where
  "parseNatRev (x#xs) = (case (parseDigit x, parseNatRev xs) of (Some d, Some y) \<Rightarrow> Some (d+y*10) | _ \<Rightarrow> None)"
| "parseNatRev [] = Some 0"

definition parseNat :: "string \<Rightarrow> nat option" where "parseNat \<equiv> \<lambda> x . parseNatRev (List.rev x)"

fun splitDigitSuffix :: "string \<Rightarrow> string \<Rightarrow> (string \<times> nat option)" where
  "splitDigitSuffix (x#tail) parsed = (if is_digit x then
      (case (parseNat (x#tail)) of Some n \<Rightarrow> (List.rev parsed, Some n) | None \<Rightarrow> (List.rev parsed @ (x#tail),None)) else
      splitDigitSuffix tail (x#parsed))"
| "splitDigitSuffix [] parsed = (List.rev parsed,None)"

definition ParseBaseTypePrefix :: "string \<Rightarrow> (nat option \<Rightarrow> abi_type option) option" where
  "ParseBaseTypePrefix \<equiv> [
    ''uint'' \<mapsto> (\<lambda> nopt . map_option (\<lambda> n . Tuint n) nopt),
    ''int'' \<mapsto> (\<lambda> nopt . map_option (\<lambda> n . Tsint n) nopt),
    ''address'' \<mapsto> (\<lambda> opt . case opt of None \<Rightarrow> Some Taddr | _ \<Rightarrow> None),
    ''function'' \<mapsto> (\<lambda> opt . case opt of None \<Rightarrow> Some Taddr | _ \<Rightarrow> None),
    ''bool'' \<mapsto> (\<lambda> opt . case opt of None \<Rightarrow> Some Tbool | _ \<Rightarrow> None),
    ''bytes'' \<mapsto> (\<lambda> opt . case opt of Some n \<Rightarrow> Some (Tfbytes n) | _ \<Rightarrow> Some Tbytes),
    ''string'' \<mapsto> (\<lambda> opt . case opt of None \<Rightarrow> Some (Tstring) | _ \<Rightarrow> None)
  ]"

definition ParseBaseType :: "string \<Rightarrow> abi_type option" where
  "ParseBaseType \<equiv> \<lambda> str . case (splitDigitSuffix str []) of (prefix, nopt) \<Rightarrow>
    (case ParseBaseTypePrefix prefix of Some fn \<Rightarrow> fn nopt | _ \<Rightarrow> None)"

datatype typeParserState = tPS_primary abi_type | tPS_array abi_type "nat option" | tPS_tuple "abi_type list"

fun typeParser :: "TypeToken list \<Rightarrow> typeParserState list \<Rightarrow> abi_type option" where
  "typeParser (LParen#tail) st = typeParser tail (tPS_tuple []#st)"
| "typeParser (Elem x#tail) (tPS_array t None#st) = Option.bind (parseNat x) (\<lambda> n . typeParser tail (tPS_array t (Some n)#st))"
| "typeParser (Elem x#tail) [] = Option.bind (ParseBaseType x) (\<lambda> type . typeParser tail (tPS_primary type#[]))"
| "typeParser (Elem x#tail) (tPS_tuple t#ts) = Option.bind (ParseBaseType x) (\<lambda> type . typeParser tail (tPS_primary type#tPS_tuple t#ts))"
| "typeParser (LBrack#tail) (tPS_primary x#st) = typeParser tail (tPS_array x None#st)"
| "typeParser (RBrack#tail) (tPS_array x nopt#st) = typeParser tail (tPS_primary (case nopt of Some n \<Rightarrow> Tfarray x n | _ \<Rightarrow> Tarray x)#st)"
| "typeParser (RParen#tail) (tPS_primary t#tPS_tuple ts#st) = typeParser tail (tPS_primary (Ttuple (List.rev (t#ts)))#st)"
| "typeParser (Comma#tail) (tPS_primary t#tPS_tuple ts#st) = typeParser tail (tPS_tuple (t#ts)#st)"
| "typeParser [] [tPS_primary x] = Some x"
| "typeParser _ _ = None"

definition parseType :: "string \<Rightarrow> abi_type option" where
  "parseType \<equiv> \<lambda> x . typeParser (scanTypeTokens x) []"

value "parseType ''(uint256[2][1],(uint8,uint9),uint256)''"

definition parseHexDigit :: "char \<Rightarrow> int option" where
  "parseHexDigit x \<equiv> 
    if is_digit x
    then Some (((of_char x)::int) - of_char (CHR ''0''))
    else if (((of_char x)::nat) \<ge> of_char (CHR ''A'') \<and> ((of_char x)::nat) \<le> of_char (CHR ''F''))
    then Some (((of_char x)::int) - of_char (CHR ''A'') + 10)
    else if (((of_char x)::nat) \<ge> of_char (CHR ''a'') \<and> ((of_char x)::nat) \<le> of_char (CHR ''f''))
    then Some (((of_char x)::int) - of_char (CHR ''a'') + 10)
    else None"

definition parseWord :: "char \<Rightarrow> char \<Rightarrow> 8 word option" where
  "parseWord \<equiv> \<lambda> x y . case (parseHexDigit x, parseHexDigit y) of (Some x, Some y) \<Rightarrow> Some (word_of_int (x * 16 + y)) | _ \<Rightarrow> None"

fun parseWords :: "string \<Rightarrow> 8 word list option" where
  "parseWords (x#y#z) = (case (parseWord x y, parseWords z) of (Some b, Some bs) \<Rightarrow> Some (b#bs) | _ \<Rightarrow> None)"
| "parseWords [] = Some []"
| "parseWords [x] = None"

datatype valueParseTree = arrayValue "valueParseTree list" | tupleValue "valueParseTree list" | primaryValue string
datatype valueParserState = vPS_primary valueParseTree | vPS_arrtuple bool "valueParseTree list"
fun valueParser :: "TypeToken list \<Rightarrow> valueParserState list \<Rightarrow> valueParseTree option" where
  "valueParser (Elem x#[]) [] = Some (primaryValue x)"
| "valueParser (Elem x#tail) (vPS_arrtuple w ar#st) = valueParser tail ((vPS_primary (primaryValue x))#vPS_arrtuple w ar#st)"
| "valueParser (LBrack#tail) (st) = valueParser tail (vPS_arrtuple False []#st)"
| "valueParser (LParen#tail) (st) = valueParser tail (vPS_arrtuple True []#st)"
| "valueParser (RBrack#tail) (vPS_arrtuple False arr#st) = valueParser tail ((vPS_primary (arrayValue []))#st)"
| "valueParser (RBrack#tail) (vPS_primary x#vPS_arrtuple False arr#st) = valueParser tail ((vPS_primary (arrayValue (List.rev (x#arr))))#st)"
| "valueParser (RParen#tail) (vPS_primary x#vPS_arrtuple True arr#st) = valueParser tail ((vPS_primary (tupleValue (List.rev (x#arr))))#st)"
| "valueParser (Comma#tail) (vPS_primary x#vPS_arrtuple w arr#st) = valueParser tail (vPS_arrtuple w (x#arr)#st)"
| "valueParser [] [vPS_primary y] = Some y"
| "valueParser _ _ = None"

definition parseU256 :: "string \<Rightarrow> 256 word option" where
  "parseU256 \<equiv> \<lambda> str. (case parseWords str of Some w \<Rightarrow> (if length w = 32 then Some (word_rcat w) else None) | _ \<Rightarrow> None)"

function (sequential) typedValueParser :: "abi_type \<Rightarrow> valueParseTree \<Rightarrow> abi_value option" where
  "typedValueParser (Tuint n) (primaryValue v) = map_option (\<lambda> w . Vuint n (uint w)) (parseU256 v)"
| "typedValueParser (Tsint n) (primaryValue v) = map_option (\<lambda> w . Vsint n (sint w)) (parseU256 v)"
| "typedValueParser Taddr (primaryValue v) = map_option (\<lambda> w . Vaddr (uint w)) (parseU256 v)"
| "typedValueParser (Tfarray t n) (arrayValue vs) = (if (length vs = n) then map_option (\<lambda> vs . Vfarray t n vs) (those (map (\<lambda> v . typedValueParser t v) vs))  else None)"
| "typedValueParser (Tarray t) (arrayValue vs) = (map_option (\<lambda> vs . Varray t vs) (those (map (\<lambda> v . typedValueParser t v) vs)))"
| "typedValueParser (Ttuple ts) (tupleValue vs) = (if (length vs = length ts) then map_option (\<lambda> vs . Vtuple ts vs) (those (map2 (\<lambda> t v . typedValueParser t v) ts vs)) else None)"
| "typedValueParser _ _ = None"
  by pat_completeness auto

primrec valueParseTreeMeasure :: "valueParseTree \<Rightarrow> nat" where
  "valueParseTreeMeasure (primaryValue x) = 1"
| "valueParseTreeMeasure (arrayValue xs) = 1 + (List.foldl (+) 0 (map valueParseTreeMeasure xs))"
| "valueParseTreeMeasure (tupleValue xs) = 1 + (List.foldl (+) 0 (map valueParseTreeMeasure xs))"

termination proof -
  have "x \<in> set vs \<Longrightarrow> valueParseTreeMeasure x \<in> set (map valueParseTreeMeasure vs)" for x vs by auto
  moreover have "(x::nat) \<in> set y \<Longrightarrow> List.foldl (+) 0 y \<ge> x" for x y
  proof -
    have 0: "foldl (+) (x + a) yb = a + foldl (+) x yb" for x a ::nat and yb
      by (induct yb arbitrary: a) (auto simp: add.assoc)
    assume "(x::nat) \<in> set y"
    then obtain ya yb where y_def: "y = ya@[x]@yb"
      by (metis append_Cons append_Nil split_list)
    show "List.foldl (+) 0 y \<ge> x" unfolding y_def
      using 0 by simp
  qed
  ultimately show ?thesis 
    by (relation "measure (\<lambda>(x,y) . valueParseTreeMeasure y)")
       (auto simp: less_SucI set_zip_rightD le_imp_less_Suc)
qed

value "Option.bind (parseType ''int256[]'') (\<lambda> t . Option.bind (valueParser (scanTypeTokens ''[0000000000000000000000000000000000000000000000000000000000000010,0000000000000000000000000000000000000000000000000000000000000011]'') []) (\<lambda> v . typedValueParser t v))"

definition parseTypedValue :: "abi_type \<Rightarrow> string \<Rightarrow> abi_value option" where
  "parseTypedValue \<equiv> \<lambda>type str . Option.bind (valueParser (scanTypeTokens str) []) (\<lambda> vs . typedValueParser type vs)"

value "Option.bind (parseType ''int256[0]'') (\<lambda> t. parseTypedValue t ''[]'')"

(*
  "valueParser (LParen#tail) st = valueParser tail (tupleValue []#st)"
| "valueParser (Elem x#[]) [] = Some (primaryValue x)"
| "valueParser (Elem x#tail) (arrayValue vs#st) = valueParser"
| "valueParser (Elem x#tail) (tPS_tuple t#ts) = Option.bind (ParseBaseType x) (\<lambda> type . typeParser tail (tPS_primary type#tPS_tuple t#ts))"
| "valueParser (LBrack#tail) (tPS_primary x#st) = typeParser tail (tPS_array x None#st)"
| "valueParser (RBrack#tail) (tPS_array x nopt#st) = typeParser tail (tPS_primary (case nopt of Some n \<Rightarrow> Tfarray x n | _ \<Rightarrow> Tarray x)#st)"
| "valueParser (RParen#tail) (tPS_primary t#tPS_tuple ts#st) = typeParser tail (tPS_primary (Ttuple (List.rev (t#ts)))#st)"
| "valueParser (Comma#tail) (tPS_primary t#tPS_tuple ts#st) = typeParser tail (tPS_tuple (t#ts)#st)"
| "valueParser [] [tPS_primary x] = Some x"
| "valueParser _ _ = None"
*)

fun writeHexNibble :: "4 word \<Rightarrow> char" where
  "writeHexNibble x = (if x < 10 then char_of (of_char (CHR ''0'') + uint x) else char_of (of_char (CHR ''A'') + uint x - 10))"

fun writeHexDigit :: "8 word \<Rightarrow> string" where
  "writeHexDigit x = (writeHexNibble (ucast (x >> 4)))#[writeHexNibble (ucast (x AND 0xF))]"

fun writeHex :: "8 word list \<Rightarrow> string" where
  "writeHex (x#tail) = writeHexDigit x@writeHex tail"
| "writeHex [] = ''''"

definition writeInt :: "int \<Rightarrow> string" where
  "writeInt \<equiv> \<lambda> n . (CHR ''0'')#(CHR ''x'')#writeHex (word_rsplit ((word_of_int n)::256 word))"

primrec writeType :: "abi_type \<Rightarrow> string" and
        writeTypeList :: "abi_type list \<Rightarrow> string" where
  "writeType (Ttuple xs) = (CHR ''(''#writeTypeList xs)@('')'')"
| "writeType (Tuint x) = ''uint''@writeInt x"
| "writeType (Tsint x) = ''int''@writeInt x"
| "writeType (Taddr) = ''address''"
| "writeType (Tbool) = ''bool''"
| "writeType (Tfixed x y) = ''fixed''@writeInt x@''x''@writeInt y"
| "writeType (Tufixed x y) = ''ufixed''@writeInt x@''x''@writeInt y"
| "writeType (Tfbytes x) = ''bytes''@writeInt x"
| "writeType (Tfunction) = ''function''"
| "writeType (Tfarray t s) = writeType t@''[''@writeInt s@'']''"
| "writeType (Tbytes) = ''bytes''"
| "writeType (Tstring) = ''string''"
| "writeType (Tarray t) = writeType t@''[]''"
| "writeTypeList (t#ts) = (if ts = [] then writeType t else writeType t@'',''@writeTypeList ts)"
| "writeTypeList [] = ''''"

primrec writeValue :: "abi_value \<Rightarrow> string" and writeValueList :: "abi_value list \<Rightarrow> string" where
  "writeValue (Vuint s value) = writeInt value"
| "writeValue (Vsint s value) = writeInt value"
| "writeValue (Vaddr value) = writeInt value"
| "writeValue (Vbool value) = (if value then ''true'' else ''false'')"
| "writeValue (Vfixed a b x) = ''unsupported''"
| "writeValue (Vufixed a b x) = ''unsupported''"
| "writeValue (Vfbytes s v) = ''0x''@(writeHex v)"
| "writeValue (Vfunction addr sel) = writeInt addr@'':''@writeInt sel"
| "writeValue (Vfarray t n vs) = CHR ''[''#writeValueList vs@'']''"
| "writeValueList (v#vs) = (if vs = [] then writeValue v else writeValue v@'',''@writeValueList vs)"
| "writeValueList [] = ''''"
| "writeValue (Vtuple ts vs) = CHR ''(''#writeValueList vs@'')''"
| "writeValue (Varray t vs) = CHR ''[''#writeValueList vs@'']''"
| "writeValue (Vbytes v) = ''0x''@(writeHex v)"
| "writeValue (Vstring str) = ''0x''@writeHex (map (\<lambda> x . word_of_int (of_char x)) str)"

definition Decode :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "Decode \<equiv> \<lambda> type encoding .
    case parseType (literal.explode type) of Some type \<Rightarrow>
    (
      case parseWords (literal.explode encoding) of Some encoding \<Rightarrow>
      (
        case decode type encoding of (Ok value) \<Rightarrow> String.implode (''OK: ''@writeValue value)
        | Err msg \<Rightarrow> String.implode (''ERR: ''@msg)
      )
      | _ \<Rightarrow> String.implode ''ERR: Cannot parse encoding.''
    )
    | _ \<Rightarrow> String.implode ''ERR: Cannot parse type.''
"

export_code Decode in SML module_name ABICoder file_prefix abicoder

end