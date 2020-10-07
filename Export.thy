theory Export
 imports AbiDecode AbiEncode "HOL.String" "HOL-Library.IArray" "HOL.Code_Numeral"
begin

datatype TypeToken = LParen | RParen | LBrack | RBrack | Comma | Elem string

primrec explode1 :: "string \<Rightarrow> TypeToken list" where
  "explode1 (x#tail) = Elem [x]#explode1 tail"
| "explode1 [] = []"

fun scanParens :: "TypeToken list \<Rightarrow> TypeToken list" where
  "scanParens (Elem ''(''#tail) = LParen#scanParens tail"
| "scanParens (Elem '')''#tail) = RParen#scanParens tail"
| "scanParens (z#tail) = z#scanParens tail"
| "scanParens [] = []"

fun scanBrackets :: "TypeToken list \<Rightarrow> TypeToken list" where
  "scanBrackets (Elem ''[''#tail) = LBrack#scanBrackets tail"
| "scanBrackets (Elem '']''#tail) = RBrack#scanBrackets tail"
| "scanBrackets (z#tail) = z#scanBrackets tail"
| "scanBrackets [] = []"

fun scanComma :: "TypeToken list \<Rightarrow> TypeToken list" where
  "scanComma (Elem '',''#tail) = Comma#scanComma tail"
| "scanComma (z#tail) = z#scanComma tail"
| "scanComma [] = []"

fun scanCombine :: "TypeToken list \<Rightarrow> TypeToken list" where
  "scanCombine (Elem a#Elem b#tail) = scanCombine (Elem (a@b)#tail)"
| "scanCombine (y#tail) = y#scanCombine tail"
| "scanCombine [] = []"

definition scan :: "string \<Rightarrow> TypeToken list" where
  "scan \<equiv> \<lambda> input. scanCombine (scanComma (scanBrackets (scanParens (explode1 input))))"

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



term "x::char"

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
  (case ParseBaseTypePrefix prefix of Some fn \<Rightarrow> fn nopt | _ \<Rightarrow> None)
"

datatype Type = Type abi_type | Tuple "Type list" | Array Type string

fun TypeM :: "Type \<Rightarrow> nat" where
  "TypeM (Type _) = 1"
| "TypeM (Tuple x) = length x + sum_list (map TypeM x)"
| "TypeM (Array x []) = 2 + TypeM x"
| "TypeM (Array x y) = 3 + TypeM x"

fun M :: "TypeToken list + TypeToken list + (TypeToken list \<times> Type list) \<Rightarrow> nat" where
  "M (Inl x) = length x"
| "M (Inr (Inl x)) = length x"
| "M (Inr (Inr (x, y))) = 1 + length x + sum_list (map TypeM y)"

term "char_of"
term "of_char"

function (sequential) parse :: "TypeToken list \<Rightarrow> (TypeToken list \<times> abi_type) option" and
    parseArray :: "TypeToken list \<Rightarrow> (TypeToken list \<times> abi_type) option" and 
    parseTuple :: "TypeToken list \<Rightarrow> abi_type list \<Rightarrow> (TypeToken list \<times> abi_type list) option" where
  "parse (RBrack#tail) = parseArray tail"
| "parse (Elem x#tail) = (case ParseBaseType x of Some type \<Rightarrow> Some (tail, type) | _ \<Rightarrow> None)"
| "parse (RParen#tail) = (case parseTuple tail [] of Some (tail, types) \<Rightarrow> Some (tail, Ttuple (List.rev types)) | _ \<Rightarrow> None)"
| "parse _ = None"
| "parseArray (LBrack#tail) = (case parse tail of Some (tail, type) \<Rightarrow> Some (tail,Tarray type) | _ \<Rightarrow> None)"
| "parseArray (Elem x#LBrack#tail) = (case parse tail of Some (tail, type) \<Rightarrow>
    (case parseNat x of (Some n) \<Rightarrow> Some (tail, Tfarray type n) | _ \<Rightarrow> None)
     | _ \<Rightarrow> None
)"
| "parseArray oth = None"
| "parseTuple (LParen#tail) staged = Some (tail, staged)"
| "parseTuple [] staged = None"
| "parseTuple oth staged = (case parse oth of Some (LParen#tail, type) \<Rightarrow> Some (tail, type#staged)
                                              | Some (Comma#tail, type) \<Rightarrow> (
            case (parseTuple tail []) of Some (tail, types) \<Rightarrow> Some (tail, type#types) | _ \<Rightarrow> None
)
                                              | _ \<Rightarrow> None)"
  by auto pat_completeness

termination 
  sorry (* TODO *)

definition readType :: "string \<Rightarrow> abi_type option" where
  "readType \<equiv> \<lambda> x . case (parse (List.rev (scan x))) of Some ([], x) \<Rightarrow> Some x | _ \<Rightarrow> None"

value "parse (List.rev (scan ''(uint256[2][1])''))"
value "readType ''(uint256[2][1],(uint8,uint9),uint256)''"
(*
fun writeNat :: "nat \<Rightarrow> string" where
  "writeNat x = (if x < 10 then [char_of (of_char (CHR ''0'') + x)] else writeNat (x div 10)@writeNat (x mod 10))"


definition writeInt :: "int \<Rightarrow> string" where
  "writeInt \<equiv> (\<lambda> x . if x < 0 then CHR ''-''#writeNat (nat (-x)) else writeNat (nat x))"
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

term "decode"

definition parseHexDigit :: "char \<Rightarrow> int option" where
  "parseHexDigit x \<equiv> (if (((of_char x)::nat) \<ge> of_char (CHR ''0'') \<and> ((of_char x)::nat) \<le> of_char (CHR ''9'')) then
                        Some (((of_char x)::int) - of_char (CHR ''0''))
                      else (
  if (((of_char x)::nat) \<ge> of_char (CHR ''A'') \<and> ((of_char x)::nat) \<le> of_char (CHR ''F'')) then
                        Some (((of_char x)::int) - of_char (CHR ''A'') + 10)
  else (  if (((of_char x)::nat) \<ge> of_char (CHR ''a'') \<and> ((of_char x)::nat) \<le> of_char (CHR ''f'')) then
                        Some (((of_char x)::int) - of_char (CHR ''a'') + 10)
  else
None
)
) )"


definition parseWord :: "char \<Rightarrow> char \<Rightarrow> 8 word option" where
  "parseWord \<equiv> \<lambda> x y . case (parseHexDigit x, parseHexDigit y) of (Some x, Some y) \<Rightarrow> Some (word_of_int (x * 16 + y)) | _ \<Rightarrow> None"

fun parseWords :: "string \<Rightarrow> 8 word list option" where
  "parseWords (x#y#z) = (case (parseWord x y, parseWords z) of (Some b, Some bs) \<Rightarrow> Some (b#bs) | _ \<Rightarrow> None)"
| "parseWords [] = Some []"
| "parseWords [x] = None"

term "case_option"

definition Decode :: "String.literal \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "Decode \<equiv> \<lambda> type encoding . 
    case (Option.bind (readType (literal.explode type))
      (\<lambda> type . map_option (\<lambda> encoding . decode type encoding) (parseWords (literal.explode encoding))))
      of (Some result) \<Rightarrow> (case result of (Ok value) \<Rightarrow> String.implode (writeValue value) | (Err reason) \<Rightarrow> String.implode (''ERR: ''@reason)
) | _ \<Rightarrow> String.implode ''ERR: INVALID INPUT''"

value "decode (Ttuple [Tuint 256,Tuint 256]) (the (parseWords ''000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F000000000000000000000000000000000000000000000000000000000000001F''))"

value "readType ''(uint248,uint8)''"

value "Decode (String.implode ''(uint248,uint8[1])'') (String.implode ''000102030405060708090A0B0C0D0E0F101112131415161718191A1B1C1D1E1F000000000000000000000000000000000000000000000000000000000000001F'')"

export_code Decode in SML module_name ABICoder file_prefix abicoder

end