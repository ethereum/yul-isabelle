theory AbiTypesSyntax
  imports AbiTypes
begin

nonterminal \<tau>
nonterminal tuple_args

context
begin
abbreviation (input) Tuint8 where "Tuint8 \<equiv> Tuint 8"
abbreviation (input) Tuint16 where "Tuint16 \<equiv> Tuint 16"
abbreviation (input) Tuint24 where "Tuint24 \<equiv> Tuint 24"
abbreviation (input) Tuint32 where "Tuint32 \<equiv> Tuint 32"
abbreviation (input) Tuint40 where "Tuint40 \<equiv> Tuint 40"
abbreviation (input) Tuint48 where "Tuint48 \<equiv> Tuint 48"
abbreviation (input) Tuint56 where "Tuint56 \<equiv> Tuint 56"
abbreviation (input) Tuint64 where "Tuint64 \<equiv> Tuint 64"
abbreviation (input) Tuint72 where "Tuint72 \<equiv> Tuint 72"
abbreviation (input) Tuint80 where "Tuint80 \<equiv> Tuint 80"
abbreviation (input) Tuint88 where "Tuint88 \<equiv> Tuint 88"
abbreviation (input) Tuint96 where "Tuint96 \<equiv> Tuint 96"
abbreviation (input) Tuint104 where "Tuint104 \<equiv> Tuint 104"
abbreviation (input) Tuint112 where "Tuint112 \<equiv> Tuint 112"
abbreviation (input) Tuint120 where "Tuint120 \<equiv> Tuint 120"
abbreviation (input) Tuint128 where "Tuint128 \<equiv> Tuint 128"
abbreviation (input) Tuint136 where "Tuint136 \<equiv> Tuint 136"
abbreviation (input) Tuint144 where "Tuint144 \<equiv> Tuint 144"
abbreviation (input) Tuint152 where "Tuint152 \<equiv> Tuint 152"
abbreviation (input) Tuint160 where "Tuint160 \<equiv> Tuint 160"
abbreviation (input) Tuint168 where "Tuint168 \<equiv> Tuint 168"
abbreviation (input) Tuint176 where "Tuint176 \<equiv> Tuint 176"
abbreviation (input) Tuint184 where "Tuint184 \<equiv> Tuint 184"
abbreviation (input) Tuint192 where "Tuint192 \<equiv> Tuint 192"
abbreviation (input) Tuint200 where "Tuint200 \<equiv> Tuint 200"
abbreviation (input) Tuint208 where "Tuint208 \<equiv> Tuint 208"
abbreviation (input) Tuint216 where "Tuint216 \<equiv> Tuint 216"
abbreviation (input) Tuint224 where "Tuint224 \<equiv> Tuint 224"
abbreviation (input) Tuint232 where "Tuint232 \<equiv> Tuint 232"
abbreviation (input) Tuint240 where "Tuint240 \<equiv> Tuint 240"
abbreviation (input) Tuint248 where "Tuint248 \<equiv> Tuint 248"
abbreviation (input) Tuint256 where "Tuint256 \<equiv> Tuint 256"
abbreviation (input) Tsint8 where "Tsint8 \<equiv> Tsint 8"
abbreviation (input) Tsint16 where "Tsint16 \<equiv> Tsint 16"
abbreviation (input) Tsint24 where "Tsint24 \<equiv> Tsint 24"
abbreviation (input) Tsint32 where "Tsint32 \<equiv> Tsint 32"
abbreviation (input) Tsint40 where "Tsint40 \<equiv> Tsint 40"
abbreviation (input) Tsint48 where "Tsint48 \<equiv> Tsint 48"
abbreviation (input) Tsint56 where "Tsint56 \<equiv> Tsint 56"
abbreviation (input) Tsint64 where "Tsint64 \<equiv> Tsint 64"
abbreviation (input) Tsint72 where "Tsint72 \<equiv> Tsint 72"
abbreviation (input) Tsint80 where "Tsint80 \<equiv> Tsint 80"
abbreviation (input) Tsint88 where "Tsint88 \<equiv> Tsint 88"
abbreviation (input) Tsint96 where "Tsint96 \<equiv> Tsint 96"
abbreviation (input) Tsint104 where "Tsint104 \<equiv> Tsint 104"
abbreviation (input) Tsint112 where "Tsint112 \<equiv> Tsint 112"
abbreviation (input) Tsint120 where "Tsint120 \<equiv> Tsint 120"
abbreviation (input) Tsint128 where "Tsint128 \<equiv> Tsint 128"
abbreviation (input) Tsint136 where "Tsint136 \<equiv> Tsint 136"
abbreviation (input) Tsint144 where "Tsint144 \<equiv> Tsint 144"
abbreviation (input) Tsint152 where "Tsint152 \<equiv> Tsint 152"
abbreviation (input) Tsint160 where "Tsint160 \<equiv> Tsint 160"
abbreviation (input) Tsint168 where "Tsint168 \<equiv> Tsint 168"
abbreviation (input) Tsint176 where "Tsint176 \<equiv> Tsint 176"
abbreviation (input) Tsint184 where "Tsint184 \<equiv> Tsint 184"
abbreviation (input) Tsint192 where "Tsint192 \<equiv> Tsint 192"
abbreviation (input) Tsint200 where "Tsint200 \<equiv> Tsint 200"
abbreviation (input) Tsint208 where "Tsint208 \<equiv> Tsint 208"
abbreviation (input) Tsint216 where "Tsint216 \<equiv> Tsint 216"
abbreviation (input) Tsint224 where "Tsint224 \<equiv> Tsint 224"
abbreviation (input) Tsint232 where "Tsint232 \<equiv> Tsint 232"
abbreviation (input) Tsint240 where "Tsint240 \<equiv> Tsint 240"
abbreviation (input) Tsint248 where "Tsint248 \<equiv> Tsint 248"
abbreviation (input) Tsint256 where "Tsint256 \<equiv> Tsint 256"
abbreviation (input) Tfbytes1 where "Tfbytes1 \<equiv> Tfbytes 1"
abbreviation (input) Tfbytes2 where "Tfbytes2 \<equiv> Tfbytes 2"
abbreviation (input) Tfbytes3 where "Tfbytes3 \<equiv> Tfbytes 3"
abbreviation (input) Tfbytes4 where "Tfbytes4 \<equiv> Tfbytes 4"
abbreviation (input) Tfbytes5 where "Tfbytes5 \<equiv> Tfbytes 5"
abbreviation (input) Tfbytes6 where "Tfbytes6 \<equiv> Tfbytes 6"
abbreviation (input) Tfbytes7 where "Tfbytes7 \<equiv> Tfbytes 7"
abbreviation (input) Tfbytes8 where "Tfbytes8 \<equiv> Tfbytes 8"
abbreviation (input) Tfbytes9 where "Tfbytes9 \<equiv> Tfbytes 9"
abbreviation (input) Tfbytes10 where "Tfbytes10 \<equiv> Tfbytes 10"
abbreviation (input) Tfbytes11 where "Tfbytes11 \<equiv> Tfbytes 11"
abbreviation (input) Tfbytes12 where "Tfbytes12 \<equiv> Tfbytes 12"
abbreviation (input) Tfbytes13 where "Tfbytes13 \<equiv> Tfbytes 13"
abbreviation (input) Tfbytes14 where "Tfbytes14 \<equiv> Tfbytes 14"
abbreviation (input) Tfbytes15 where "Tfbytes15 \<equiv> Tfbytes 15"
abbreviation (input) Tfbytes16 where "Tfbytes16 \<equiv> Tfbytes 16"
abbreviation (input) Tfbytes17 where "Tfbytes17 \<equiv> Tfbytes 17"
abbreviation (input) Tfbytes18 where "Tfbytes18 \<equiv> Tfbytes 18"
abbreviation (input) Tfbytes19 where "Tfbytes19 \<equiv> Tfbytes 19"
abbreviation (input) Tfbytes20 where "Tfbytes20 \<equiv> Tfbytes 20"
abbreviation (input) Tfbytes21 where "Tfbytes21 \<equiv> Tfbytes 21"
abbreviation (input) Tfbytes22 where "Tfbytes22 \<equiv> Tfbytes 22"
abbreviation (input) Tfbytes23 where "Tfbytes23 \<equiv> Tfbytes 23"
abbreviation (input) Tfbytes24 where "Tfbytes24 \<equiv> Tfbytes 24"
abbreviation (input) Tfbytes25 where "Tfbytes25 \<equiv> Tfbytes 25"
abbreviation (input) Tfbytes26 where "Tfbytes26 \<equiv> Tfbytes 26"
abbreviation (input) Tfbytes27 where "Tfbytes27 \<equiv> Tfbytes 27"
abbreviation (input) Tfbytes28 where "Tfbytes28 \<equiv> Tfbytes 28"
abbreviation (input) Tfbytes29 where "Tfbytes29 \<equiv> Tfbytes 29"
abbreviation (input) Tfbytes30 where "Tfbytes30 \<equiv> Tfbytes 30"
abbreviation (input) Tfbytes31 where "Tfbytes31 \<equiv> Tfbytes 31"
abbreviation (input) Tfbytes32 where "Tfbytes32 \<equiv> Tfbytes 32"
abbreviation (input) unary_tuple_helper where "unary_tuple_helper x \<equiv> [x]"
abbreviation (input) Tempty_tuple where "Tempty_tuple \<equiv> Ttuple []"
end

syntax
  "" :: "\<tau> \<Rightarrow> abi_type" ("ABI'_TYPE\<guillemotleft>_\<guillemotright>")
  "Tuint" :: "num \<Rightarrow> \<tau>" ("uint<_>")
  "Tuint8" :: "\<tau>" ("uint8")
  "Tuint16" :: "\<tau>" ("uint16")
  "Tuint24" :: "\<tau>" ("uint24")
  "Tuint32" :: "\<tau>" ("uint32")
  "Tuint40" :: "\<tau>" ("uint40")
  "Tuint48" :: "\<tau>" ("uint48")
  "Tuint56" :: "\<tau>" ("uint56")
  "Tuint64" :: "\<tau>" ("uint64")
  "Tuint72" :: "\<tau>" ("uint72")
  "Tuint80" :: "\<tau>" ("uint80")
  "Tuint88" :: "\<tau>" ("uint88")
  "Tuint96" :: "\<tau>" ("uint96")
  "Tuint104" :: "\<tau>" ("uint104")
  "Tuint112" :: "\<tau>" ("uint112")
  "Tuint120" :: "\<tau>" ("uint120")
  "Tuint128" :: "\<tau>" ("uint128")
  "Tuint136" :: "\<tau>" ("uint136")
  "Tuint144" :: "\<tau>" ("uint144")
  "Tuint152" :: "\<tau>" ("uint152")
  "Tuint160" :: "\<tau>" ("uint160")
  "Tuint168" :: "\<tau>" ("uint168")
  "Tuint176" :: "\<tau>" ("uint176")
  "Tuint184" :: "\<tau>" ("uint184")
  "Tuint192" :: "\<tau>" ("uint192")
  "Tuint200" :: "\<tau>" ("uint200")
  "Tuint208" :: "\<tau>" ("uint208")
  "Tuint216" :: "\<tau>" ("uint216")
  "Tuint224" :: "\<tau>" ("uint224")
  "Tuint232" :: "\<tau>" ("uint232")
  "Tuint240" :: "\<tau>" ("uint240")
  "Tuint248" :: "\<tau>" ("uint248")
  "Tuint256" :: "\<tau>" ("uint256")
  "Tsint" :: "num \<Rightarrow> \<tau>" ("int<_>")
  "Tsint8" :: "\<tau>" ("int8")
  "Tsint16" :: "\<tau>" ("int16")
  "Tsint24" :: "\<tau>" ("int24")
  "Tsint32" :: "\<tau>" ("int32")
  "Tsint40" :: "\<tau>" ("int40")
  "Tsint48" :: "\<tau>" ("int48")
  "Tsint56" :: "\<tau>" ("int56")
  "Tsint64" :: "\<tau>" ("int64")
  "Tsint72" :: "\<tau>" ("int72")
  "Tsint80" :: "\<tau>" ("int80")
  "Tsint88" :: "\<tau>" ("int88")
  "Tsint96" :: "\<tau>" ("int96")
  "Tsint104" :: "\<tau>" ("int104")
  "Tsint112" :: "\<tau>" ("int112")
  "Tsint120" :: "\<tau>" ("int120")
  "Tsint128" :: "\<tau>" ("int128")
  "Tsint136" :: "\<tau>" ("int136")
  "Tsint144" :: "\<tau>" ("int144")
  "Tsint152" :: "\<tau>" ("int152")
  "Tsint160" :: "\<tau>" ("int160")
  "Tsint168" :: "\<tau>" ("int168")
  "Tsint176" :: "\<tau>" ("int176")
  "Tsint184" :: "\<tau>" ("int184")
  "Tsint192" :: "\<tau>" ("int192")
  "Tsint200" :: "\<tau>" ("int200")
  "Tsint208" :: "\<tau>" ("int208")
  "Tsint216" :: "\<tau>" ("int216")
  "Tsint224" :: "\<tau>" ("int224")
  "Tsint232" :: "\<tau>" ("int232")
  "Tsint240" :: "\<tau>" ("int240")
  "Tsint248" :: "\<tau>" ("int248")
  "Tsint256" :: "\<tau>" ("int256")
  "Taddr" :: "\<tau>" ("address")
  "Tbool" :: "\<tau>" ("bool")
  "Tfixed" :: "num \<Rightarrow> num \<Rightarrow> \<tau>" ("fixed<_,_>")
  "Tufixed" :: "num \<Rightarrow> num \<Rightarrow> \<tau>" ("ufixed<_,_>")
  "Tfbytes" :: "num \<Rightarrow> \<tau>" ("bytes<_>")
  "Tbytes1" :: "\<tau>" ("bytes1")
  "Tbytes2" :: "\<tau>" ("bytes2")
  "Tbytes3" :: "\<tau>" ("bytes3")
  "Tbytes4" :: "\<tau>" ("bytes4")
  "Tbytes5" :: "\<tau>" ("bytes5")
  "Tbytes6" :: "\<tau>" ("bytes6")
  "Tbytes7" :: "\<tau>" ("bytes7")
  "Tbytes8" :: "\<tau>" ("bytes8")
  "Tbytes9" :: "\<tau>" ("bytes9")
  "Tbytes10" :: "\<tau>" ("bytes10")
  "Tbytes11" :: "\<tau>" ("bytes11")
  "Tbytes12" :: "\<tau>" ("bytes12")
  "Tbytes13" :: "\<tau>" ("bytes13")
  "Tbytes14" :: "\<tau>" ("bytes14")
  "Tbytes15" :: "\<tau>" ("bytes15")
  "Tbytes16" :: "\<tau>" ("bytes16")
  "Tbytes17" :: "\<tau>" ("bytes17")
  "Tbytes18" :: "\<tau>" ("bytes18")
  "Tbytes19" :: "\<tau>" ("bytes19")
  "Tbytes20" :: "\<tau>" ("bytes20")
  "Tbytes21" :: "\<tau>" ("bytes21")
  "Tbytes22" :: "\<tau>" ("bytes22")
  "Tbytes23" :: "\<tau>" ("bytes23")
  "Tbytes24" :: "\<tau>" ("bytes24")
  "Tbytes25" :: "\<tau>" ("bytes25")
  "Tbytes26" :: "\<tau>" ("bytes26")
  "Tbytes27" :: "\<tau>" ("bytes27")
  "Tbytes28" :: "\<tau>" ("bytes28")
  "Tbytes29" :: "\<tau>" ("bytes29")
  "Tbytes30" :: "\<tau>" ("bytes30")
  "Tbytes31" :: "\<tau>" ("bytes31")
  "Tbytes32" :: "\<tau>" ("bytes32")
  "Tfunction" :: "\<tau>" ("function")
  "Tbytes" :: "\<tau>" ("bytes")
  "Tstring" :: "\<tau>" ("string")
  "Tarray" :: "\<tau> \<Rightarrow> \<tau>" ("_[]")
  "Tfarray" :: "\<tau> \<Rightarrow> num \<Rightarrow> \<tau>" ("_[_]")
  "unary_tuple_helper" :: "\<tau> \<Rightarrow> tuple_args" ("_")
  "Cons" :: "\<tau> \<Rightarrow> tuple_args \<Rightarrow> tuple_args" ("_,_" 1)
  "Cons" :: "id_position \<Rightarrow> id_position \<Rightarrow> tuple_args" ("_#_" 1)
  "Ttuple" :: "tuple_args \<Rightarrow> \<tau>" ("'((_)')")
  "Tempty_tuple" :: "\<tau>" ("'(')")
  "" :: "id_position \<Rightarrow> \<tau>" ("_")

(* Unfortunately required workaround, since Isabelle otherwise doesn't
 * properly distinguish type from term namespaces. *)
type_notation bool ("bool")

value "ABI_TYPE\<guillemotleft>uint8\<guillemotright>"
value "ABI_TYPE\<guillemotleft>uint16\<guillemotright>"
value "ABI_TYPE\<guillemotleft>uint<16>\<guillemotright>"
value "ABI_TYPE\<guillemotleft>uint256\<guillemotright>"

value "ABI_TYPE\<guillemotleft>int8\<guillemotright>"
value "ABI_TYPE\<guillemotleft>int16\<guillemotright>"
value "ABI_TYPE\<guillemotleft>int<16>\<guillemotright>"
value "ABI_TYPE\<guillemotleft>int256\<guillemotright>"

value "ABI_TYPE\<guillemotleft>bool\<guillemotright>"
value "ABI_TYPE\<guillemotleft>address\<guillemotright>"
value "ABI_TYPE\<guillemotleft>function\<guillemotright>"
value "ABI_TYPE\<guillemotleft>string\<guillemotright>"
value "ABI_TYPE\<guillemotleft>bytes\<guillemotright>"
value "ABI_TYPE\<guillemotleft>(int8)\<guillemotright>"
value "ABI_TYPE\<guillemotleft>(bytes,uint8)\<guillemotright>"
value "ABI_TYPE\<guillemotleft>(bytes,int8,uint32)\<guillemotright>"
value "ABI_TYPE\<guillemotleft>(bytes,int8[],uint32[8])\<guillemotright>"
value "ABI_TYPE\<guillemotleft>(bytes[2],int8[],uint<32>[8][][9])[9]\<guillemotright>"

fun dummy :: "abi_type \<Rightarrow> nat" where
  "dummy ABI_TYPE\<guillemotleft>uint<x>\<guillemotright> = x"
| "dummy ABI_TYPE\<guillemotleft>int<x>\<guillemotright> = x"
| "dummy ABI_TYPE\<guillemotleft>bytes<x>\<guillemotright> = x"
| "dummy ABI_TYPE\<guillemotleft>address\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>fixed<a,b>\<guillemotright> = a + b"
| "dummy ABI_TYPE\<guillemotleft>ufixed<a,b>\<guillemotright> = a + b"
| "dummy ABI_TYPE\<guillemotleft>x[y]\<guillemotright> = y"
| "dummy ABI_TYPE\<guillemotleft>bool\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>function\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>()\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>(h#tail)\<guillemotright> = dummy h + length tail"
| "dummy ABI_TYPE\<guillemotleft>bytes\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>string\<guillemotright> = 0"
| "dummy ABI_TYPE\<guillemotleft>x[]\<guillemotright> = 0"

end