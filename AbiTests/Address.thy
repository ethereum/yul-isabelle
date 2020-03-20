theory Address imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        address x = 0x52908400098527886E0F7030069857D2E4169EE7;
        return abi.encode(x);
    }
}
*)

(*hex output *)

(*

0x00000000000000000000000052908400098527886e0f7030069857d2e4169ee7
*)

definition test_in :: "8 word list" where
"test_in = 
hex_splits ''00000000000000000000000052908400098527886e0f7030069857d2e4169ee7''"

definition test_schema :: abi_type where
"test_schema = Taddr"

definition test_out :: "abi_value" where
"test_out = Vaddr (hexread ''52908400098527886e0f7030069857d2e4169ee7'')"

value "test_out"

value "decode test_schema test_in = Ok test_out"

value "encode test_out = Ok test_in"


end