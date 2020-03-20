theory Bool imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"

begin
(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        bool x = true;
        return abi.encode(x);
    }
}
*)

(* hex output *)
(*
bytes: 0x0000000000000000000000000000000000000000000000000000000000000001
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''0000000000000000000000000000000000000000000000000000000000000001''"

definition test_schema :: abi_type where
"test_schema = Tbool"

definition test_out :: abi_value where
"test_out = Vbool True"

value "decode test_schema test_in = Ok test_out"
value "encode test_out = Ok test_in"

end
