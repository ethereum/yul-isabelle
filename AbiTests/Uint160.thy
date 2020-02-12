theory Uint160 imports "../AbiTypes" "../Hex" "../AbiDecode"

begin
(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        uint160 x = 42;
        return abi.encode(x);
    }
}


*)

(* hex output *)
(*
0x000000000000000000000000000000000000000000000000000000000000002a
*)

definition test_in :: "8 word list" where
"test_in = 
hex_splits ''000000000000000000000000000000000000000000000000000000000000002a''"

definition test_schema :: abi_type where
"test_schema = Tuint 160"

definition test_out :: abi_value where
"test_out = Vuint 160 42"

value "decode test_schema test_in"

end