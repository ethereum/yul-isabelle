theory Uint256 imports "../AbiTypes" "../Hex"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        uint256 x = 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF;
        return abi.encode(x);
    }
}
*)

(* hex output *)

(*
0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
*)

definition test_in :: "8 word list" where
"test_in = hex_splits
''deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef''"

definition test_schema :: abi_type where
"test_schema = Tuint 256"

definition test_out :: abi_value where
"test_out = Vuint 256 (hexread ''deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef'')"

value "test_out"

value "decode test_schema test_in"

end