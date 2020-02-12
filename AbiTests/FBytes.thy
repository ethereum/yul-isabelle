theory FBytes imports "../AbiTypes" "../Hex" "../AbiDecode"

begin

(* solidity *)

(*
contract C {
    function getEncoding() external returns (bytes memory) {
                    bytes32 x = hex"DEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF";
        return abi.encode(x);
    }
}
*)

(* hex output *)
(*
0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef''"

definition test_schema :: abi_type where
"test_schema = Tfbytes 32"

definition test_out :: abi_value where
"test_out = Vfbytes 32 (hex_splits ''deadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef'')"

value "decode test_schema test_in = Ok test_out"

end