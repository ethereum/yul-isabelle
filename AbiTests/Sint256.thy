theory Sint256 imports "../AbiTypes" "../Hex"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        int256 x = (-1) * 0x7EADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF;
        return abi.encode(x);
    }
}
*)

(* hex output *)

(*

 0x8152411021524110215241102152411021524110215241102152411021524111"
*)


definition test_in :: "8 word list" where
"test_in = hex_splits
''8152411021524110215241102152411021524110215241102152411021524111''"

definition test_schema :: abi_type where
"test_schema = Tsint 256"

definition test_out :: abi_value where
"test_out = Vsint 256 ( (-1) * 0x7EADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF) "

value "test_out"

value "decode test_schema test_in"
end