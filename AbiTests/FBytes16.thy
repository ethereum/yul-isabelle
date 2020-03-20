theory FBytes16 imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"

begin

(* solidity *)

(*
 contract C {
    function getEncoding() external returns (bytes memory) {
                    bytes16 x = hex"DEADBEEFDEADBEEFDEADBEEFDEADBEEF";
        return abi.encode(x);
    }
}

*)

(* hex output *)
(*
{
0xdeadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000
}
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''deadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000''"

definition test_schema :: abi_type where
"test_schema = Tfbytes 16"

definition test_out :: "abi_value" where
"test_out = Vfbytes 16 (hex_splits ''deadbeefdeadbeefdeadbeefdeadbeef'')"

value "test_in"

value "decode test_schema test_in"
value "decode test_schema test_in = Ok test_out"

value "encode test_out = Ok test_in"

value "encode test_out"

end