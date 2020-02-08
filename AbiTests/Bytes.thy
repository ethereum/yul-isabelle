theory Bytes imports "../AbiTypes" "../Hex"

begin

(* solidity *)

(*
 contract C {
    function getEncoding() external returns (bytes memory) {
                    bytes memory x = hex"DEADBEEFDEADBEEFDEADBEEFDEADBEEF";
        return abi.encode(x);
    }
}
*)

(* hex output (raw) *)

(*

0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010deadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000"

*)

(* hex output (trimmed) *)

(*
0000000000000000000000000000000000000000000000000000000000000010deadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''0000000000000000000000000000000000000000000000000000000000000010deadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000''"

definition test_schema :: abi_type where
"test_schema = Tbytes"

definition test_out :: "abi_value" where
"test_out = Vbytes (hex_splits ''deadbeefdeadbeefdeadbeefdeadbeef'')"

value "decode test_schema test_in"

value test_out

end