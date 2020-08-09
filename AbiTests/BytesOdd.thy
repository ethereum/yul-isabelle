theory BytesOdd imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"
 
begin

(* test of for byte-strings with an odd number of bytes
(thus, not divisible by 32 - this was a case i had been decoding incorrectly. *)

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

{
	"0": "bytes: 0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000fdeadbeefdeadbeefdeadbeefdeadbe0000000000000000000000000000000000"
}
*)

(* hex output (trimmed) *)

(*
	"0": "bytes: 000000000000000000000000000000000000000000000000000000000000000fdeadbeefdeadbeefdeadbeefdeadbe0000000000000000000000000000000000"
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''000000000000000000000000000000000000000000000000000000000000000fdeadbeefdeadbeefdeadbeefdeadbe0000000000000000000000000000000000''"

definition test_schema :: abi_type where
"test_schema = Tbytes"

definition test_out :: "abi_value" where
"test_out = Vbytes (hex_splits ''deadbeefdeadbeefdeadbeefdeadbe'')"

value "decode test_schema test_in = Ok test_out"

value "encode test_out = Ok test_in"

end