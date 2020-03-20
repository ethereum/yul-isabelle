theory StringTest imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"

begin

(* solidity *)

(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        string memory x = "hello, world!";
        return abi.encode(x);
    }
}
*)

(* hex output *)

(*

0x0000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000d68656c6c6f2c20776f726c642100000000000000000000000000000000000000"

*)

(* hex output (outer header trimmed) *)

(*

0x000000000000000000000000000000000000000000000000000000000000000d68656c6c6f2c20776f726c642100000000000000000000000000000000000000
*)

definition test_in :: "8 word list" where
"test_in = hex_splits
''000000000000000000000000000000000000000000000000000000000000000d68656c6c6f2c20776f726c642100000000000000000000000000000000000000''"

definition test_schema :: abi_type where
"test_schema = Tstring"

definition test_out :: abi_value where
"test_out = Vstring ''hello, world!''"

value "test_out"

value "decode test_schema test_in"


value "decode test_schema test_in = Ok test_out"
value "encode test_out = Ok test_in"

end