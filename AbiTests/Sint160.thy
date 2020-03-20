theory Sint160 imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        int160 x = -42;
        return abi.encode(x);
    }
}
*)

(* hex output *)
(*

0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd6

*)

definition test_in :: "8 word list" where
"test_in = hex_splits
''ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd6''"

definition test_schema :: abi_type where
"test_schema = Tsint 160"

definition test_out :: abi_value where
"test_out = Vsint 160 (-42)"

value "test_out"

value "decode test_schema test_in"

value "decode test_schema test_in = Ok test_out"

value "encode test_out = Ok test_in"

end