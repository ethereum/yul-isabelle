theory Tuple imports "../AbiTypes" "../Hex" "../AbiDecode" "../AbiEncode"
 
begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        uint256 w = 42;
        uint256 x = 43;
        uint256 y = 44;
        uint256 z = 45;
        return abi.encode(w, x, y, z);
    }
}
*)

(* hex output *) 

(*

0x000000000000000000000000000000000000000000000000000000000000002a000000000000000000000000000000000000000000000000000000000000002b000000000000000000000000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000000000000000000002d
*)

definition test_in :: "8 word list" where
"test_in = hex_splits
''000000000000000000000000000000000000000000000000000000000000002a000000000000000000000000000000000000000000000000000000000000002b000000000000000000000000000000000000000000000000000000000000002c000000000000000000000000000000000000000000000000000000000000002d''"

definition test_schema :: abi_type where
"test_schema = Ttuple [Tuint 256, Tuint 256, Tuint 256, Tuint 256]"

definition test_out :: abi_value where
"test_out = Vtuple [Tuint 256, Tuint 256, Tuint 256, Tuint 256]
            (map (Vuint 256) [42, 43, 44, 45])"

value "test_out"

value "decode test_schema test_in"

value "decode test_schema test_in = Ok test_out"
value "encode test_out = Ok test_in"

end
