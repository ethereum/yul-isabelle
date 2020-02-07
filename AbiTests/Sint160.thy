theory Sint160 imports "../AbiTypes" "../Hex"

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


end