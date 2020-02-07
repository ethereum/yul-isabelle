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

end