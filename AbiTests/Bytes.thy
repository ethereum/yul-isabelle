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

(* hex output *)

(*

0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000010deadbeefdeadbeefdeadbeefdeadbeef00000000000000000000000000000000"

*)

end