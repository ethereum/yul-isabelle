theory FBytes16 imports "../AbiTypes" "../Hex"

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
end