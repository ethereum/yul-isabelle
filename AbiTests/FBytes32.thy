theory FBytes32 imports "../AbiTypes" "../Hex"

begin

(* solidity *)

(*
contract C {
    function getEncoding() external returns (bytes memory) {
                    bytes32 x = hex"DEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF";
        return abi.encode(x);
    }
}
*)

(* hex output *)
(*
0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef
*)
end