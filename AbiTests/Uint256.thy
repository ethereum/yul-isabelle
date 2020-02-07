theory Uint256 imports "../AbiTypes" "../Hex"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        uint256 x = 0xDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEFDEADBEEF;
        return abi.encode(x);
    }
}
*)

(* hex output *)

(*
0xdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeefdeadbeef"
*)

end