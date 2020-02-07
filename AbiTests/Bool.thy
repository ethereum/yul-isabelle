theory Bool imports "../AbiTypes" "../Hex"

begin
(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        bool x = true;
        return abi.encode(x);
    }
}
*)

(* hex output *)
(*
bytes: 0x0000000000000000000000000000000000000000000000000000000000000001
*)
end
