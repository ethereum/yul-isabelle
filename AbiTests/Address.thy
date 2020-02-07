theory Address imports "../AbiTypes" "../Hex"

begin

(* solidity *)
(*
 contract C {
    function getEncoding() external returns (bytes memory) {
        address x = 0x52908400098527886E0F7030069857D2E4169EE7;
        return abi.encode(x);
    }
}
*)

(*hex output *)

(*

0x00000000000000000000000052908400098527886e0f7030069857d2e4169ee7
*)
end