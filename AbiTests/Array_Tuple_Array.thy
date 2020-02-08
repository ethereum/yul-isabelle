theory Array_Tuple_Array imports "../Hex" "../AbiTypes" "../AbiTypesSyntax"
begin

(* example of a dynamic structure containing a static structure which in turn contains a dynamic structure *)

(* solidity *)

(*


 pragma experimental ABIEncoderV2;

 contract C {
     
    struct uintas {
    uint256 [] i1;
    uint256 [] i2;
    }
    
    uint256 [] i11;
    uint256 [] i12;
    
    uint256 [] i21;
    uint256 [] i22;

    uint256 [] i31;
    uint256 [] i32;
    
    uintas [] x;   
    
    function getEncoding() external returns (bytes memory) {
        
        i11.push(uint256(1));
        i11.push(uint256(2));
        i11.push(uint256(3));
        i11.push(uint256(4));
        
        i12.push(uint256(10));
        
        i21.push(uint256(40));
        i21.push(uint256(41));
        
        // i22 empty
        
        i31.push(uint256(60));
        i31.push(uint256(61));
        i31.push(uint256(62));
        
        i32.push(uint256(100));
        i32.push(uint256(101));
        

        x.push(uintas(i11, i12));
        x.push(uintas(i21, i22));
        x.push(uintas(i31, i32));
        
        return abi.encode(x);
    }
}

*)

(* hex output (raw) *)

(*

{
	"0": "bytes: 0x00000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000002800000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003d000000000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000640000000000000000000000000000000000000000000000000000000000000065"
}

*)

(* hex output (trimmed) *)

(*
0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000002800000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003d000000000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000640000000000000000000000000000000000000000000000000000000000000065
*)

definition test_in :: "8 word list" where
"test_in = hex_splits ''0000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000006000000000000000000000000000000000000000000000000000000000000001800000000000000000000000000000000000000000000000000000000000000240000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000e0000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000300000000000000000000000000000000000000000000000000000000000000040000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000000000000000000000000000000000000a000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000a00000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000002800000000000000000000000000000000000000000000000000000000000000290000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000c00000000000000000000000000000000000000000000000000000000000000003000000000000000000000000000000000000000000000000000000000000003c000000000000000000000000000000000000000000000000000000000000003d000000000000000000000000000000000000000000000000000000000000003e000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000640000000000000000000000000000000000000000000000000000000000000065''"


definition test_schema :: abi_type where
"test_schema = ABI_TYPE\<guillemotleft>(Tuint256 [], Tuint256 []) []\<guillemotright>"

definition test_out :: "abi_value" where
"test_out = Varray (ABI_TYPE\<guillemotleft>(Tuint256 [], Tuint256 [])\<guillemotright>)
            (map (Vtuple [ABI_TYPE\<guillemotleft>Tuint256 []\<guillemotright>, ABI_TYPE\<guillemotleft>Tuint256 []\<guillemotright>])
                      [[Varray (Tuint 256) (map (Vuint 256) [1, 2, 3, 4]),
                        Varray (Tuint 256) (map (Vuint 256) [10])],
                       [Varray (Tuint 256) (map (Vuint 256) [40, 41]),
                        Varray (Tuint 256) []],
                       [Varray (Tuint 256) (map (Vuint 256) [60, 61, 62]),
                        Varray (Tuint 256) (map (Vuint 256) [100, 101])]])"

end