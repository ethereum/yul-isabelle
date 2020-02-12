theory NonCanonical_Overlap imports "../Hex" "../AbiDecode" begin

(* testing parsing of non-canoncial representations (i.e. those which
Solidity's encoder cannot output but are still valid ) *)

(* in this case we are testing overlapping tails as well as reordering *)

definition test_schema :: abi_type where
"test_schema = Ttuple [Tarray (Tuint 256), Tarray (Tuint 256), Tarray (Tuint 256)]"

definition test_out :: "abi_value" where
"test_out = Vtuple [Tarray (Tuint 256), Tarray (Tuint 256), Tarray (Tuint 256)]
                   [Varray (Tuint 256) (map (Vuint 256) [23, 1]),
                    Varray (Tuint 256) [Vuint 256 42],
                    Varray (Tuint 256) [Vuint 256 42]]"

(* one non-canonical encoding of this example *)

definition test1_in' :: "256 word list" where
"test1_in' =
  [ 
    \<^cancel>\<open>tail pointer to 2-element array\<close>
    \<^cancel>\<open>bytes 0-32\<close>
    word_of_int 160,

    \<^cancel>\<open>tail pointer to 1-element array\<close>
    \<^cancel>\<open>bytes 32-64\<close>
    word_of_int 96,

    \<^cancel>\<open>tail pointer to 1-element array at same location \<close>
    \<^cancel>\<open>bytes 64-96\<close>
    word_of_int 96,

    \<^cancel>\<open>length of 1-element array\<close>
    \<^cancel>\<open>bytes 96-128\<close>
    word_of_int 1,

    \<^cancel>\<open>element of 1-element array\<close>
    \<^cancel>\<open>bytes 128-160\<close>
    word_of_int 42,

    \<^cancel>\<open>length of 2-element array\<close>
    \<^cancel>\<open>bytes 160-192\<close>
    word_of_int 2,

    \<^cancel>\<open>elements of 2-element array\<close>
    \<^cancel>\<open>bytes 192-256\<close>
    word_of_int 23,
    word_of_int 1]"

definition test1_in :: "8 word list" where
"test1_in = concat (map word_rsplit test1_in')"

value "test1_in"

value "decode test_schema test1_in"
value "decode test_schema test1_in = Ok test_out"



(* another non-canonical encoding, overlapping *)
definition test2_in' :: "256 word list" where
"test2_in' =
  [ 
    \<^cancel>\<open>tail pointer to 2-element array\<close>
    \<^cancel>\<open>bytes 0-32\<close>
    word_of_int 96,

    \<^cancel>\<open>tail pointer to 1-element array\<close>
    \<^cancel>\<open>bytes 32-64\<close>
    word_of_int 160,

    \<^cancel>\<open>tail pointer to 1-element array at same location \<close>
    \<^cancel>\<open>bytes 64-96\<close>
    word_of_int 160,

    \<^cancel>\<open>length of 2-element array\<close>
    \<^cancel>\<open>bytes 96-128\<close>
    word_of_int 2,

    \<^cancel>\<open>first element of 2-element array\<close>
    \<^cancel>\<open>bytes 128-160\<close>
    word_of_int 23,

    \<^cancel>\<open>second element of 2-element array\<close>
    \<^cancel>\<open>doubles as the length of the 1-element array\<close>
    \<^cancel>\<open>bytes 160-192\<close>
    word_of_int 1,

    \<^cancel>\<open>element of 1-element array\<close>
    \<^cancel>\<open>bytes 192-224\<close>
    word_of_int 42]"

 definition test2_in :: "8 word list" where
"test2_in = concat (map word_rsplit test2_in')"

value "decode test_schema test2_in"
value "decode test_schema test2_in = Ok test_out"

end