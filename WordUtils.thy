theory WordUtils imports 
"HOL-Library.Word"
"Word_Lib/Rsplit"

begin

(* convert a byte array to an array of EVM words *)

fun bytesToEvmWords :: "8 word list \<Rightarrow> 256 word list" where
"bytesToEvmWords [] = []"
| "bytesToEvmWords bs =
  (if (length bs > 32) then
    word_rcat (take 32 bs) # bytesToEvmWords (drop 32 bs)
   else [word_rcat (take 32 bs)])"
  

(* convert an array of EVM words to a byte array *)
fun evmWordsToBytes :: "256 word list \<Rightarrow> 8 word list" where
"evmWordsToBytes ew = 
  List.concat (List.map word_rsplit ew)"

end