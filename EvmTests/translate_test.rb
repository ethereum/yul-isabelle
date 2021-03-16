#!/usr/bin/env ruby
require 'json'

# TODO: make this more robust w/r/t directory structure

lllc_file = '/mnt/c/Users/yorix/winhome/Code/solidity/build/lllc/lllc'

if ARGV.length < 1 then
  abort("Requires an argument (JSON file to translate)")
end

name_j = ARGV[0]
name_t = name_j.gsub ".json", ".thy"
name_l = name_j.gsub ".json", ".lll"
name_b = name_j.gsub ".json", ".out"
name_stem1 = name_j.gsub ".json", ""
name_stem = name_stem1.gsub(/^.*\//, "") 

f_json = File.open(name_j, "r")
obj = JSON.load f_json
prog = obj.keys[0]
contract = obj[prog]["pre"].keys[0]

lll_code = obj[prog]["pre"][contract]["code"]

File.open(name_l, "w") { |f|
  f.write lll_code
}

def drop0x(str)
  if(str.nil?)
    ""
  else
    if(str[0..1] == "0x")
      if(str == "0x")
      then
        "0" # sometimes zero is annotated this way in the test cases...
      else
        str[2..]
      end
    else
      str
    end
  end
end

def select_parser(str)
  if(str[0..1] == "0x")
    "parse_hex_str_eint"
  else
    "parse_dec_str_eint"
  end
end

def parse_storage(obj, keys)
  if keys == []
  then
    ""
  else
    out = "(#{select_parser (keys[0])} ''#{drop0x keys[0]}'', #{select_parser (obj[keys[0]])} ''#{drop0x obj[keys[0]]}'')"
    if keys.length > 1 then
      out + " , " + parse_storage(obj, keys[1..])
    else
      out
    end
  end
end

system(lllc_file, name_l, "-x", :out => [name_b, "w"])

f_b = File.open(name_b, "r")

bin_code = f_b.read.gsub("\n", "")

puts bin_code


# TODO: probably need to explicitly call toString in a bunch of places.


template =
%Q`
theory #{name_stem}
imports "../../../Utils/Hex" "../../../EVM/EvmInterpreter" "../../test_utils"
begin
definition prog :: "8 word list" where
"prog = hex_splits ''#{bin_code}''"

definition input_storage where
"input_storage = create_storage [#{parse_storage obj[prog]["pre"][contract]["storage"], obj[prog]["pre"][contract]["storage"].keys}]"

definition output_storage where
"output_storage = [#{parse_storage obj[prog]["expect"][contract]["storage"], obj[prog]["expect"][contract]["storage"].keys}]"

definition  init_Estate :: "estate_ll" where
"init_Estate =
(dummy_estate_ll
(| el_e :=
  (dummy_estate
    (| e_coinbase := #{select_parser (obj[prog]["env"]["currentCoinbase"])} ''#{drop0x obj[prog]["env"]["currentCoinbase"]}''
     , e_difficulty := #{select_parser(obj[prog]["env"]["currentDifficulty"])} ''#{drop0x obj[prog]["env"]["currentDifficulty"]}''
     , e_gaslimit := #{select_parser(obj[prog]["env"]["currentGasLimit"])} ''#{drop0x obj[prog]["env"]["currentGasLimit"]}''
     , e_blocknumber := #{select_parser(obj[prog]["env"]["currentNumber"])} ''#{drop0x obj[prog]["env"]["currentNumber"]}''
     , e_timestamp := #{select_parser(obj[prog]["env"]["currentTimestamp"])} ''#{drop0x obj[prog]["env"]["currentTimestamp"]}''
     , e_blockhash := parse_hex_str_eint ''#{drop0x obj[prog]["env"]["previousHash"]}''

     , e_address := parse_hex_str_eint ''#{drop0x obj[prog]["exec"]["address"]}''
     , e_caller := parse_hex_str_eint ''#{drop0x obj[prog]["exec"]["caller"]}''
     , e_calldata := hex_splits ''#{drop0x obj[prog]["exec"]["data"]}''
     , e_gas := #{select_parser (obj[prog]["exec"]["gas"])} ''#{drop0x obj[prog]["exec"]["gas"]}''
     , e_gasprice := #{select_parser obj[prog]["exec"]["gasPrice"]} ''#{drop0x obj[prog]["exec"]["gasPrice"]}''
     , e_origin := parse_hex_str_eint ''#{drop0x obj[prog]["exec"]["origin"]}''
     , e_callvalue := #{select_parser (obj[prog]["exec"]["gas"])} ''#{drop0x obj[prog]["exec"]["value"]}''
     
     , e_selfbalance := #{select_parser (obj[prog]["pre"][contract]["balance"])} ''#{drop0x obj[prog]["pre"][contract]["balance"]}''
     , e_codedata := hex_splits ''#{bin_code}''
     , e_nonce := #{select_parser (obj[prog]["pre"][contract]["nonce"])} ''#{drop0x obj[prog]["pre"][contract]["nonce"]}''
     , e_storage := input_storage
    |))
|))"

definition final_Estate :: "estate_ll option" where
"final_Estate = evm_exec init_Estate"

definition final_check :: "bool" where
"final_check =
  (case final_Estate of
    None => False
    | Some e => check_storage e output_storage)"

(* value "final_estate" *)

(*
 * Iff this returns true, the test has succeeded.
 *)
value "final_check"
end
`

puts "writing output..."

f_thy = File.open(name_t, "w") { |f|
  f.write template
}
