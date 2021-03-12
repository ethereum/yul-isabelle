require 'json'

lllc_file = '/mnt/c/Users/yorix/winhome/Code/solidity/build/lllc/lllc'

if ARGV.length < 1 then
  abort("Requires an argument (JSON file to translate)")
end

name_j = ARGV[0]
name_t = name_j.gsub ".json", ".thy"
name_l = name_j.gsub ".json", ".lll"
name_b = name_j.gsub ".json", ".out"

f_json = File.open(name_j, "r")
obj = JSON.load f_json
prog = obj.keys[0]
contract = obj[prog]["pre"].keys[0]

lll_code = obj[prog]["pre"][contract]["code"]

File.open(name_l, "w") { |f|
  f.write lll_code
}

system(lllc_file, name_l, "-x", :out => [name_b, "w"])

f_b = File.open(name_b, "r")

bin_code = f_b.read


f_thy = File.open(name_t, "w")

=begin

env:
- currentCoinbase, 
- currentDifficulty
- currentGasLimit
- currentNumber
- currentTimestamp
- previousHash

exec:
-address, caller, data, gas, gasPrice, origin, value

pre:
- account (the hash)
  - balance
  - code
  - nonce
  - storage

expect: (this is the key part)
- account (the hash)
  - storage
    - mapping from keys to values
      (special case "0x => 0")

storage seems to be the only expect...

=end


# File.open(name_j, "r") do |f_json|
#   obj = JSON.load f_json

#   # puts obj
  
#   File.open(name_t, "w") do |f_thy|
    
#   end
# end

