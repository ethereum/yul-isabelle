require 'json'

lllc_file = '~/winhome/Code/solidity/build/lllc/lllc'

if ARGV.length < 1 then
  abort("Requires an argument (JSON file to translate)")
end

name_j = ARGV[0]
name_t = name_j.gsub ".json", ".thy"
name_l = name_j.gsub ".json", ".lll"
name_b = name_j.gsup ".json", ".bin"

f_json = File.open(name_j, "r")
obj = JSON.load f_json
prog = obj.keys[0]
contract = obj[prog]["pre"].keys[0]

lll_code = obj[prog]["pre"][contract]["code"]

File.open(name_l, "w") { |f|
  f.write lll_code
}

system(lllc_file, name_l, :out => [name_b, "w"])

f_b = File.open(name_b, "r")

bin_code = f_b.read

f_thy = File.open(name_t, "w")




# File.open(name_j, "r") do |f_json|
#   obj = JSON.load f_json

#   # puts obj
  
#   File.open(name_t, "w") do |f_thy|
    
#   end
# end

