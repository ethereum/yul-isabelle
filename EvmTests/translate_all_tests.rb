#!/usr/bin/env ruby
# Automation for generating all tests present in the provided Tests directory

translate_script = "./translate_test.rb"

if ARGV.length < 1 then
  abort("Provide a directory to compile tests from")
end

target = ARGV[0]

files = Dir.children "#{target}"

puts "Translating tests from ./#{target}"

for file_rel in files
  if (/\.json$/ =~ file_rel)
  then
    file = "./" + target + "/" + file_rel
    puts "Translating #{file}"
    system("ruby", translate_script, file)
  end
end

