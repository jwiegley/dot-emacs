require "optparse"

$strip = false
$signatures = false
$cmd = nil

option_parser = OptionParser.new do |opts|
  opts.on("--signatures", "Diff only function signatures") do |v|
    $signatures = true
  end

  opts.on("--strip", "Normalize output") do |v|
    $strip = true
  end

  opts.on("--cmd=NAME", "Only diff command NAME") do |v|
    puts "CMD!!! #{v}"
    $cmd = v
  end
end

option_parser.parse!


cmake1 = ARGV.shift
if ARGV.empty?
  cmake2 = "cmake"
else
  cmake2 = ARGV.shift
end

unless ARGV.empty?
  raise "Unexpected arguments: #{ARGV.join(' ')}"
end

def system_with_output(*args)
  cmd = args.join(" ")
  return `#{cmd}`.split("\n")
end

def command_list(bin)
  list = system_with_output("#{bin} --help-command-list")
  if list[0] =~ /cmake version/
    list.shift
  end
  return list
end

def cmake_command_help(bin, cmd)
  list = system_with_output("#{bin} --help-command #{cmd}")
  if list[0] =~ /cmake version/
    list.shift
  end
  return list
end

def cmake_version(bin)
  list = system_with_output("#{bin} --version")
  return list[0]
end

def write_to_file(name, lines, guess_signatures = false)
  File.open(name, "w") do |fh|
    last_was_empty = false
    seen_double_colon = false
    seen_signature = false
    lines.each do |line|
      if line == "::"
        seen_double_colon = true
        if $strip
          next
        end
      end

      if line =~ /^-+$/
        # Eat the line, and ensure that the next empty line is
        # stripped as well.
        last_was_empty = true
        next
      end

      if last_was_empty && line.empty?
        if $stip
          next
        end
      end

      if !line.empty? && seen_double_colon
        seen_signature = true
        seen_double_colon = false
      end

      if line.empty? && seen_signature
        seen_signature = false
      end


      if (   guess_signatures \
          && last_was_empty   \
          && /         ([a-zA-Z_0-9@]+)\(/.match(line))
        seen_signature = true
      end

      if $strip
        line = line.lstrip
        line = line.squeeze(" ")
        line = line.gsub("``", "")
      end

      line = line.rstrip
      if !$signatures || seen_signature
        fh.puts(line)
      end

      last_was_empty = line.empty?
    end
  end
end

cmd_list1 = command_list(cmake1)
version1 = cmake_version(cmake1)

cmd_list2 = command_list(cmake2)
version2 = cmake_version(cmake2)

only_in_1 = cmd_list1 - cmd_list2
unless only_in_1.empty?
  puts "Only in #{version1}"
  only_in_1.each do |command|
    puts "  #{command}"
  end
end


only_in_2 = cmd_list2 - cmd_list1
unless only_in_2.empty?
  puts "Only in #{version2}"
  only_in_2.each do |command|
    puts "  #{command}"
  end
end

puts "Command in both versions:"

cmd_list1.each do |cmd|
  if cmd_list2.include?(cmd)
    if !$cmd || $cmd == cmd
      puts cmd
      puts "<" * 20
      out1 = cmake_command_help(cmake1, cmd)
      out2 = cmake_command_help(cmake2, cmd)
      write_to_file("out1.txt", out1, true)
      write_to_file("out2.txt", out2, true)
      result = system_with_output("diff out1.txt out2.txt")
      puts result
      puts ">" * 20
    end
  end
end

# DiffCommandHelp.rb ends here
