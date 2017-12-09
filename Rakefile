require 'rake'

def remove_compiled_file(file)
  begin
    puts file + "c"
    FileUtils.rm(file + "c")
  rescue
  end
end

def execute(command)
  puts command
  system command
end

def compile_elisp(file, load_paths = [])
  execute "emacs -batch -Q -L . -L #{load_paths.join(" -L ")} -f batch-byte-compile #{file}"
end

task :compile do
  compile_elisp 'smart-newline.el'
end

task :test, :file
task :test  do |task, args|
  test_files = unless args.file
                 Dir["test/*.el"].join(" -l ")
               else
                 args.file
               end
  execute "emacs -batch -Q -L . -L test -l vendor/cursor-test.el -l test/test-helper.el -l #{test_files} -f ert-run-tests-batch-and-exit"
end
