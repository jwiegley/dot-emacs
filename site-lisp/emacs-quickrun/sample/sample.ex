defmodule Hello do
 def world do
  Erlang.io.format("Hello quickrun.el.~n", [])
 end
end
Hello.world
