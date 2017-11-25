# CMake highlighting example.
#
# 'cmake-font-lock' is aware of all built-in CMake types, so that
# arguments are correctly colored as variables, keywords etc.
#
# In addition, you can specify the function signature of your own
# functions, like 'my_get_dirs' below.

function(my_get_dirs var)
  set(dirs "")
  foreach(file ${ARGN})
    get_filename_component(abs_file ${file} ABSOLUTE)
    get_filename_component(abs_path ${abs_file} PATH)
    list(FIND dirs ${abs_path} present)
    if(${present} EQUAL -1)
      list(APPEND dirs ${abs_path})
    endif()
  endforeach()
  set(${var} ${dirs} PARENT_SCOPE)
endfunction()

my_get_dirs(DIRS alpha/one.h alpha/two.h beta/three.h)

message(STATUS "Directories:")
foreach(d ${DIRS})
  message(STATUS "  ${d}")
endforeach()
