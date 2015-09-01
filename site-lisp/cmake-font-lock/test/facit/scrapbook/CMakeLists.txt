#
# This file contains snippets of CMakeLists.txt files containing
# uncommon constructs.
#

add_compiler_rt_static_runtime(clang_rt.asan-${arch} ${arch}
      SOURCES ${ASAN_SOURCES}
              $<TARGET_OBJECTS:RTInterception.${arch}>
              $<TARGET_OBJECTS:RTSanitizerCommon.${arch}>
      CFLAGS ${ASAN_CFLAGS}
      DEFS ${ASAN_COMMON_DEFINITIONS})

source_group(alpha FILES test.c)
source_group(alpha\\beta FILES test.c)

# Target names may contain "."
add_library(foo     allan.c)
add_library(foo.ENU allan.c)
set_target_properties(foo.ENU PROPERTIES prop value prop2 value2)
set_target_properties(foo     PROPERTIES prop value prop2 value2)

foo({allan})
foo(${allan})
foo($sune{allan})

foo($sune{${one}})
foo($sune{nested${one}nested})
foo($sune{$sune{one}})
foo($sune{nested$sune{one}nested})

set(ENV{allan} test $ENV{foo} $nonstandard{allan})

set (ENV{LD_LIBRARY_PATH} ${LD_LIBRARY_PATH}:$ENV{LD_LIBRARY_PATH})
