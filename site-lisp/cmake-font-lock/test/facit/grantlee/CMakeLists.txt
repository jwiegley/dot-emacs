
project(Grantlee)

cmake_minimum_required(VERSION 2.6.4)

# Workaround for http://public.kitware.com/Bug/view.php?id=12301
if (MINGW)
  if(NOT CMAKE_BUILD_TYPE)
    set(CMAKE_BUILD_TYPE Debug CACHE STRING "Choose the type of build,
  options are: None(CMAKE_CXX_FLAGS or CMAKE_C_FLAGS used) Debug Release
  RelWithDebInfo MinSizeRel Coverage." FORCE)
  endif()
endif()

option( BUILD_CORE "Build the Grantlee template library. Deprecated. Use BUILD_TEMPLATES instead" TRUE )
option( BUILD_GUI "Build the Grantlee textdocument library. Deprecated. Use BUILD_TEXTDOCUMENT instead" TRUE )
option( BUILD_TEMPLATES "Build the Grantlee template library" TRUE )
option( BUILD_TEXTDOCUMENT "Build the Grantlee textdocument library" TRUE )
option( BUILD_MAIN_PLUGINS "Build the Grantlee Templates plugins" TRUE )
option( BUILD_I18N_PLUGIN "Build the Grantlee Templates i18n plugin" TRUE )
option( BUILD_SCRIPT_PLUGIN "Build the Grantlee Templates scriptable tags plugin" TRUE )
option( BUILD_TESTS "Build the Grantlee tests" TRUE )

if (BUILD_TESTS)
  enable_testing()
endif()

set(Grantlee_MODULE_DIR ${Grantlee_SOURCE_DIR}/cmake/modules)
set(CMAKE_MODULE_PATH ${Grantlee_MODULE_DIR})

include(GrantleeGenerateExportHeader)

# create coverage build type
set(CMAKE_CONFIGURATION_TYPES ${CMAKE_CONFIGURATION_TYPES} Coverage )
if (${CMAKE_VERSION} VERSION_GREATER 2.8.2)
  set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS
                "Debug" "Release" "MinSizeRel" "RelWithDebInfo" "Coverage" "TestCocoon")
endif()

set(CMAKE_CXX_FLAGS_COVERAGE "${CMAKE_CXX_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
set(CMAKE_C_FLAGS_COVERAGE "${CMAKE_C_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
set(CMAKE_EXE_LINKER_FLAGS_COVERAGE "${CMAKE_EXE_LINKER_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
set(CMAKE_SHARED_LINKER_FLAGS_COVERAGE "${CMAKE_SHARED_LINKER_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")
set(CMAKE_STATIC_LINKER_FLAGS_COVERAGE "${CMAKE_STATIC_LINKER_FLAGS_RELEASE} -fprofile-arcs -ftest-coverage")

set(TESTCOCOON_ARGS "--cs-on --cs-count --cs-include-file-abs-regex=${CMAKE_SOURCE_DIR}/.* --cs-include-file-regex=qrc_* --cs-qt4 --cs-exclude-file-abs-regex=${CMAKE_BINARY_DIR}/.*")
set(CMAKE_CXX_FLAGS_TESTCOCOON "${CMAKE_CXX_FLAGS_RELEASE} ${TESTCOCOON_ARGS}")
set(CMAKE_C_FLAGS_TESTCOCOON "${CMAKE_C_FLAGS_RELEASE} ${TESTCOCOON_ARGS}")
set(CMAKE_EXE_LINKER_FLAGS_TESTCOCOON "${CMAKE_EXE_LINKER_FLAGS_RELEASE} ${TESTCOCOON_ARGS}")
set(CMAKE_SHARED_LINKER_FLAGS_TESTCOCOON "${CMAKE_SHARED_LINKER_FLAGS_RELEASE} ${TESTCOCOON_ARGS}")
set(CMAKE_STATIC_LINKER_FLAGS_TESTCOCOON "${CMAKE_STATIC_LINKER_FLAGS_RELEASE} ${TESTCOCOON_ARGS}")

if (CMAKE_COMPILER_IS_GNUCXX)
  set (CMAKE_C_FLAGS   "${CMAKE_C_FLAGS} -Wno-long-long -std=iso9899:1990 -Wundef -Wcast-align -Werror-implicit-function-declaration -Wchar-subscripts -Wall -W -Wpointer-arith -Wwrite-strings -Wformat-security -Wmissing-format-attribute -fno-common")
  set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wnon-virtual-dtor -Wno-long-long -ansi -Wundef -Wcast-align -Wchar-subscripts -Wall -W -Wpointer-arith -Wformat-security -fno-check-new -fno-common ")

  if (CMAKE_BUILD_TYPE MATCHES TestCocoon)
    # Needed on 64 bit
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} --cs-libgen=-fPIC")
  else()
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -pedantic-errors")
  endif()

  if (NOT APPLE)
    set ( CMAKE_SHARED_LINKER_FLAGS "-Wl,--fatal-warnings -Wl,--no-undefined ${CMAKE_SHARED_LINKER_FLAGS}")
    set ( CMAKE_MODULE_LINKER_FLAGS "-Wl,--fatal-warnings -Wl,--no-undefined ${CMAKE_MODULE_LINKER_FLAGS}")
  endif ()

  if (NOT MINGW)
    grantlee_enable_gcc_hidden_visibility()
  endif ()
endif()

# Tell FindQt4.cmake to point the QT_QTFOO_LIBRARY targets at the imported targets
# for the Qt libraries, so we get full handling of release and debug versions of the
# Qt libs and are flexible regarding the install location of Qt under Windows
set(QT_USE_IMPORTED_TARGETS TRUE)

add_definitions(-DQT_NO_CAST_TO_ASCII)
add_definitions(-DQT_NO_CAST_FROM_ASCII)
add_definitions(-DQT_STRICT_ITERATORS)
add_definitions(-DQT_NO_URL_CAST_FROM_STRING)
add_definitions(-DQT_NO_CAST_FROM_BYTEARRAY)
add_definitions(-DQT_NO_KEYWORDS)

# Always include the source and build directories in the include path
# to save doing so manually in every subdirectory.
SET( CMAKE_INCLUDE_CURRENT_DIR ON )

set(Grantlee_VERSION_MAJOR 0)
set(Grantlee_VERSION_MINOR 3)
set(Grantlee_VERSION_PATCH 0)
set(Grantlee_MIN_PLUGIN_VERSION 1)

set(Grantlee_MAJOR_MINOR_VERSION_STRING "${Grantlee_VERSION_MAJOR}.${Grantlee_VERSION_MINOR}" )
set(Grantlee_VERSION_STRING "${Grantlee_VERSION_MAJOR}.${Grantlee_VERSION_MINOR}.${Grantlee_VERSION_PATCH}" )

set (LIB_SUFFIX "" CACHE STRING "Define suffix of library directory name (eg. '64')")

set( LIB_INSTALL_DIR lib${LIB_SUFFIX} )
set( PLUGIN_INSTALL_DIR lib${LIB_SUFFIX}/grantlee/${Grantlee_MAJOR_MINOR_VERSION_STRING} )
set( BIN_INSTALL_DIR bin )
set( INCLUDE_INSTALL_DIR include )
set( DATA_INSTALL_DIR share/apps )

# set up RPATH/install_name_dir
set( CMAKE_INSTALL_NAME_DIR ${CMAKE_INSTALL_PREFIX}/${LIB_INSTALL_DIR})
set( CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)

set(Grantlee_USE_FILE "${Grantlee_MODULE_DIR}/GrantleeUse.cmake")

if (BUILD_CORE AND BUILD_TEMPLATES)
  add_subdirectory(templates)
endif()

if (BUILD_GUI AND BUILD_TEXTDOCUMENT)
  add_subdirectory(textdocument)
endif()

set(CMAKECONFIG_INSTALL_DIR "${LIB_INSTALL_DIR}/cmake/grantlee" )

file(RELATIVE_PATH relInstallDir ${CMAKE_INSTALL_PREFIX}/${CMAKECONFIG_INSTALL_DIR} ${CMAKE_INSTALL_PREFIX} )

configure_file(
  "${Grantlee_MODULE_DIR}/GrantleeConfig.cmake.in"
  "${Grantlee_BINARY_DIR}/GrantleeConfig.cmake"
  @ONLY
)

configure_file(
  "${Grantlee_MODULE_DIR}/GrantleeConfigVersion.cmake.in"
  "${Grantlee_BINARY_DIR}/GrantleeConfigVersion.cmake"
  @ONLY
)

install(FILES
  "${Grantlee_BINARY_DIR}/GrantleeConfig.cmake"
  "${Grantlee_BINARY_DIR}/GrantleeConfigVersion.cmake"
  DESTINATION "${CMAKECONFIG_INSTALL_DIR}"
  COMPONENT Common
)

install(FILES
  "${Grantlee_MODULE_DIR}/GrantleeUse.cmake"
  "${Grantlee_MODULE_DIR}/GrantleeParseArguments.cmake"
  DESTINATION "${CMAKECONFIG_INSTALL_DIR}"
  COMPONENT Common
)

install(EXPORT grantlee_targets
  DESTINATION "${CMAKECONFIG_INSTALL_DIR}"
  FILE GrantleeTargets.cmake
  COMPONENT Common
)

# Add support for an uninstall target
configure_file(
  "${Grantlee_MODULE_DIR}/cmake_uninstall.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
  IMMEDIATE @ONLY)

add_custom_target(uninstall
  "${CMAKE_COMMAND}" -P
  "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake")

find_package(Doxygen)
if (DOXYGEN_FOUND AND DOXYGEN_DOT_FOUND)
  message (STATUS "Doxygen and dot found. make docs target is available")
  # Add support for a docs target

  # Available from http://gcc.gnu.org/onlinedocs/libstdc++/latest-doxygen/libstdc++.tag
  set(STLTAGFILE "${CMAKE_SOURCE_DIR}/scripts/libstdc++.tag=http://gcc.gnu.org/onlinedocs/libstdc++/latest-doxygen")
  set(QTTAGFILE "${CMAKE_SOURCE_DIR}/scripts/qttags.tag=http://qt.nokia.com/doc/${QT_VERSION_MAJOR}.${QT_VERSION_MINOR}")

  set(TAGFILES "${QTTAGFILE} ${STLTAGFILE}")
  set(DOCS_OUTPUT_DIRECTORY "@CMAKE_BINARY_DIR@")
  configure_file(
    "${Grantlee_MODULE_DIR}/Doxyfile.in"
    "${CMAKE_CURRENT_BINARY_DIR}/Doxyfile"
    @ONLY)

  # Add support for a Qt assistant docs target
  # qttags.tag is too big to distribute with Grantlee. Get it
  # from http://api.kde.org/kdereview-api/kdereview.tar.gz for example.
  if(EXISTS ${CMAKE_SOURCE_DIR}/scripts/qttags.tag)
    set(DOCS_OUTPUT_DIRECTORY "@CMAKE_BINARY_DIR@/qtdocs")

    # Available from http://steveire.com/libstdc++-longnames.tag
    # Also recommended: http://www.steveire.com/libstdc++-v3.qch
    set(STLTAGFILE "${CMAKE_SOURCE_DIR}/scripts/libstdc++-longnames.tag=qthelp://org.gnu.libstdcxx/libstdc++-v3/")
    set(QTTAGFILE "${CMAKE_SOURCE_DIR}/scripts/qttags.tag=qthelp://com.trolltech.qt/qdoc/")

    set(TAGFILES "${QTTAGFILE} ${STLTAGFILE}")
    set(GENERATE_QHP "yes")

    configure_file(
      "${Grantlee_MODULE_DIR}/Doxyfile.in"
      "${CMAKE_CURRENT_BINARY_DIR}/Doxyfile.qt"
      @ONLY)
  endif()

  set( DOCS_ARGS ${DOXYGEN_EXECUTABLE} "${CMAKE_CURRENT_BINARY_DIR}/Doxyfile" )
  if(EXISTS "${CMAKE_CURRENT_BINARY_DIR}/Doxyfile.qt")
    set(DOCS_ARGS ${DOCS_ARGS} COMMAND ${DOXYGEN_EXECUTABLE} "${CMAKE_CURRENT_BINARY_DIR}/Doxyfile.qt" )
  endif()

  add_custom_target(docs
    ${DOCS_ARGS}
  )
endif()

find_package(LCov)

if(LCOV_FOUND)
  get_property(UNITTESTS GLOBAL PROPERTY TEST_COVERAGE)

  set(coverageDir ${CMAKE_BINARY_DIR})

  foreach(_testpath ${UNITTESTS})
    set(coverage_ARGS ${coverage_ARGS} COMMAND ${LCOV_EXECUTABLE} -z -d ${coverageDir})

    get_filename_component(_test ${_testpath} NAME)

    set(coverage_ARGS ${coverage_ARGS} COMMAND ${_testpath})
    set(coverage_ARGS ${coverage_ARGS} COMMAND ${LCOV_EXECUTABLE} -c -t ${_test} -d ${coverageDir} -o ${CMAKE_BINARY_DIR}/test_${_test}.info)
    set(infoFiles ${infoFiles} -a ${CMAKE_BINARY_DIR}/test_${_test}.info)
  endforeach()

  set(coverage_ARGS ${coverage_ARGS} COMMAND ${LCOV_EXECUTABLE} ${infoFiles} -o test_all.info)

  # For an unknown reason lcov does not work with absolute paths such as ${CMAKE_BINARY_DIR}
  file(RELATIVE_PATH relBinaryDir / ${CMAKE_BINARY_DIR})
  file(RELATIVE_PATH relQtDir / ${QT_HEADERS_DIR})

  set(coverage_ARGS ${coverage_ARGS} COMMAND ${LCOV_EXECUTABLE} -r test_all.info *${relBinaryDir}*
                                                                -r test_all.info *pluginpointer*
                                                                -r test_all.info *usr/include*
                                                                -r test_all.info *${relQtDir}*
                                                                -o test_all.info
  )

  set(coverage_ARGS ${coverage_ARGS} COMMAND ${CMAKE_COMMAND} -E remove_directory coverage)
  set(coverage_ARGS ${coverage_ARGS} COMMAND ${GENHTML_EXECUTABLE} -o coverage/ -s --demangle-cpp -f test_all.info)

  add_custom_target(coverage
    ${coverage_ARGS}
  )
endif()

if (CMAKE_BUILD_TYPE MATCHES TestCocoon)

  get_property(UNITTESTS GLOBAL PROPERTY TEST_COVERAGE)

  set(coverageDir ${CMAKE_BINARY_DIR})

  set(testcocoon_ARGS)

  foreach(_testpath ${UNITTESTS})
    set(testcocoon_ARGS ${testcocoon_ARGS} COMMAND "${_testpath}")
  endforeach()

  find_program(TESTCOCOON_CMMERGE_EXECUTABLE cmmerge)
  find_program(TESTCOCOON_CMCSEXEIMPORT_EXECUTABLE cmcsexeimport)

  set(testcocoon_ARGS ${testcocoon_ARGS} COMMAND ${TESTCOCOON_CMMERGE_EXECUTABLE} -o unittests.csmes)
  foreach(_testpath ${UNITTESTS})
    set(testcocoon_ARGS ${testcocoon_ARGS} ${_testpath}.csmes)
  endforeach()
  set(_plugins "grantlee_defaultfilters" "grantlee_defaulttags" "grantlee_i18ntags" "grantlee_loadertags")
  foreach(_plugin ${_plugins})
    set(testcocoon_ARGS ${testcocoon_ARGS} "${coverageDir}/grantlee/0.2/${_plugin}.so.csmes")
  endforeach()
  set(testcocoon_ARGS ${testcocoon_ARGS} "${coverageDir}/templates/lib/libgrantlee_core.so.csmes")

  set(testcocoon_ARGS ${testcocoon_ARGS}
    COMMAND ${TESTCOCOON_CMCSEXEIMPORT_EXECUTABLE}
    -m unittests.csmes -t "\"--unnamed--\"" -p
    merge -e "${coverageDir}/coverage.csexe"
  )

  set(testcocoon_ARGS ${testcocoon_ARGS}
    COMMAND ${TESTCOCOON_CMMERGE_EXECUTABLE} -o "${coverageDir}/libgrantlee_core.so.csmes"
    -i "${coverageDir}/templates/lib/libgrantlee_core.so.csmes" "${coverageDir}/unittests.csmes"
  )

  set(testcocoon_ARGS ${testcocoon_ARGS}
    COMMAND ${TESTCOCOON_CMMERGE_EXECUTABLE} -o "${coverageDir}/libgrantlee_gui.so.csmes"
    -i "${coverageDir}/textdocument/lib/libgrantlee_gui.so.csmes" "${coverageDir}/unittests.csmes"
  )

  foreach(_plugin ${_plugins})
    set(testcocoon_ARGS ${testcocoon_ARGS}
      COMMAND ${TESTCOCOON_CMMERGE_EXECUTABLE} -o "${coverageDir}/${_plugin}.so.csmes"
      -i "${coverageDir}/grantlee/0.2/${_plugin}.so.csmes" "${coverageDir}/unittests.csmes"
    )
  endforeach()

  find_program(TESTCOCOON_CMREPORT_EXECUTABLE cmreport)
  set(_csmes_files ${_plugins} "libgrantlee_gui" "libgrantlee_core")
  foreach(_csmes_file ${_csmes_files})
    set(testcocoon_ARGS ${testcocoon_ARGS}
      COMMAND echo -n \"${_csmes_file}\" COMMAND ${TESTCOCOON_CMREPORT_EXECUTABLE} -s '.*' -m "${_csmes_file}.so.csmes"
    )
  endforeach()

  add_custom_target(testcocoon
    ${testcocoon_ARGS}
  )
endif()

find_package(Cccc)
if (CCCC_FOUND)
  get_property(CCCC_FILES GLOBAL PROPERTY SOURCE_LIST)

  set( cccc_ARGS ${CCCC_EXECUTABLE} ${CCCC_FILES} --outdir=${CMAKE_BINARY_DIR}/cccc --html_outfile=${CMAKE_BINARY_DIR}/cccc/index.html)

  add_custom_target(cccc
    ${cccc_ARGS}
  )
endif()

# http://www.vtk.org/Wiki/CMake:Component_Install_With_CPack
set(CPACK_PACKAGE_NAME "grantlee")
set(CPACK_PACKAGE_VERSION_MAJOR ${Grantlee_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${Grantlee_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${Grantlee_VERSION_PATCH})
set(CPACK_PACKAGE_CONTACT "Stephen Kelly <steveire@gmail.com>")
set(CPACK_PACKAGE_DESCRIPTION_SUMMARY "A set of frameworks for use with Qt")
set(CPACK_GENERATOR "TGZ" )
set(CPACK_RESOURCE_FILE_README "${CMAKE_SOURCE_DIR}/README")
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_SOURCE_DIR}/COPYING.LIB")

set(CPACK_COMPONENT_COMMON_DISPLAY_NAME "Grantlee Common files")
set(CPACK_COMPONENT_TEMPLATES_DISPLAY_NAME "Grantlee String Templates")
set(CPACK_COMPONENT_TEXTDOCUMENT_DISPLAY_NAME "Grantlee TextDocument framework")

set(CPACK_COMPONENT_COMMON_DESCRIPTION
  "Files needed by all Grantlee frameworks")
set(CPACK_COMPONENT_TEMPLATES_DESCRIPTION
  "A string template system for Qt based on Django syntax")
set(CPACK_COMPONENT_TEXTDOCUMENT_DESCRIPTION
  "A framework for QTextDocument related tasks")

set(CPACK_COMPONENT_TEMPLATES_DEPENDS Common)
set(CPACK_COMPONENT_TEXTDOCUMENT_DEPENDS Common)
set(CPACK_COMPONENT_COMMON_REQUIRED ON)

set(CPACK_ARCHIVE_COMPONENT_INSTALL ON)

if (WIN32)
  set(CPACK_NSIS_MODIFY_PATH ON)
  set(CPACK_GENERATOR ${CPACK_GENERATOR} "NSIS" )
endif()

include(CPack)
