
if(${CMAKE_SOURCE_DIR} STREQUAL ${CMAKE_BINARY_DIR})
	if(NOT DEFINED WITH_IN_SOURCE_BUILD)
		message(FATAL_ERROR
			"CMake generation for OpenCollada is not allowed within the source directory!"
			"\n Remove the CMakeCache.txt file and try again from another folder, e.g.:"
			"\n "
			"\n rm CMakeCache.txt"
			"\n cd .."
			"\n mkdir cmake-make"
			"\n cd cmake-make"
			"\n cmake ../opencollada"
			"\n "
			"\n Alternately define WITH_IN_SOURCE_BUILD to force this option (not recommended!)"
		)
	endif()
endif()

cmake_minimum_required(VERSION 2.6)


#-----------------------------------------------------------------------------
# Set policy.

# see "cmake --help-policy CMP0003"
# So library linking is more sane
cmake_policy(SET CMP0003 NEW)

# So defines are automatically quoted
cmake_policy(SET CMP0005 NEW)

# So syntax problems are errors
cmake_policy(SET CMP0010 NEW)

# Input directories must have CMakeLists.txt
cmake_policy(SET CMP0014 NEW)

# avoid having empty buildtype
set(CMAKE_BUILD_TYPE_INIT "Release")

list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/Externals/cmake-modules")
set(CMAKE_CONFIGURATION_TYPES "Debug;Release" CACHE STRING "Only do Release and Debug" FORCE )
mark_as_advanced(CMAKE_CONFIGURATION_TYPES)


#-----------------------------------------------------------------------------
# Macro's

macro(opencollada_add_lib
	name
	sources
	target_libs
	)

	link_directories(${LIBRARY_OUTPUT_PATH})

	if (USE_STATIC)
		add_library(${name}_static STATIC ${sources})
		set_target_properties(${name}_static PROPERTIES OUTPUT_NAME ${name})
		target_link_libraries(${name}_static ${target_libs})
		set(CMAKE_REQUIRED_LIBRARIES "${name}_static;${CMAKE_REQUIRED_LIBRARIES}" PARENT_SCOPE)

		install(
			TARGETS ${name}_static
			ARCHIVE DESTINATION ${OPENCOLLADA_INST_LIBRARY}
		)
	endif ()

	if (USE_SHARED)
		if (NOT UNIX)
			message(${name} " WARNING: Shared library support implemented for UNIX-like OS only")
		endif ()
		add_library(${name}_shared SHARED ${sources})
		set_target_properties(${name}_shared PROPERTIES OUTPUT_NAME ${name})
		target_link_libraries(${name}_shared ${target_libs})
		set(CMAKE_REQUIRED_LIBRARIES "${name}_shared;${CMAKE_REQUIRED_LIBRARIES}"  PARENT_SCOPE)

		install(
			TARGETS ${name}_shared
			LIBRARY DESTINATION ${OPENCOLLADA_INST_LIBRARY}
		)
	endif ()
endmacro()


# ---------------------
# copied from blender's
# build_files/cmake/macros.cmake

macro(ADD_CHECK_C_COMPILER_FLAG
	_CFLAGS
	_CACHE_VAR
	_FLAG)

	include(CheckCCompilerFlag)

	CHECK_C_COMPILER_FLAG("${_FLAG}" "${_CACHE_VAR}")
	if(${_CACHE_VAR})
		# message(STATUS "Using CFLAG: ${_FLAG}")
		set(${_CFLAGS} "${${_CFLAGS}} ${_FLAG}")
	else()
		message(STATUS "Unsupported CFLAG: ${_FLAG}")
	endif()
endmacro()

macro(ADD_CHECK_CXX_COMPILER_FLAG
	_CXXFLAGS
	_CACHE_VAR
	_FLAG)

	include(CheckCXXCompilerFlag)

	CHECK_CXX_COMPILER_FLAG("${_FLAG}" "${_CACHE_VAR}")
	if(${_CACHE_VAR})
		# message(STATUS "Using CXXFLAG: ${_FLAG}")
		set(${_CXXFLAGS} "${${_CXXFLAGS}} ${_FLAG}")
	else()
		message(STATUS "Unsupported CXXFLAG: ${_FLAG}")
	endif()
endmacro()
# end copy
# --------

#-----------------------------------------------------------------------------
# Initialize project.

project(OPENCOLLADA)  # must be after setting cmake_configuration_types

# defines where specific parts of BRICS_MM are stored or created
set(LIBRARY_OUTPUT_PATH            ${CMAKE_HOME_DIRECTORY}/lib)  # static libraries
set(EXECUTABLE_OUTPUT_PATH         ${CMAKE_HOME_DIRECTORY}/bin)  # executables
set(EXTERNAL_LIBRARIES        	   ${CMAKE_HOME_DIRECTORY}/Externals)  # external libraries
set(CMAKE_MODULE_PATH "${EXTERNAL_LIBRARIES}/cmake-modules")


#-----------------------------------------------------------------------------
# Compiler warnings.

set(C_WARNINGS   "")
set(CXX_WARNINGS "")

if (CMAKE_COMPILER_IS_GNUCC)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_ALL -Wall)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_EXTRA -Wextra)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_NO_UNKNOWN_PRAGMAS -Wno-unknown-pragmas)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_NO_SWITCH -Wno-switch)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_NO_UNUSED_PARAMETER -Wno-unused-parameter)
	ADD_CHECK_C_COMPILER_FLAG(C_WARNINGS C_WARN_NO_IGNORED_QUALIFIERS -Wno-ignored-qualifiers)
endif ()
if (CMAKE_COMPILER_IS_GNUCXX)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_ALL -Wall)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_EXTRA -Wextra)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_NO_UNKNOWN_PRAGMAS -Wno-unknown-pragmas)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_NO_SWITCH -Wno-switch)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_NO_REORDER -Wno-reorder)  # could be re-ordered but for now this is just noise.
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_NO_UNUSED_PARAMETER -Wno-unused-parameter)
	ADD_CHECK_CXX_COMPILER_FLAG(CXX_WARNINGS CXX_WARN_NO_IGNORED_QUALIFIERS -Wno-ignored-qualifiers)
endif ()

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${C_WARNINGS}")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${CXX_WARNINGS}")


#-----------------------------------------------------------------------------
# Install vars

set(OPENCOLLADA_INST_INCLUDE ${CMAKE_INSTALL_PREFIX}/include/opencollada)
set(OPENCOLLADA_INST_LIBRARY ${CMAKE_INSTALL_PREFIX}/lib/opencollada)


#-----------------------------------------------------------------------------
# Redirect output files

set(EXECUTABLE_OUTPUT_PATH ${CMAKE_BINARY_DIR}/bin CACHE INTERNAL "" FORCE )
set(LIBRARY_OUTPUT_PATH ${CMAKE_BINARY_DIR}/lib CACHE INTERNAL "" FORCE )


#-----------------------------------------------------------------------------
# Set default config options

option(USE_STATIC "Build static libraries"  ON)
option(USE_SHARED "Build shared libraries"  OFF)
option(USE_LIBXML "Use LibXml2 parser"      ON)
option(USE_EXPAT  "Use expat parser"        OFF)

#adding xml2
if (USE_LIBXML)
	add_definitions(
		-DGENERATEDSAXPARSER_XMLPARSER_LIBXML
		-DXMLPARSER_LIBXML
	)
	find_package(LibXml2)
	if (LIBXML2_FOUND)
		message(STATUS "SUCCESSFUL: LibXml2 found")
	else ()  # if xml2 not found building its local copy from ./Externals
		if (WIN32)
			message("WARNING: Native LibXml2 not found, taking LibXml from ./Externals")
			add_subdirectory(${EXTERNAL_LIBRARIES}/LibXML)
			set(LIBXML2_INCLUDE_DIR
				${libxml_include_dirs}
			)
			set(LIBXML2_LIBRARIES xml)
		else ()
			message("ERROR: LibXml2 not found, please install xml2 library (for Debian libxml2-dev)")
		endif ()
	endif ()
endif ()

if (USE_EXPAT)
	add_definitions(-DGENERATEDSAXPARSER_XMLPARSER_EXPAT)
	message("FATAL: EXPAT support not implemented")
	# TODO:: use externals
endif ()

#adding PCRE
find_package(PCRE)
if (PCRE_FOUND)
	message(STATUS "SUCCESSFUL: PCRE found")
else ()  # if pcre not found building its local copy from ./Externals
	if (WIN32)
		message("WARNING: Native PCRE not found, taking PCRE from ./Externals")
		add_definitions(-DPCRE_STATIC)
		add_subdirectory(${EXTERNAL_LIBRARIES}/pcre)
		set(PCRE_INCLUDE_DIR ${libpcre_include_dirs})
		set(PCRE_LIBRARIES pcre)
	else ()
		message("ERROR: PCRE not found, please install pcre library")
	endif ()
endif ()

# building required libs
add_subdirectory(common/libftoa)
add_subdirectory(common/libBuffer)
add_subdirectory(${EXTERNAL_LIBRARIES}/UTF)
add_subdirectory(${EXTERNAL_LIBRARIES}/MathMLSolver)

# building OpenCOLLADA libs
add_subdirectory(COLLADABaseUtils)
add_subdirectory(COLLADAFramework)
add_subdirectory(GeneratedSaxParser)
add_subdirectory(COLLADASaxFrameworkLoader)
add_subdirectory(COLLADAStreamWriter)

# building COLLADAValidator app
add_subdirectory(COLLADAValidator)
