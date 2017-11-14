/**
 * @file debug.h
 * #define DEBUG_FILE "debug.h"
 */

/*
 * This program is free software: you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either vers* ion 3 of
 * the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful, but
 * WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see
 * <http://www.gnu.org/licenses/>.
 */

#ifndef DEBUG_H
#define DEBUG_H

/* Enable debug globally */
#ifndef DEBUG
#define DEBUG
#endif /* DEBUG */

#define DEFAULT_PRINTLEVEL   0
#define MAIN_PRINTLEVEL      DEFAULT_PRINTLEVEL
#define MERGE_PRINTLEVEL     DEFAULT_PRINTLEVEL
#define DOC_PRINTLEVEL       DEFAULT_PRINTLEVEL
#define LEXER_PRINTLEVEL     DEFAULT_PRINTLEVEL
#define PARSER_PRINTLEVEL    DEFAULT_PRINTLEVEL
#define DOC_ELT_PRINTLEVEL   DEFAULT_PRINTLEVEL
#define ORG_HEADING_PRINTLEVEL DEFAULT_PRINTLEVEL
#define LISTMERGE_PRINTLEVEL DEFAULT_PRINTLEVEL
#define SMERGER_PRINTLEVEL   DEFAULT_PRINTLEVEL

/* DEBUG_ON is used to test if debug is enabled */
#ifdef DEBUG
#define DEBUG_ON 1
#else
#define DEBUG_ON 0
#endif /* DEBUG */

#ifndef DEBUG_OUT
#define DEBUG_OUT stderr
#endif /* DEBUG_OUT */

#ifndef DEBUG_PRINT
#define DEBUG_PRINT 1
#endif /* DEBUG_PRINT */

/* Standard Debug Module  */
#ifndef DEBUG_MODULE
#define DEBUG_MODULE DEFAULT
#endif /* DEBUG_MODULE */

/* lint checkers cannot understand variadic macros */
#ifndef S_SPLINT_S

#define debug_printf(format, ...) \
  debug_msg(DEFAULT, DEFAULT_PRINTLEVEL, format, ##__VA_ARGS__)

#define debug_msg(module, level, format, ...)                   \
  do { if (DEBUG_ON && (level <= module ## _PRINTLEVEL)) {      \
    fprintf (DEBUG_OUT, #module"-%d:%s:%d:%s " format,          \
      level, __FILE__, __LINE__, __func__, ##__VA_ARGS__);	\
    }} while (0)

#else /* ! S_SPLINT_S */
#define comment
#define debug_msg coment ## coment
#undef comment
#endif /* S_SPLINT_S */

#endif /*DEBUG_H */
