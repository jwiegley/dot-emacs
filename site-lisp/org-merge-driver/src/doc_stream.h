/**
 * @file doc_stream.h
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

#ifndef DOC_STREAM_H
#define DOC_STREAM_H

#include <stdio.h>

/**
 * @todo write safe wrapper macros.
 */

#define doc_stream FILE
#define doc_stream_open fopen
#define doc_stream_close fclose
#define doc_stream_putc putc
#define doc_stream_puts fputs
#define doc_stream_fwrite fwrite

#endif
