// -*- C++ -*-
//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef _LIBCPP___SH_SH_USING_H
#define _LIBCPP___SH_SH_USING_H

#include <meta>
#include <sh>

using std::format;
using std::print;
using std::println;
using std::ranges::views::drop;
using std::ranges::views::filter;
using std::ranges::views::grep;
using std::ranges::views::show;
using std::ranges::views::sort_by;
using std::ranges::views::take;
using std::ranges::views::transform;
using std::sh::append_file;
using std::sh::cat;
using std::sh::cd;
using std::sh::cp;
using std::sh::dir_entry;
using std::sh::env;
using std::sh::exec;
using std::sh::exists;
using std::sh::file_entry;
using std::sh::file_exists;
using std::sh::fs_entry;
using std::sh::glob;
using std::sh::head;
using std::sh::is_dir;
using std::sh::line_entry;
using std::sh::lines;
using std::sh::lines_view;
using std::sh::link_entry;
using std::sh::ls;
using std::sh::ls_opts;
using std::sh::ls_view;
using std::sh::mkdir_p;
using std::sh::mv;
using std::sh::operator_unresolved;
using std::sh::pwd;
using std::sh::read_file;
using std::sh::read_lines;
using std::sh::rm;
using std::sh::run;
using std::sh::setenv;
using std::sh::sh_result;
using std::sh::sym;
using std::sh::tail;
using std::sh::touch;
using std::sh::write_file;
using std::sh::wc_l;
using std::sh::__cppsh_type_line;
using std::placeholders::_;
using std::placeholders::_1;
using std::placeholders::_2;
using std::placeholders::_3;
using std::placeholders::_4;
using std::placeholders::_5;

#endif // _LIBCPP___SH_SH_USING_H
