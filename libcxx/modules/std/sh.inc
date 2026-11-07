// -*- C++ -*-
//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

export {
  using ::operator""_KB;
  using ::operator""_MB;
  using ::operator""_GB;
}

export namespace std {
  using std::print;

  namespace ranges {
  namespace views {
    using std::ranges::views::grep;
    using std::ranges::views::sort_by;
    using std::ranges::views::show;
  } // namespace views
  } // namespace ranges

  namespace sh {
    using std::sh::sym;
    using std::sh::operator_unresolved;
    using std::sh::file_entry;
    using std::sh::dir_entry;
    using std::sh::link_entry;
    using std::sh::fs_entry;
    using std::sh::is_dir;
    using std::sh::__cppsh_snapshot;
    using std::sh::__cppsh_staged_step;
    using std::sh::__cppsh_staged_coro;
    using std::sh::__cppsh_staged_state;
    using std::sh::__cppsh_ask;
    using std::sh::__cppsh_variant_get;
    using std::sh::__cppsh_background;
    using std::sh::__cppsh_shell;
    using std::sh::__cppsh_shell_line;
    using std::sh::__cppsh_reap_jobs;
    using std::sh::background;
    using std::sh::bg;
    using std::sh::fg;
    using std::sh::job_entry;
    using std::sh::jobs;
    using std::sh::command;
    using std::sh::pipeline;
    using std::sh::last_status;
    using std::sh::operator|;
    using std::sh::operator>;
    using std::sh::operator>>;
    using std::sh::operator<;
    using std::sh::ls_opts;
    using std::sh::line_entry;
    using std::sh::lines_view;
    using std::sh::ls_view;
    using std::sh::read_file;
    using std::sh::read_lines;
    using std::sh::lines;
    using std::sh::write_file;
    using std::sh::append_file;
    using std::sh::file_exists;
    using std::sh::ls;
    using std::sh::cat;
    using std::sh::pwd;
    using std::sh::cd;
    using std::sh::env;
  } // namespace sh
} // namespace std
