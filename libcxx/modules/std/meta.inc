// -*- C++ -*-
//===----------------------------------------------------------------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

export namespace std {
namespace meta {
  using std::meta::info;
  using std::meta::info_range;
  using std::meta::__reflect;
  using std::meta::__splice_call;
  using std::meta::identifier_of;
  using std::meta::is_type;
  using std::meta::is_nonstatic_data_member;
  using std::meta::is_member_function;
  using std::meta::is_function;
  using std::meta::remove_cvref;
  using std::meta::members_of;
  using std::meta::find_member;
} // namespace meta

using std::cppsh_proj;
using std::cppsh_placeholder_root;
using std::cppsh_arg_n;

namespace placeholders {
  using std::placeholders::_;
  using std::placeholders::_1;
  using std::placeholders::_2;
  using std::placeholders::_3;
  using std::placeholders::_4;
  using std::placeholders::_5;
} // namespace placeholders
} // namespace std
