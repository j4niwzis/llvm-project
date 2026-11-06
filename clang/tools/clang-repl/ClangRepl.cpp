//===--- tools/clang-repl/ClangRepl.cpp - clang-repl - the Clang REPL -----===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
//  This file implements a REPL tool on top of clang.
//
//===----------------------------------------------------------------------===//

#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticFrontend.h"
#include "clang/Basic/Version.h"
#include "clang/Config/config.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Interpreter/CodeCompletion.h"
#include "clang/Interpreter/Interpreter.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Sema/Sema.h"

#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/LineEditor/LineEditor.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/ManagedStatic.h" // llvm_shutdown
#include "llvm/Support/Path.h"
#include "llvm/Support/Process.h"
#include "llvm/Support/Signals.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/VirtualFileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Host.h"
#include "llvm/TargetParser/Triple.h"
#include <optional>

#include <string>
#include <vector>

// Disable LSan for this test.
// FIXME: Re-enable once we can assume GCC 13.2 or higher.
// https://llvm.org/github.com/llvm/llvm-project/issues/67586.
#if LLVM_ADDRESS_SANITIZER_BUILD || LLVM_HWADDRESS_SANITIZER_BUILD
#include <sanitizer/lsan_interface.h>
LLVM_ATTRIBUTE_USED int __lsan_is_turned_off() { return 1; }
#endif

#define DEBUG_TYPE "clang-repl"

static llvm::cl::opt<bool> CudaEnabled("cuda", llvm::cl::Hidden);
static llvm::cl::opt<bool> HipEnabled("hip", llvm::cl::Hidden);
static llvm::cl::opt<std::string> RocmPath("rocm-path", llvm::cl::Hidden);
static llvm::cl::opt<std::string> CudaPath("cuda-path", llvm::cl::Hidden);
static llvm::cl::opt<std::string> OffloadArch("offload-arch", llvm::cl::Hidden);
static llvm::cl::OptionCategory OOPCategory("Out-of-process Execution Options");
static llvm::cl::opt<std::string> SlabAllocateSizeString(
    "slab-allocate",
    llvm::cl::desc("Allocate from a slab of the given size "
                   "(allowable suffixes: Kb, Mb, Gb. default = "
                   "Kb)"),
    llvm::cl::init(""), llvm::cl::cat(OOPCategory));
static llvm::cl::opt<std::string>
    OOPExecutor("oop-executor",
                llvm::cl::desc("Launch an out-of-process executor to run code"),
                llvm::cl::init(""), llvm::cl::ValueOptional,
                llvm::cl::cat(OOPCategory));
static llvm::cl::opt<std::string> OOPExecutorConnect(
    "oop-executor-connect",
    llvm::cl::desc(
        "Connect to an out-of-process executor through a TCP socket"),
    llvm::cl::value_desc("<hostname>:<port>"));
static llvm::cl::opt<std::string>
    OrcRuntimePath("orc-runtime", llvm::cl::desc("Path to the ORC runtime"),
                   llvm::cl::init(""), llvm::cl::ValueOptional,
                   llvm::cl::cat(OOPCategory));
static llvm::cl::opt<bool> UseSharedMemory(
    "use-shared-memory",
    llvm::cl::desc("Use shared memory to transfer generated code and data"),
    llvm::cl::init(false), llvm::cl::cat(OOPCategory));
static llvm::cl::list<std::string>
    ClangArgs("Xcc",
              llvm::cl::desc("Argument to pass to the CompilerInvocation"),
              llvm::cl::CommaSeparated);
static llvm::cl::opt<bool> OptHostSupportsJit("host-supports-jit",
                                              llvm::cl::Hidden);
static llvm::cl::opt<bool> OptHostJitTriple("host-jit-triple",
                                            llvm::cl::Hidden);
static llvm::cl::list<std::string> OptInputs(llvm::cl::Positional,
                                             llvm::cl::desc("[code to run]"));
static llvm::cl::opt<bool> CppShEnabled(
    "cppsh",
    llvm::cl::desc("Enable C++ shell runtime (operator_unresolved, _, ls, "
                   "filter, sort_by, take)"),
    llvm::cl::init(false));

static const char *const CppShRuntimePrelude = R"CPPSH(
extern "C" int printf(const char *, ...);
extern "C" int snprintf(char *, unsigned long, const char *, ...);
extern "C" int system(const char *);
extern "C" unsigned long strlen(const char *);
extern "C" int strcmp(const char *, const char *);
extern "C" void *malloc(unsigned long);
extern "C" void *realloc(void *, unsigned long);
extern "C" void free(void *);
extern "C" void *memcpy(void *, const void *, unsigned long);

struct cppsh_str {
  char buf[256];
  unsigned long len = 0;
  constexpr cppsh_str() : buf{0}, len(0) {}
  cppsh_str(const char *s) {
    len = s ? strlen(s) : 0;
    if (len > 255) len = 255;
    if (len) memcpy(buf, s, len);
    buf[len] = '\0';
  }
  constexpr const char *c_str() const noexcept { return buf; }
  constexpr unsigned long size() const noexcept { return len; }
  friend bool operator==(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.buf, b.buf) == 0;
  }
  friend bool operator==(const cppsh_str &a, const char *b) {
    return strcmp(a.buf, b ? b : "") == 0;
  }
  friend bool operator!=(const cppsh_str &a, const char *b) {
    return strcmp(a.buf, b ? b : "") != 0;
  }
  friend bool operator<(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.buf, b.buf) < 0;
  }
  friend bool operator>(const cppsh_str &a, const cppsh_str &b) {
    return strcmp(a.buf, b.buf) > 0;
  }
};

template <char... Cs>
struct sym {
  static constexpr const char value[sizeof...(Cs) + 1] = {Cs..., '\0'};
  constexpr operator const char *() const noexcept { return value; }
  operator cppsh_str() const { return cppsh_str(value); }
  constexpr const char *c_str() const noexcept { return value; }
  constexpr unsigned long size() const noexcept { return sizeof...(Cs); }
  template <char... NextCs>
  constexpr auto operator_unresolved() const noexcept {
    return sym<Cs..., '.', NextCs...>{};
  }
  constexpr auto operator-() const noexcept { return sym<'-', Cs...>{}; }
  constexpr auto operator--() const noexcept { return sym<'-', '-', Cs...>{}; }
  template <char... RCs>
  constexpr auto operator-(sym<RCs...>) const noexcept {
    return sym<Cs..., '-', RCs...>{};
  }
  template <char... RCs>
  constexpr auto operator/(sym<RCs...>) const noexcept {
    return sym<Cs..., '/', RCs...>{};
  }
  template <typename... Args>
  int operator()(Args &&...args) const {
    char cmd[2048];
    unsigned long pos = 0;
    auto appendStr = [&](const char *s) {
      while (s && *s && pos + 1 < sizeof(cmd))
        cmd[pos++] = *s++;
      cmd[pos] = '\0';
    };
    appendStr(value);
    auto appendOne = [&](const auto &a) {
      appendStr(" ");
      if constexpr (requires { static_cast<const char *>(a); }) {
        appendStr(static_cast<const char *>(a));
      } else if constexpr (requires { a.c_str(); }) {
        appendStr(a.c_str());
      } else {
        char num[64];
        snprintf(num, sizeof(num), "%lld", (long long)a);
        appendStr(num);
      }
    };
    (appendOne(args), ...);
    return system(cmd);
  }
};

template <char... Cs>
constexpr auto operator_unresolved() noexcept {
  return sym<Cs...>{};
}

constexpr unsigned long long operator""_KB(unsigned long long v) noexcept {
  return v * 1024ULL;
}
constexpr unsigned long long operator""_MB(unsigned long long v) noexcept {
  return v * 1024ULL * 1024ULL;
}
constexpr unsigned long long operator""_GB(unsigned long long v) noexcept {
  return v * 1024ULL * 1024ULL * 1024ULL;
}

template <typename F>
struct cppsh_proj {
  F fn;
  template <typename T>
  constexpr decltype(auto) operator()(T &&x) const {
    return fn(static_cast<T &&>(x));
  }
  template <char... Cs>
  constexpr auto operator_unresolved() const {
    auto next = [prev = fn](auto &&x) -> decltype(auto) {
      auto &&obj = prev(static_cast<decltype(x) &&>(x));
      return obj.template __cppsh_member<Cs...>;
    };
    return cppsh_proj<decltype(next)>{next};
  }
#define CPPSH_BINOP(OP)                                                        \
  template <typename R>                                                        \
  constexpr auto operator OP(R rhs) const {                                    \
    auto p = [f = fn, r = rhs](auto &&x) {                                     \
      return f(static_cast<decltype(x) &&>(x)) OP r;                           \
    };                                                                         \
    return cppsh_proj<decltype(p)>{p};                                         \
  }
  CPPSH_BINOP(==)
  CPPSH_BINOP(!=)
  CPPSH_BINOP(<)
  CPPSH_BINOP(>)
  CPPSH_BINOP(<=)
  CPPSH_BINOP(>=)
  CPPSH_BINOP(+)
  CPPSH_BINOP(-)
  CPPSH_BINOP(*)
  CPPSH_BINOP(/)
  CPPSH_BINOP(%)
  CPPSH_BINOP(&&)
  CPPSH_BINOP(||)
#undef CPPSH_BINOP
};

struct cppsh_placeholder_root {
  template <typename T>
  constexpr T &&operator()(T &&x) const noexcept {
    return static_cast<T &&>(x);
  }
};
inline constexpr cppsh_proj<cppsh_placeholder_root> _{cppsh_placeholder_root{}};

template <typename T>
struct cppsh_vec {
  T *data_ = nullptr;
  unsigned long size_ = 0;
  unsigned long cap_ = 0;
  cppsh_vec() = default;
  cppsh_vec(const cppsh_vec &o) {
    for (unsigned long i = 0; i < o.size_; ++i)
      push_back(o.data_[i]);
  }
  cppsh_vec &operator=(const cppsh_vec &o) {
    if (this != &o) {
      free(data_);
      data_ = nullptr;
      size_ = cap_ = 0;
      for (unsigned long i = 0; i < o.size_; ++i)
        push_back(o.data_[i]);
    }
    return *this;
  }
  ~cppsh_vec() { free(data_); }
  void push_back(const T &v) {
    if (size_ == cap_) {
      cap_ = cap_ ? cap_ * 2 : 16;
      data_ = static_cast<T *>(realloc(data_, cap_ * sizeof(T)));
    }
    data_[size_++] = v;
  }
  T *begin() { return data_; }
  T *end() { return data_ + size_; }
  const T *begin() const { return data_; }
  const T *end() const { return data_ + size_; }
  unsigned long size() const { return size_; }
  T &operator[](unsigned long i) { return data_[i]; }
  const T &operator[](unsigned long i) const { return data_[i]; }
};

struct file_entry {
  cppsh_str name;
  cppsh_str ext;
  long long size = 0;
  bool is_dir = false;
  void dump() const {
    printf("%s %-28s %10lld B\n", is_dir ? "[dir] " : "[file]", name.c_str(),
           size);
  }
};

struct ls_opts {
  bool all = false;
  bool recursive = false;
  bool dirs_only = false;
  bool files_only = false;
};

extern "C" {
struct __cppsh_dirent {
  unsigned long d_ino;
  long d_off;
  unsigned short d_reclen;
  unsigned char d_type;
  char d_name[256];
};
void *opendir(const char *);
__cppsh_dirent *readdir(void *);
int closedir(void *);
int __xstat(int, const char *, void *);
int stat(const char *, void *);
}

inline cppsh_vec<file_entry> ls(const char *dir = ".", ls_opts opts = {}) {
  if (dir && dir[0] == '-') {
    for (const char *p = dir + 1; *p; ++p)
      if (*p == 'a')
        opts.all = true;
    dir = ".";
  }
  cppsh_vec<file_entry> out;
  void *d = opendir(dir);
  if (!d)
    return out;
  while (__cppsh_dirent *de = readdir(d)) {
    const char *fname = de->d_name;
    if (strcmp(fname, ".") == 0 || strcmp(fname, "..") == 0)
      continue;
    if (!opts.all && fname[0] == '.')
      continue;
    bool isDir = (de->d_type == 4);
    char fullpath[1024];
    snprintf(fullpath, sizeof(fullpath), "%s/%s", dir, fname);
    alignas(8) unsigned char stbuf[256] = {0};
    long long fsize = 0;
    if (stat(fullpath, stbuf) == 0) {
      unsigned int mode = *reinterpret_cast<unsigned int *>(stbuf + 24);
      isDir = ((mode & 0170000) == 0040000);
      if (!isDir)
        fsize = *reinterpret_cast<long long *>(stbuf + 48);
    }
    if (opts.dirs_only && !isDir)
      continue;
    if (opts.files_only && isDir)
      continue;
    const char *dot = nullptr;
    for (const char *p = fname; *p; ++p)
      if (*p == '.')
        dot = p;
    out.push_back({cppsh_str(fname), cppsh_str(dot ? dot : ""), fsize, isDir});
  }
  closedir(d);
  return out;
}

template <typename Pred>
struct cppsh_filter_stage {
  Pred pred;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_filter_stage &s) {
    Rng out;
    for (auto &&item : rng)
      if (s.pred(item))
        out.push_back(item);
    return out;
  }
};
template <typename Pred>
constexpr auto filter(Pred p) {
  return cppsh_filter_stage<Pred>{p};
}

template <typename Proj>
struct cppsh_sort_stage {
  Proj proj;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_sort_stage &s) {
    for (unsigned long i = 0; i < rng.size(); ++i)
      for (unsigned long j = i + 1; j < rng.size(); ++j)
        if (s.proj(rng[j]) < s.proj(rng[i])) {
          auto tmp = rng[i];
          rng[i] = rng[j];
          rng[j] = tmp;
        }
    return rng;
  }
};
template <typename Proj>
constexpr auto sort_by(Proj p) {
  return cppsh_sort_stage<Proj>{p};
}

struct cppsh_take_stage {
  unsigned long n;
  template <typename Rng>
  friend auto operator|(Rng rng, const cppsh_take_stage &s) {
    Rng out;
    unsigned long i = 0;
    for (auto &&item : rng) {
      if (i++ >= s.n)
        break;
      out.push_back(item);
    }
    return out;
  }
};
inline constexpr auto take(unsigned long n) { return cppsh_take_stage{n}; }

struct cppsh_print_stage {
  template <typename Rng>
  friend void operator|(Rng rng, const cppsh_print_stage &) {
    for (const auto &item : rng)
      item.dump();
  }
};
inline constexpr cppsh_print_stage show{};

template <typename A, typename B>
inline constexpr bool __cppsh_same = false;
template <typename A>
inline constexpr bool __cppsh_same<A, A> = true;

template <typename T>
void print(const T &v) {
  if constexpr (requires { v.c_str(); })
    printf("%s\n", v.c_str());
  else if constexpr (requires { static_cast<const char *>(v); })
    printf("%s\n", static_cast<const char *>(v));
  else if constexpr (__cppsh_same<T, double> || __cppsh_same<T, float>)
    printf("%g\n", (double)v);
  else
    printf("%lld\n", (long long)v);
}
)CPPSH";

static llvm::Error sanitizeOopArguments(const char *ArgV0) {
  // Only one of -oop-executor and -oop-executor-connect can be used.
  if (!!OOPExecutor.getNumOccurrences() &&
      !!OOPExecutorConnect.getNumOccurrences())
    return llvm::make_error<llvm::StringError>(
        "Only one of -" + OOPExecutor.ArgStr + " and -" +
            OOPExecutorConnect.ArgStr + " can be specified",
        llvm::inconvertibleErrorCode());

  llvm::Triple SystemTriple(llvm::sys::getProcessTriple());
  // TODO: Remove once out-of-process execution support is implemented for
  // non-Unix platforms.
  if ((!SystemTriple.isOSBinFormatELF() &&
       !SystemTriple.isOSBinFormatMachO()) &&
      (OOPExecutor.getNumOccurrences() ||
       OOPExecutorConnect.getNumOccurrences()))
    return llvm::make_error<llvm::StringError>(
        SystemTriple.isOSEmscripten()
            ? "Out-of-process execution is not supported by the WebAssembly "
              "executor"
            : "Out-of-process execution is only supported on Unix platforms",
        llvm::inconvertibleErrorCode());

  // If -slab-allocate is passed, check that we're not trying to use it in
  // -oop-executor or -oop-executor-connect mode.
  //
  // FIXME: Remove once we enable remote slab allocation.
  if (SlabAllocateSizeString != "") {
    if (OOPExecutor.getNumOccurrences() ||
        OOPExecutorConnect.getNumOccurrences())
      return llvm::make_error<llvm::StringError>(
          "-slab-allocate cannot be used with -oop-executor or "
          "-oop-executor-connect",
          llvm::inconvertibleErrorCode());
  }

  // Out-of-process executors require the ORC runtime. ORC Runtime Path
  // resolution is done in Interpreter.cpp.

  // If -oop-executor was used but no value was specified then use a sensible
  // default.
  if (!!OOPExecutor.getNumOccurrences() && OOPExecutor.empty()) {
    llvm::SmallString<256> OOPExecutorPath(llvm::sys::fs::getMainExecutable(
        ArgV0, reinterpret_cast<void *>(&sanitizeOopArguments)));
    llvm::sys::path::remove_filename(OOPExecutorPath);
    llvm::sys::path::append(OOPExecutorPath, "llvm-jitlink-executor");
    OOPExecutor = OOPExecutorPath.str().str();
  }

  return llvm::Error::success();
}

static llvm::Expected<unsigned> getSlabAllocSize(llvm::StringRef SizeString) {
  SizeString = SizeString.trim();

  uint64_t Units = 1024;

  if (SizeString.ends_with_insensitive("kb"))
    SizeString = SizeString.drop_back(2).rtrim();
  else if (SizeString.ends_with_insensitive("mb")) {
    Units = 1024 * 1024;
    SizeString = SizeString.drop_back(2).rtrim();
  } else if (SizeString.ends_with_insensitive("gb")) {
    Units = 1024 * 1024 * 1024;
    SizeString = SizeString.drop_back(2).rtrim();
  } else if (SizeString.empty())
    return 0;

  uint64_t SlabSize = 0;
  if (SizeString.getAsInteger(10, SlabSize))
    return llvm::make_error<llvm::StringError>(
        "Invalid numeric format for slab size", llvm::inconvertibleErrorCode());

  return SlabSize * Units;
}

static void LLVMErrorHandler(void *UserData, const char *Message,
                             bool GenCrashDiag) {
  auto &Diags = *static_cast<clang::DiagnosticsEngine *>(UserData);

  Diags.Report(clang::diag::err_fe_error_backend) << Message;

  // Run the interrupt handlers to make sure any special cleanups get done, in
  // particular that we remove files registered with RemoveFileOnSignal.
  llvm::sys::RunInterruptHandlers();

  // We cannot recover from llvm errors.  When reporting a fatal error, exit
  // with status 70 to generate crash diagnostics.  For BSD systems this is
  // defined as an internal software error. Otherwise, exit with status 1.

  exit(GenCrashDiag ? 70 : 1);
}

// If we are running with -verify a reported has to be returned as unsuccess.
// This is relevant especially for the test suite.
static int checkDiagErrors(const clang::CompilerInstance *CI, bool HasError) {
  unsigned Errs = CI->getDiagnostics().getClient()->getNumErrors();
  if (CI->getDiagnosticOpts().VerifyDiagnostics) {
    // If there was an error that came from the verifier we must return 1 as
    // an exit code for the process. This will make the test fail as expected.
    clang::DiagnosticConsumer *Client = CI->getDiagnostics().getClient();
    Client->EndSourceFile();
    Errs = Client->getNumErrors();

    // The interpreter expects BeginSourceFile/EndSourceFiles to be balanced.
    Client->BeginSourceFile(CI->getLangOpts(), &CI->getPreprocessor());
  }
  return (Errs || HasError) ? EXIT_FAILURE : EXIT_SUCCESS;
}

struct ReplListCompleter {
  clang::IncrementalCompilerBuilder &CB;
  clang::Interpreter &MainInterp;
  ReplListCompleter(clang::IncrementalCompilerBuilder &CB,
                    clang::Interpreter &Interp)
      : CB(CB), MainInterp(Interp) {};

  std::vector<llvm::LineEditor::Completion> operator()(llvm::StringRef Buffer,
                                                       size_t Pos) const;
  std::vector<llvm::LineEditor::Completion>
  operator()(llvm::StringRef Buffer, size_t Pos, llvm::Error &ErrRes) const;
};

std::vector<llvm::LineEditor::Completion>
ReplListCompleter::operator()(llvm::StringRef Buffer, size_t Pos) const {
  auto Err = llvm::Error::success();
  auto res = (*this)(Buffer, Pos, Err);
  if (Err)
    llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
  return res;
}

std::vector<llvm::LineEditor::Completion>
ReplListCompleter::operator()(llvm::StringRef Buffer, size_t Pos,
                              llvm::Error &ErrRes) const {
  std::vector<llvm::LineEditor::Completion> Comps;
  std::vector<std::string> Results;

  auto CI = CB.CreateCpp();
  if (auto Err = CI.takeError()) {
    ErrRes = std::move(Err);
    return {};
  }

  size_t Lines =
      std::count(Buffer.begin(), std::next(Buffer.begin(), Pos), '\n') + 1;
  auto Interp = clang::Interpreter::create(std::move(*CI));

  if (auto Err = Interp.takeError()) {
    // log the error and returns an empty vector;
    ErrRes = std::move(Err);

    return {};
  }
  auto *MainCI = (*Interp)->getCompilerInstance();
  auto CC = clang::ReplCodeCompleter();
  CC.codeComplete(MainCI, Buffer, Lines, Pos + 1,
                  MainInterp.getCompilerInstance(), Results);
  for (auto c : Results) {
    if (c.find(CC.Prefix) == 0)
      Comps.push_back(
          llvm::LineEditor::Completion(c.substr(CC.Prefix.size()), c));
  }
  return Comps;
}

llvm::ExitOnError ExitOnErr;
int main(int argc, const char **argv) {
  llvm::sys::PrintStackTraceOnErrorSignal(argv[0]);

  ExitOnErr.setBanner("clang-repl: ");
  llvm::cl::ParseCommandLineOptions(argc, argv);

  llvm::llvm_shutdown_obj Y; // Call llvm_shutdown() on exit.

  std::vector<const char *> ClangArgv(ClangArgs.size());
  std::transform(ClangArgs.begin(), ClangArgs.end(), ClangArgv.begin(),
                 [](const std::string &s) -> const char * { return s.data(); });
  if (CppShEnabled || (OptInputs.empty() && llvm::sys::Process::StandardInIsUserInput()))
    ClangArgv.push_back("-std=gnu++20");
  // Initialize all targets (required for device offloading)
  llvm::InitializeAllTargetInfos();
  llvm::InitializeAllTargets();
  llvm::InitializeAllTargetMCs();
  llvm::InitializeAllAsmPrinters();
  llvm::InitializeAllAsmParsers();

  auto IEB = clang::IncrementalExecutorBuilder::createDefault();
  if (OptHostSupportsJit) {
    llvm::outs() << (IEB->supportsJIT() ? "true\n" : "false\n");
    return 0;
  } else if (OptHostJitTriple) {
    auto T = ExitOnErr(IEB->getHostJITTriple());
    llvm::outs() << T.normalize() << '\n';
    return 0;
  }

  ExitOnErr(sanitizeOopArguments(argv[0]));

  clang::IncrementalCompilerBuilder CB;
  CB.SetCompilerArgs(ClangArgv);

  auto SizeOrErr = getSlabAllocSize(SlabAllocateSizeString);
  if (!SizeOrErr) {
    llvm::logAllUnhandledErrors(SizeOrErr.takeError(), llvm::errs(), "error: ");
    return EXIT_FAILURE;
  }

  clang::IncrementalExecutorBuilder::Options ExecutorOpts;
  ExecutorOpts.IsOutOfProcess =
      !OOPExecutor.empty() || !OOPExecutorConnect.empty();
  ExecutorOpts.ExecutorPath = OOPExecutor;
  ExecutorOpts.RuntimePath = OrcRuntimePath;
  ExecutorOpts.SlabAllocateSize = *SizeOrErr;
  ExecutorOpts.UseSharedMemory = UseSharedMemory;
  ExitOnErr(IEB->configure(CB, ExecutorOpts));

  // If both -cuda and -hip are passed, the one that appears later wins.
  // FIXME: Support both CUDA and HIP setups at the same time, for example with
  // one interpreter per device language in a multi-interpreter setup.
  bool UseHip = HipEnabled && (!CudaEnabled || HipEnabled.getPosition() >
                                                   CudaEnabled.getPosition());
  bool DeviceEnabled = HipEnabled || CudaEnabled;

  clang::OffloadType OffloadKind =
      UseHip ? clang::OffloadType::HIP : clang::OffloadType::CUDA;
  std::string DevicePath = UseHip ? RocmPath : CudaPath;
  llvm::StringRef DeviceOffloadArch = !OffloadArch.empty()
                                          ? llvm::StringRef(OffloadArch)
                                          : (UseHip ? "native" : "sm_35");

  std::unique_ptr<clang::CompilerInstance> DeviceCI;

  if (DeviceEnabled) {
    CB.SetDeviceSDK(DevicePath);
    CB.SetOffloadArch(DeviceOffloadArch);
    DeviceCI = ExitOnErr(CB.CreateDevice(OffloadKind));
  }

  // FIXME: Investigate if we could use runToolOnCodeWithArgs from tooling. It
  // can replace the boilerplate code for creation of the compiler instance.
  std::unique_ptr<clang::CompilerInstance> CI;
  if (DeviceEnabled) {
    CI = ExitOnErr(CB.CreateHost(OffloadKind));
  } else {
    CI = ExitOnErr(CB.CreateCpp());
  }

  // Set an error handler, so that any LLVM backend diagnostics go through our
  // error handler.
  llvm::install_fatal_error_handler(LLVMErrorHandler,
                                    static_cast<void *>(&CI->getDiagnostics()));

  // Load any requested plugins.
  CI->LoadRequestedPlugins();
  if (DeviceEnabled)
    DeviceCI->LoadRequestedPlugins();

  std::unique_ptr<clang::Interpreter> Interp;

  if (DeviceEnabled) {
    Interp = ExitOnErr(clang::Interpreter::createWithDevice(
        std::move(CI), std::move(DeviceCI), OffloadKind));

    const char *RuntimeLib = UseHip ? "libamdhip64.so" : "libcudart.so";
    if (DevicePath.empty()) {
      ExitOnErr(Interp->LoadDynamicLibrary(RuntimeLib));
    } else {
      std::string RuntimeLibPath = DevicePath + "/lib/" + RuntimeLib;
      ExitOnErr(Interp->LoadDynamicLibrary(RuntimeLibPath.c_str()));
    }
  } else {
    Interp =
        ExitOnErr(clang::Interpreter::create(std::move(CI), std::move(IEB)));
  }

  bool HasError = false;

  if (CppShEnabled ||
      (OptInputs.empty() && llvm::sys::Process::StandardInIsUserInput())) {
    if (auto Err = Interp->ParseAndExecute(CppShRuntimePrelude)) {
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      HasError = true;
    }
  }

  for (const std::string &input : OptInputs) {
    if (auto Err = Interp->ParseAndExecute(input)) {
      llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      HasError = true;
    }
  }

  if (OptInputs.empty()) {
    llvm::LineEditor LE("clang-repl");
    std::string Input;
    LE.setListCompleter(ReplListCompleter(CB, *Interp));
    while (std::optional<std::string> Line = LE.readLine()) {
      llvm::StringRef L = *Line;
      L = L.trim();
      if (L.ends_with("\\")) {
        Input += L.drop_back(1);
        // If it is a preprocessor directive, new lines matter.
        if (L.starts_with('#'))
          Input += "\n";
        LE.setPrompt("clang-repl...   ");
        continue;
      }

      Input += L;
      // If we add more % commands, there should be better architecture than
      // this.
      if (Input == R"(%quit)") {
        break;
      }
      if (Input == R"(%undo)") {
        if (auto Err = Interp->Undo())
          llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      } else if (Input == R"(%cppsh)") {
        if (auto Err = Interp->ParseAndExecute(CppShRuntimePrelude))
          llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      } else if (Input == R"(%help)") {
        llvm::outs() << "%help\t\tlist clang-repl %commands\n"
                     << "%cppsh\t\tload C++ shell runtime (_, ls, filter, "
                        "sort_by, take, show)\n"
                     << "%undo\t\tundo the previous input\n"
                     << "%lib\t<path>\tlink a dynamic library\n"
                     << "%quit\t\texit clang-repl\n";
      } else if (Input == R"(%lib)") {
        auto Err = llvm::make_error<llvm::StringError>(
            "%lib expects 1 argument: the path to a dynamic library\n",
            std::error_code());
        llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      } else if (Input.rfind("%lib ", 0) == 0) {
        if (auto Err = Interp->LoadDynamicLibrary(Input.data() + 5))
          llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      } else if (Input[0] == '%') {
        auto Err = llvm::make_error<llvm::StringError>(
            llvm::formatv(
                "Invalid % command \"{0}\", use \"%help\" to list commands\n",
                Input),
            std::error_code());
        llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      } else if (auto Err = Interp->ParseAndExecute(Input)) {
        llvm::logAllUnhandledErrors(std::move(Err), llvm::errs(), "error: ");
      }

      Input = "";
      LE.setPrompt("clang-repl> ");
    }
  }

  // Our error handler depends on the Diagnostics object, which we're
  // potentially about to delete. Uninstall the handler now so that any
  // later errors use the default handling behavior instead.
  llvm::remove_fatal_error_handler();

  return checkDiagErrors(Interp->getCompilerInstance(), HasError);
}
