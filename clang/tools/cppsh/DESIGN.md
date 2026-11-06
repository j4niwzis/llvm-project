# `cppsh` — C++26 Interactive Shell & Language Extensions (`llvm-project` Design Document)

## 1. Концепция и цель проекта

**`cppsh`** — это интерактивный шелл (REPL) и скриптовый рантайм поверх Clang/LLVM (`clang-repl` / `clang::Interpreter` + ORC JIT), превращающий C++26 со статической рефлексией (P2996 `^^T` / `[:r:]`) и `std::ranges` в полноценный типизированный командный язык в духе **Nushell / PowerShell / Haskell**, но с нативной компиляцией через Clang и прямым доступом ко всей экосистеме C++.

Ключевые принципы дизайна:
1. **Единый язык для шелла и программ:** команды шелла (`ls`, `lines`, `head`, `tail`, `cat`, `cd`, `cp`, `mv`, `rm`, `exec`, `run`) — это обычные типизированные функции и ленивые `std::ranges::view` в пространстве имён `std::sh` (экспортируемые модулем `std.sh`).
2. **Структурированные конвейеры вместо сырого текста:** `ls` возвращает ленивый диапазон структур `file_entry { name, ext, size, is_dir }`, а `lines("file")` — ленивый диапазон `line_entry { num, text, size }`. Пайплайн `|` — это стандартный оператор адаптеров `std::ranges::views` (`filter`, `where`, `sort_by`, `take`, `drop`, `transform`, `grep`, `show`).
3. **Лаконичный синтаксис без бойлерплейта:**
   - Вызов функций без скобок (`ls "." {.all = true}`, `take 5`, `std::println "{}" x`).
   - Неявный `auto` для переменных и функций (`x = 42;`, `f x = x + 1;`).
   - Автоматический подъём выражений с плейсхолдерами `_` / `_1`..`_5` в лямбды (`_.size > 10_KB`, `_.name.starts_with("R")`).
   - Специализация шаблонных `auto`-функций по значениям аргументов (`if (n == 0)` фолдится на этапе инстанцирования шаблона и позволяет веткам возвращать разные типы без `if constexpr`).
   - Автовызов 0-аргументных команд (`ls` → `ls()`) и авторендеринг ленивых диапазонов в таблицу Nushell (`╭───┬───╮`) на верхнем уровне REPL.

---

## 2. Архитектура и карта изменённых компонентов в `llvm-project`

### 2.1. Лексер и Парсер (`clang/lib/Lex`, `clang/lib/Parse`)
| Файл | Что сделано и как работает |
|---|---|
| `clang/include/clang/Basic/TokenKinds.def`<br>`clang/lib/Lex/Lexer.cpp` | Добавлена лексема `^^` (`tok::caretcaret`) для оператора отражения C++26 (P2996) и скобки сплайсинга `[: ... :]`. |
| `clang/lib/Parse/ParseTentative.cpp`<br>`clang/lib/Parse/ParseDecl.cpp`<br>`clang/lib/Parse/ParseStmt.cpp` | **Неявный `auto` (`isImplicitAutoDeclaration`):** если идентификатор не является именем типа и за ним идёт `=`, парсер автоматически подставляет `DeclSpec::TST_auto`.<br>**Краткое объявление функций (`f x = expr`):** `isConciseFunctionDeclaration()` распознаёт `ident param1 param2 = body` и строит определение функции с `auto`-параметрами (шаблон функции в C++20/23) и телом `return expr;`.<br>**Range-for по командам (`for (x : ls)`):** в `ParseForRangeInitializerAfterColon` и при инициализации `auto`-переменных (`obj = ls;`) 0-аргументные функции из `std::sh` автоматически вызываются (`ls()`). |
| `clang/lib/Parse/ParseExpr.cpp`<br>`clang/lib/Parse/ParseExprCXX.cpp` | **Вызов без скобок (Juxtaposition Call):** если за выражением-функцией (или именем шаблона/переменной с `operator()`) на той же строке следует аргумент (литерал, идентификатор, `{...}`, `_`), парсер собирает аргументы до `|`, `;` или конца выражения и вызывает `ActOnCallExpr`.<br>**Отражение и сплайсинг (`^^expr`, `^^Type`, `[:r:]`, `typename [:r:]`, `obj.[:r:]`):** парсинг унарного `^^` и сплайсов в выражениях, типах и доступе к членам класса. |

### 2.2. Семантический анализ, Рефлексия и Шаблоны (`clang/lib/Sema`, `clang/lib/AST`)
| Файл | Что сделано и как работает |
|---|---|
| `clang/lib/Sema/SemaExpr.cpp` | **1. Подъём плейсхолдеров (`_` / `_1`..`_5`):** выражения вида `_.size > 100` или `_.name.starts_with("R")` автоматически оборачиваются в синтетическую generic-лямбду `[](auto &&_1) -> decltype(auto) { return _1.size > 100; }`. Это работает как для обычных бинарных/унарных операторов, так и для цепочек вызовов методов.<br>**2. Автовызов на левой стороне пайпа (`LHS \| RHS`):** если `LHS` в `BuildBinOp(BO_Or)` — 0-аргументная функция (`ls`), она автоматически превращается в `ls()` перед передачей в `operator\|`.<br>**3. Value-специализация `auto`-функций:** при вызове функции с `auto`-параметрами и константными аргументами создаётся специализированный `FunctionTemplateDecl` (`<Name>__cppsh_val_<ID>`) с сохранёнными `APValue` параметров (`ParamConstValues`), чтобы внутри тела функции обычные `if (cond)` могли сворачиваться на этапе инстанцирования.<br>**4. Рефлексия (`ActOnReflectExpr` / `ActOnSpliceExpr`):** создание `CXXReflectExpr` (`std::meta::info { id, kind }`) и разрешение сплайсов полей/типов/значений, а также генерация constexpr-массива `__cppsh_meta_members_<Record>` для `std::meta::members_of(^^T)`. |
| `clang/lib/Sema/TreeTransform.h` | В `TransformIfStmt`: если условие обычного (не `constexpr`) `if` при подстановке шаблона константно вычисляется через `EvaluateAsBooleanCondition`, `TreeTransform` сразу возвращает только активную ветку (`Then` или `Else`), не проверяя типы отброшенной ветки. Это позволяет разным веткам обычного `if` возвращать разные типы в `auto`-функциях. |
| `clang/lib/Sema/SemaTemplateInstantiateDecl.cpp` | При инстанцировании `FunctionDecl` копируются `ParamConstValues` из шаблона в параметры специализации, чтобы `ExprConstant` видел константные значения аргументов вызова. |
| `clang/lib/AST/ExprConstant.cpp` | Вычисление `CXXReflectExpr`, встроенных функций рефлексии (`__builtin_meta_identifier_of`, `__builtin_meta_is_nonstatic_data_member`, `__builtin_meta_type_of`) и чтение `ParamConstValues` у `ParmVarDecl` во время constant evaluation. |
| `clang/lib/AST/ItaniumMangle.cpp` | В `mangleUnscopedTemplateName`: если специализированный `FunctionTemplateDecl` имеет собственное имя `SpecTemplate` (`f__cppsh_val_N`), отличное от `getTemplatedDecl()->getDeclName()`, манглится уникальное имя `SpecTemplate`, чтобы разные value-специализации с одинаковыми типами аргументов не конфликтовали в ORC JIT. |
| `clang/lib/AST/ASTImporter.cpp` | В `ASTImporter::Import(FileID)` перед рекурсивным импортом `IncludeLoc` ставится заглушка `ImportedFileIDs[FromID] = ToSM.getMainFileID()`, устраняющая бесконечную рекурсию при `Tab`-дополнении с импортированным модулем `std.sh`. |

### 2.3. Модули, Кэширование и Интерпретатор (`clang/lib/Frontend`, `clang/lib/Interpreter`)
| Файл | Что сделано и как работает |
|---|---|
| `clang/lib/Frontend/CompilerInstance.cpp` | **Генерация и дисковый кэш модулей `std` и `std.sh`:**<br>`findOrCompileModuleAndReadAST` автоматически синтезирует `std` и `std.sh` через `createModuleFromSource`. Скомпилированные `.pcm` и `.map` файлы сохраняются в `/tmp/cppsh_pcm_cache/std_sh_<hash>.pcm`, где `<hash>` учитывает `ContextHash`, содержимое modulemap, `mtime`/`size` файлов `<sh>`, `<meta>`, `<__sh/sh_using.h>` и бинарника `cppsh`. При повторном запуске `cppsh` модуль читается с диска без перекомпиляции; при изменении заголовков или флагов автоматически пересобирается. |
| `clang/lib/Interpreter/Interpreter.cpp` | **1. Автопоиск путей `libc++` и кэш системных путей (`/tmp/cppsh_sysdirs.cache`):** находит `build/include/c++/v1` и `libcxx/include` относительно исполняемого файла, а системные пути `g++ -Wp,-v` кэширует в `/tmp/cppsh_sysdirs.cache`.<br>**2. Поддержка 128-битной арифметики в JIT (`__udivti3`, `__umodti3`, `__divti3`, `__modti3`, `__udivmodti4`):** функции реализованы в `Interpreter.cpp` и регистрируются через `llvm::sys::DynamicLibrary::AddSymbol`, чтобы `std::format` и `std::println` работали в JIT без ошибки отсутствующих символов `libgcc`. |
| `clang/lib/Interpreter/InterpreterValuePrinter.cpp` | В интерактивном режиме на верхнем уровне REPL: если введено имя 0-аргументной функции (`ls`, `pwd`), она автоматически вызывается; если результат выражения является ленивым `view` (или имеет метод `.show()` / передаётся в `std::ranges::views::show`), к нему автоматически применяется `\| show` для отрисовки таблицы. |

### 2.4. Стандартная библиотека `std::meta` и `std::sh` (`libcxx/include`)
| Файл | Что сделано и как работает |
|---|---|
| `libcxx/include/meta` | Реализация `std::meta::info`, `members_of`, `identifier_of`, `type_of`, `is_nonstatic_data_member` для статической рефлексии C++26. |
| `libcxx/include/sh` | Полная библиотека шелла в `std::sh` и `std::ranges::views`:<br>• **Структуры данных:** `file_entry { name, ext, size, is_dir }`, `ls_opts { all, recursive, dirs_only, files_only }`, `line_entry { num, text, size }`, `sh_result { code, out }`, символьные пути/флаги `sym<Cs...>` (`operator_unresolved`).<br>• **Ленивые генераторы и команды:** `ls`, `glob`, `lines`, `read_lines`, `read_file`, `write_file`, `append_file`, `cat`, `head`, `tail`, `wc_l`, `pwd`, `cd`, `env`, `setenv`, `exists`, `mkdir_p`, `rm`, `cp`, `mv`, `touch`, `run`, `exec`.<br>• **Конвейерные адаптеры:** `grep`, `sort_by`, `show` (и стандартные `filter`, `take`, `drop`, `transform`, `reverse`).<br>• **Рендерер таблиц Nushell (`__cppsh_render_nu_table`):** рисует таблицы с рамками Unicode (`╭─┬─╮`, `├─┼─┤`, `╰─┴─╯`), автовыравниванием колонок по UTF-8 ширине, подсветкой типов/размеров (`2.2 KB`, `1.5 MB`) и автоматической рефлексией произвольных пользовательских структур через `meta::members_of(^^ElemT)` и сплайсинг `item.[:field:]`.<br>• **Интеграция с `<format>` и `<print>`:** специализации `std::formatter` для `file_entry`, `line_entry`, `sh_result`. |
| `libcxx/include/__sh/sh_using.h` | Экспортирует все команды `std::sh::*`, адаптеры `std::ranges::views::*`, `std::print`, `std::println`, `std::format` и плейсхолдеры `_`, `_1`..`_5` в глобальное пространство имён при `import std.sh;`. |

### 2.5. Терминал, `LineEditor` и бинарник `cppsh` (`llvm/lib/LineEditor`, `clang/tools/cppsh`)
| Файл | Что сделано и как работает |
|---|---|
| `llvm/lib/LineEditor/LineEditor.cpp` | • Переключён на `EL_PROMPT_ESC` с маркером `\001`, чтобы ANSI-цвета в промпте не ломали подсчёт ширины строки в `libedit`.<br>• Включена поддержка UTF-8 локали (`setlocale(LC_ALL, "")`) для корректного ввода кириллицы и Unicode.<br>• Многоколоночный вывод `Tab`-подсказок с вычислением визуальной ширины UTF-8 и игнорированием ANSI-кодов (и одноколоночный режим для многострочных карточек).<br>• Обработка `SIGINT` (`Ctrl + C`) через `sigaction` без выхода из шелла (`el_reset`, вывод `^C` и возврат маркера `"\x03"`). |
| `clang/tools/cppsh/CppSh.cpp`<br>`clang/tools/cppsh/CMakeLists.txt` | Отдельный бинарник `cppsh`:<br>• Автоматически выполняет `import std.sh;` при старте и включает `-std=gnu++23 -Wno-unused-result -Wno-unused-value`.<br>• Цветной промпт `user path $ ` с сокращением `$HOME` в `~` и красным `$` при ошибке предыдущей команды.<br>• Встроенные команды шелла `cd`, `clear`, `exit`/`quit`, `%undo`, а также запуск скриптов (`cppsh script.cppsh` и `-c "..."`).<br>• Кастомный `ReplListCompleter` для `Tab`-автодополнения: флаги в designated initializers (`ls {.` + `Tab`), поля структур в пайплайнах (`_.` + `Tab` и `_.name.` + `Tab`), пути файловой системы и команды. |

---

## 3. Текущий статус `clang/tools/cppsh/CppSh.cpp`

Все изменения в компиляторе, `Interpreter.cpp`, `CompilerInstance.cpp`, `LineEditor.cpp`, `ParseStmt.cpp`, `ParseDecl.cpp`, `libcxx/include/sh` и `libcxx/include/__sh/sh_using.h` написаны и запушены. В `CppSh.cpp` дописано:

1. **`Ctrl + C` (маркер `"\x03"` от `LineEditor::readLine()`):** в `main()` ввод (вместе с продолженными через `\` строками) сбрасывается, `$` в промпте становится красным, выводится новый промпт.
2. **Резолв типа выражения перед `.` по AST (`ReplListCompleter`):**
   - текст перед точкой читается как цепочка (`chainBackward`): имя, затем шаги `.member` / `.method(...)`;
   - корень цепочки (`rootType`): плейсхолдер `_` / `_1` — элемент того, с чего начинается пайплайн текущего выражения (до первого `|`); переменная `for (x : rng)` / `for (auto &x : rng)` из буфера — элемент `rng`; глобальная переменная из `TranslationUnitDecl`; результат функции — вызванной (`f()`, `lines "f"`) или 0-аргументной команды (`ls`), которую шелл вызывает сам;
   - тип элемента диапазона (`elementTypeOf`): `value_type`, иначе `begin()` (указатель или `operator*` итератора), иначе первый аргумент шаблона `ClassTemplateSpecializationDecl`, у массива — элемент;
   - шаги цепочки: поле, статический член или метод (тип результата), с обходом публичных баз;
   - `auto`-типы результата выводятся `Sema::DeduceReturnType` под `SFINAETrap`, неполные специализации инстанцируются `isCompleteType` — диагностика не попадает в сессию;
   - `completeRecordMembers` обходит публичные базы (`RD->bases()`), показывает только `AS_public` поля и методы (включая шаблонные), без конструкторов, деструкторов и `__`-имён;
   - если AST не даёт типа (пайплайн через результат лямбды), остаётся прежняя эвристика `file_entry` / `line_entry`.
3. **Карточка команды (`ls` + `Tab`):** когда введённое имя — единственное оставшееся дополнение, выводится карточка (`commandCard`): сигнатуры всех перегрузок из AST, опции из record-параметра (`ls_opts`: `.all`, `.recursive`, `.dirs_only`, `.files_only`), поля элементов результата (`yields (file_entry)`: `.name`, `.ext`, `.size`, `.is_dir`) или поля результата (`returns (sh_result)`), и примеры вызова. Таблица команд (`commands()`) общая для списка дополнений и карточек.

Built and run by the user on their machine; this machine has no room for an llvm-project build.

## 4. Run-time values as compile-time values (staging)

Every argument cppsh specializes a call on is a value known as the call is compiled: a literal, a constant, a value read from `std::cin`, a `std::string` or a container. No `__builtin_constant_p`, and no requirement to split the input into REPL lines by hand.

### 4.1. Value specialization

- A call whose arguments evaluate to constants gets a specialization of the callee (`__cppsh_val_N`) whose parameters carry those values (`CppshParamValue`: `ParmVarDecl` → `APValue`; `CppshParamRebuild`: `ParmVarDecl` → `Expr`, for values that are not literal types: strings, containers, variants). Nothing is written into the parameters' default arguments or initializers.
- In the specialization, a plain `if` on a parameter folds (`TreeTransform`), so `ls {.files_only = true}` returns `ls_view<file_entry>` and `ls` returns the variant range.
- A variable a statement already run defined is read from JIT memory (`cppshRuntimeValueOf`), or rebuilt from a snapshot (`std::sh::__cppsh_snapshot`, registry `__cppsh_snapshot_of`) into an expression recreating it (`cppshRuntimeRebuildOf`). A C string is rebuilt as a string literal.

### 4.2. Staged input (top level)

An input of several top-level statements is probed in a fork of the shell (`cppshProbe`): the child compiles it with diagnostics off and reports, down a pipe, where a statement needs a value an earlier statement of the same input defines (`CppshStageAt` against `CppshTopLevelStarts`), and any call of a staged function to hoist. The session then compiles each piece exactly once: no undo (undo left the code generator's deferred declarations behind), no held diagnostics.

### 4.3. Staged functions

A function whose body needs a value only running it gives (a local read from `std::cin`, the result of another staged function) is cut there:

- **The cut.** The parser (or, for a function with `auto` parameters, the instantiation of its body: `TreeTransform::TransformCompoundStmt`) keeps the rest of the block as text, and the function returns `std::sh::__cppsh_cut(Id, std::sh::__cppsh_frame(live locals...))`, of type `staged`. The live locals are the variables in scope at the need, innermost of a name, up to the parameters, plus the iterators of the range-fors around it; their types fully qualified, `&&`-marked where they have no copy (moved).
- **The continuation.** `__cppsh_cut_run` compiles `__cppsh_contK(auto locals...)` with the remainder as its body, against reference globals `__cppsh_fK_x` bound to the frame, and keeps its result in `__cppsh_resK` (`std::sh::__cppsh_value`). The locals are value-specialized: the rest compiles with their values known. The result of a staging is that of the innermost continuation.
- **Callers.** A call of a staged function cuts its caller in turn; at the top level the call is hoisted, run on its own, and its result put in its place.
- **Nested blocks.** A need in a nested block is cut there; each block around it appends what follows its statement to the remainder (the inner rest braced; nothing after an inner rest that always returns) and cuts there too, so every way out of the function is staged alike.
- **Loops.** A need in a loop body is cut there. The continuation finishes the iteration in `do { ... } while (false)` (so `continue` works; an own `break` sets `__cppsh_brkN`), then calls `__cppsh_loopK(T &locals..., bool brk)`, which runs the loop on from its next step (`inc; for (; cond; inc) body`, `while (cond) body`, `++__begin; for (; __begin != __end; ++__begin) { decl = *__begin; body }`) and what follows it. Its locals are references, never constants, since the next iteration changes them; its body is parsed and its need cut again, so each iteration that reaches the need compiles once. When every cut in a loop was made for one local declared before it that the loop does not change (an AST walk), the cut is moved before the loop: one continuation for the whole loop.
- **switch.** The rest of the case and the cases it falls through to run in `do { ... } while (false)` with their labels dropped.
- **Refused, with a diagnostic:** a `return` before the need in the same block; a continuation whose first statement needs the value again (it would never progress); a structured binding as a range-for variable; a loop condition declaring a variable; an own `continue` in the rest of a switch.
- **Prompting.** `std::cin >> x` as typed reads through `std::sh::__cppsh_ask`, which shows `x? ` on stderr when stdin is a terminal.

## 5. External commands and jobs (`libcxx/include/sh`)

- **A command** is a word the shell does not know (`sym<...>`), applied to its arguments by juxtaposition: `git status`, `grep "x" f`. The words come from what was written: a string as it is, a number as written, an entry by its name, a range a word per element (`__cppsh_word`). The result is a `std::sh::command`, which runs when its full expression ends if nothing used it.
- **Uses.** `int s = cmd;` / `if (cmd)`: the exit status. `std::string out = cmd;`: its output, trailing newlines off. `for (auto l : cmd)`: its lines, streamed as it writes them (`line_entry`). `cmd.capture()`: `(status, output)`.
- **Pipes and redirects.** `a | b` is a `pipeline`, its stages run together, its status that of the last failing stage (pipefail). A range piped into a command feeds its stdin a line per element, on a thread of its own. `cmd > "f"`, `cmd >> "f"`, `cmd < "f"`, `cmd.err_to_out()` (`2>&1`). The status of the last run is `std::sh::last_status`.
- **Processes.** `posix_spawnp`, each pipeline in a process group of its own, with the signals the shell catches restored to default in it. The terminal is the group's while it runs in the foreground (`tcsetpgrp`), captured or not, so a password prompt or a pager reaches the user.
- **Jobs.** A foreground job stopped by Ctrl+Z is kept in the job table with its processes not reaped yet. `jobs` lists the table (`job_entry`: id, state, pgid, command) and reaps what ended (`Done`). `fg [n]` brings a job back: it's continued if stopped, gets the terminal, and is waited for. `bg [n]` continues a stopped job in the background. A trailing `&` in typed input (`sleep 10 &`, `a | b &`: the whole expression) becomes `std::sh::__cppsh_background(expr)`, which starts it as a job without waiting; `cmd | background` does the same.
- **Prompting.** `std::cin >> x` in typed input shows `x? ` when stdin is a terminal (`__cppsh_ask`).
