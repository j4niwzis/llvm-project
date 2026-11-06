set( LLVM_LINK_COMPONENTS
  ${LLVM_TARGETS_TO_BUILD}
  Core
  LineEditor
  Option
  Support
  TargetParser
  )

add_clang_tool(cppsh
  CppSh.cpp

  EXPORT_SYMBOLS
  )

if(EMSCRIPTEN)
  target_link_options(cppsh PRIVATE
    "-fwasm-exceptions"
    "SHELL:-s MAIN_MODULE=1"
    "LINKER:--export=__clang_Interpreter_SetValueWithAlloc"
    "LINKER:--export=__clang_Interpreter_SetValueNoAlloc"
    "LINKER:--export=_ZnwmPv26__clang_Interpreter_NewTag"
  )
endif()

if(MSVC)
  set_target_properties(cppsh PROPERTIES WINDOWS_EXPORT_ALL_SYMBOLS 1)
endif(MSVC)

clang_target_link_libraries(cppsh PRIVATE
  clangAST
  clangBasic
  clangFrontend
  clangInterpreter
  )

set(flag_long_plt "LINKER:--long-plt")
check_linker_flag(CXX ${flag_long_plt} HAVE_LINKER_FLAG_LONG_PLT)
if(HAVE_LINKER_FLAG_LONG_PLT)
  target_link_options(cppsh PRIVATE ${flag_long_plt})
endif()
