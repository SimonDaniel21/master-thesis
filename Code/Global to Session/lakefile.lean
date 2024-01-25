import Lake
open Lake DSL

package «test» where

  -- add package configuration options here

lean_lib «chorlean» where
lean_lib «Test» where
  -- add library configuration options here
require socket from git
  "https://github.com/hargoniX/socket.lean/" @ "main"
--  "https://github.com/xubaiw/lean4-socket.git"

@[default_target]
lean_exe «test» where
  root := `Main
  moreLeancArgs := #["-fPIC"]
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_exe generated where
  root := `DemoTest
  moreLeancArgs := #["-fPIC"]
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_exe prog_gen where
  root := `Test.ProgramGeneration
  moreLeancArgs := #["-fPIC"]
  -- Enables the use of the Lean interpreter by the executable (e.g.,
  -- `runFrontend`) at the expense of increased binary size on Linux.
  -- Remove this line if you do not need such functionality.
  supportInterpreter := true

lean_exe network where
  root := `chorlean.Network
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe choreo where
  root := `chorlean.Choreo
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe silent_post where
  root := `chorlean.examples.silent_post
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe bookseller where
  root := `chorlean.examples.bookseller
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

-- package foo where
--   dependencies := #[{
--     name := `socket
--     src := Source.git "https://github.com/xubaiw/lean4-socket.git" "main"
--   }]
