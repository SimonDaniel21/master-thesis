import Lake
open Lake DSL

package «default» where
--   lean

  -- add package configuration options here


lean_lib «Meeting_12_02» where
  leanOptions := #[⟨`relaxedAutoImplicit, false⟩]

lean_lib «chorlean» where
lean_lib «Test» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
require socket from git
  "https://github.com/SimonDaniel21/socket.lean" @ "main"
--  "https://github.com/xubaiw/lean4-socket.git"

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4.git"


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

lean_exe silent_post2 where
  root := `chorlean.examples.silent_post2
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true


lean_exe bookseller where
  root := `chorlean.examples.bookseller
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe bookseller2 where
  root := `chorlean.examples.bookseller2
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe bookseller3 where
  root := `chorlean.examples.bookseller3
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe bookseller4 where
  root := `chorlean.examples.bookseller4
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe auth where
  root := `chorlean.examples.sso_auth
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe merge where
  root := `chorlean.examples.mergesort
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

lean_exe play where
  root := `Meeting_12_02.playground6
  moreLeancArgs := #["-fPIC"]
  supportInterpreter := true

-- package foo where
--   dependencies := #[{
--     name := `socket
--     src := Source.git "https://github.com/xubaiw/lean4-socket.git" "main"
--   }]
