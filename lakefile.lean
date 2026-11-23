import Lake
open Lake DSL

package "LeanKissat" where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]
  moreLeancArgs := #["-O3"]

require batteries from git
  "https://github.com/leanprover-community/batteries.git" @ "v4.36.0"

@[default_target]
lean_lib «LeanKissat» where

lean_exe «lkissat» where
  root := `Main

lean_exe «unittest» where
  root := `Test.Unit

lean_exe «sorttest» where
  root := `Test.Sort

lean_exe scanbench where
  root := `bench2.ScanBench
