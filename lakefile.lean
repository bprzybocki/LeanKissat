import Lake
open Lake DSL

package "LeanKissat" where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩,
    ⟨`linter.extra.unreachableTactic, true⟩, ⟨`linter.extra.unnecessarySeqFocus, true⟩,
    ⟨`linter.extra.dupNamespace, true⟩]
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

lean_exe phasebench where
  root := `bench2.PhaseBench

lean_exe wordbench where
  root := `bench2.WordBench
