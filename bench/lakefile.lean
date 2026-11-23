import Lake
open Lake DSL
package bench where
  moreLeancArgs := #["-O3"]
@[default_target] lean_exe arrbench where root := `ArrBench
lean_exe structbench where root := `StructBench
