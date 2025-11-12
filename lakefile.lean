import Lake
open Lake DSL

package "cs4410sp19" where
  version := v!"0.1.0"

lean_lib «Cs4410sp19» where
  -- add library configuration options here

@[default_target]
lean_exe "cs4410sp19" where
  root := `Main
