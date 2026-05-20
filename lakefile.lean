import Lake
open Lake DSL

package "pc_sast_lean" where
  version := v!"0.1.0"

lean_lib «PcSastLean» where
  -- add library configuration options here

@[default_target]
lean_exe "pc_sast_lean" where
  root := `Main
