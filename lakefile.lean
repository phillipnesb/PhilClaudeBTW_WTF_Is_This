import Lake
open Lake DSL

package «formal_proof» where
  -- Standalone Lean 4 package with zero external dependencies

@[default_target]
lean_exe «verify_proof» where
  root := `proof
