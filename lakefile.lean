import Lake
open Lake DSL

package quantyra where
  -- Minimal Lean 4 package configuration.

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.13.0"

@[default_target]
lean_lib CertifiedAffine where
  srcDir := "lean"
