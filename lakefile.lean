/- Assembled by Axiom Prover. -/
import Lake
open Lake DSL

package spt_cm_formalization where
  version := v!"1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.35.0-rc2"

@[default_target]
lean_lib SptCM where
  srcDir := "."
  roots := #[`blessed.SptCM]

lean_lib Palomar where
  roots := #[`Challenge, `Solution]
