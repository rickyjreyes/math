import Lake
open Lake DSL

package reyes_math where
  version := v!"0.1.0"

@[default_target]
lean_lib MathProofs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"
