import Lake
open Lake DSL

package reyes_math where
  version := v!"0.1.0"

@[default_target]
lean_lib MathProofs

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.23.0"

-- Verified periodic cubic-quintic H² theory (PVNP PR #40).
-- Pin the audited revision rather than following a moving default branch.
require pvnp from git
  "https://github.com/rickyjreyes/PVNP" @ "924f7866ab991638153b19507dfbc72c4a1a69cf" / "lean"
