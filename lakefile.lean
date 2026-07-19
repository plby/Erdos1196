import Lake
open Lake DSL

package «Erdos1196» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib «Erdos1196» where

lean_lib «Challenge» where
