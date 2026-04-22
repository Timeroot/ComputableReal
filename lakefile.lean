import Lake
open Lake DSL

package «computableReal» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.29.1"

@[default_target]
lean_lib «ComputableReal» {
  -- add any library configuration options here
}
