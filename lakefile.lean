import Lake
open Lake DSL

package ASCII

@[default_target]
lean_lib ASCII where
  precompileModules := true

require std from git
  "https://github.com/leanprover/std4" @ "main"
