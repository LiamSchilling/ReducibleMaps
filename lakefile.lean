import Lake
open Lake DSL

package ReducibleMaps

@[default_target]
lean_lib ReducibleMaps

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

require checkdecls from git
  "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"
