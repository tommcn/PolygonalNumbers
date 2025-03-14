import Lake
open Lake DSL

package "PolygonalNumbers" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «PolygonalNumbers» where
  -- add any library configuration options here

-- https://github.com/PatrickMassot/checkdecls
require checkdecls from git "https://github.com/urkud/checkdecls" @ "YK-fix-superscript"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- Custom files
lean_lib PolygonalNumbers.Polygonal
lean_lib PolygonalNumbers.Lemmas
