/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Lake
open Lake DSL

require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.32.0"
require genl from ".."

package GenlBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib GenlBlueprint where
