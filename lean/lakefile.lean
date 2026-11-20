/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

import Lake

/-! # Package configuration for the subexponential bound -/

open Lake DSL

package «a-subexponential-upper-bound-for-log-c-in-the-abc-conjecture» where
  moreLeanArgs := if (get_config? strict).isSome then #["-DwarningAsError=true"] else #[]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "25e572b8074098af3f09d4cb2a4231cbdc584534"

lean_lib AbcTwoNinths where
  roots := #[`AbcTwoNinths]
  globs := #[.submodules `AbcTwoNinths]

@[default_target]
lean_lib Subexp where
  roots := #[`Subexp, `Solution]
  globs := #[.andSubmodules `Subexp, .one `Solution]

lean_lib Challenge
