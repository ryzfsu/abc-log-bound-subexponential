/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

public import Subexp
meta import Lean

/-! # The type and axioms of the subexponential radical bound -/

run_cmd do
  let info ← Lean.getConstInfo `AbcSubexp.subexp
  let statement ← Lean.getConstInfo `AbcSubexp.subexpStatement
  unless info.type.isForall && statement.value? == some info.type do
    throwError "Expected the inlined universal statement of Theorem 1.1"

#print axioms AbcSubexp.subexp
