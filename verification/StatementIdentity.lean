/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruiyi Zhang
-/
module

import Lean

/-!
# Statement identity for Theorem 1.1

This program checks that the theorem types in `Challenge` and `Solution`
display the quantifiers of Theorem 1.1 and match the retained definition.
It also compares the definitions of the radical and the triple hypotheses.
-/

open Lean

private def getDeclaration (env : Environment) (name : Name) : IO ConstantInfo :=
  match env.find? name with
  | some info => pure info
  | none => throw <| IO.userError s!"Missing declaration: {name}"

/-- Compare the two presentations of Theorem 1.1 and emit the identity report. -/
public def main (args : List String) : IO Unit := do
  let modules ← match args with
    | [] => pure (`Challenge, `Solution)
    | [first, second] => pure (first.toName, second.toName)
    | _ => throw <| IO.userError "Expected zero or two module names"
  let buildLibrary ← Lean.realPathNormalized ".lake/build/lib/lean"
  Lean.initSearchPath (← Lean.findSysroot) [buildLibrary]
  for mod in [modules.1, modules.2] do
    let resolved ← Lean.findOLean mod
    let expected := Lean.modToFilePath buildLibrary mod "olean"
    unless resolved.normalize == expected do
      throw <| IO.userError s!"Expected {mod} at {expected}, found {resolved}"
  let challenge ← Lean.importModules #[{ module := modules.1 }] {}
  let solution ← Lean.importModules #[{ module := modules.2 }] {}
  let statement := `AbcSubexp.subexpStatement
  let theoremName := `AbcSubexp.subexp
  let challengeTheorem ← getDeclaration challenge theoremName
  let solutionTheorem ← getDeclaration solution theoremName
  let restatementName := `AbcSubexp.Solution.subexp
  let restatement ← getDeclaration solution restatementName
  let definitions := #[`AbcTwoNinths.radNat, `AbcTwoNinths.TwoNinthsTriple, statement]
  for name in definitions do
    let challengeDefinition ← getDeclaration challenge name
    let solutionDefinition ← getDeclaration solution name
    let some body := challengeDefinition.value?
      | throw <| IO.userError s!"Expected a fixed definition: {name}"
    unless challengeDefinition.type == solutionDefinition.type &&
        some body == solutionDefinition.value? do
      throw <| IO.userError s!"Fixed definition differs: {name}"
  let preservedStatement ← getDeclaration solution statement
  for (label, info) in [("challenge theorem", challengeTheorem),
      ("library theorem", solutionTheorem), ("solution restatement", restatement)] do
    unless info.type.isForall do
      throw <| IO.userError s!"Expected a universal quantifier at the root of the {label} type"
    unless preservedStatement.value? == some info.type do
      throw <| IO.userError s!"The {label} type differs from the body of {statement}"
  IO.println <| (Json.mkObj [
    ("state", toJson "PASS_STATEMENT_AND_FIXED_DEFINITIONS"),
    ("challenge_module", toJson modules.1.toString),
    ("solution_module", toJson modules.2.toString),
    ("main_theorem", toJson theoremName.toString),
    ("solution_restatement", toJson restatementName.toString),
    ("challenge_solution_theorem_type_identical", toJson true),
    ("all_theorem_types_begin_with_forall", toJson true),
    ("all_theorem_types_equal_preserved_statement_body", toJson true),
    ("fixed_definition_bodies_identical", toJson (definitions.map Name.toString))]).pretty
