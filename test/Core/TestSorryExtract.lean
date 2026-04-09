import Meridian.Core.SorryExtract

open Lean Elab Command
open Meridian.Core.SorryExtract

-- Test declarations
theorem proved_thm : 1 + 1 = 2 := rfl
theorem sorry_thm : 2 + 2 = 4 := sorry
def no_sorry_def : Nat := 42
noncomputable def partial_sorry : Nat × Nat := (1, sorry)

-- Test containsSorry
run_cmd do
  let env ← getEnv
  match env.find? `sorry_thm with
  | some ci =>
    match ci.value? with
    | some v =>
      if !containsSorry v then throwError "sorry_thm should contain sorry"
    | none   => throwError "sorry_thm has no value"
  | none => throwError "sorry_thm not found"
  match env.find? `proved_thm with
  | some ci =>
    match ci.value? with
    | some v =>
      if containsSorry v then throwError "proved_thm should not contain sorry"
    | none   => throwError "proved_thm has no value"
  | none => throwError "proved_thm not found"
  logInfo "containsSorry: OK"

-- Test collectSorryGoals
run_cmd do
  let env ← getEnv
  match env.find? `sorry_thm with
  | some ci =>
    match ci.value? with
    | some v =>
      let goals := collectSorryGoals v
      if goals.isEmpty then throwError "sorry_thm should have sorry goals"
    | none => throwError "no value"
  | none => throwError "not found"
  logInfo "collectSorryGoals: OK"

-- Test collectDeps
run_cmd do
  let env ← getEnv
  match env.find? `proved_thm with
  | some ci =>
    let deps := collectDeps ci.type
    if !deps.contains ``Eq then throwError "proved_thm type should reference Eq"
    if !deps.contains ``Nat then throwError "proved_thm type should reference Nat"
  | none => throwError "not found"
  logInfo "collectDeps: OK"

-- Test extractAllDeclsNoCoverage
run_cmd do
  let decls ← extractAllDeclsNoCoverage
  let sorryDecls := decls.filter (·.hasSorry)
  if sorryDecls.isEmpty then throwError "should find sorry-containing decls"
  let names := sorryDecls.map (·.name)
  if !names.contains `sorry_thm then throwError "should find sorry_thm"
  logInfo s!"extractAllDeclsNoCoverage: OK ({decls.length} decls, {sorryDecls.length} with sorry)"
