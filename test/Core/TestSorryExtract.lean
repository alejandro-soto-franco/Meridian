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

-- Test CoverageResult construction
run_cmd do
  let cov : CoverageResult := {
    category := .C
    exactMatches := []
    nearMisses := []
  }
  if cov.category != .C then throwError "category should be C"
  logInfo "CoverageResult: OK"

-- Regression: collectDeps must be DAG-aware, not exponential on shared subterms.
-- Lean `Expr` is a hash-consed DAG with maximal sharing; a naive structural
-- walk that recurses into both children of every `.app` revisits shared nodes
-- 2^depth times. We build `eₙ` with `e₀ = .const Nat.zero` and `eₙ₊₁ = .app eₙ eₙ`
-- (both children the SAME node), so a memoised walk visits `depth` nodes while a
-- naive walk visits ~2^depth. The dep set is `{Nat.zero}` regardless of depth.
run_cmd do
  let depth := 26
  let mut e : Lean.Expr := .const ``Nat.zero []
  for _ in [0:depth] do
    e := .app e e
  -- A bare `let deps := collectDeps e` is lazy and the walk would run outside
  -- the timing window; `IO.lazyPure` forces the full computation here.
  let t0 ← IO.monoMsNow
  let sz ← IO.lazyPure (fun _ => (collectDeps e).size)
  let dt := (← IO.monoMsNow) - t0
  if sz != 1 then
    throwError s!"collectDeps must return exactly the one dep \{Nat.zero}, got {sz}"
  if dt > 1000 then
    throwError s!"collectDeps is exponential on a shared DAG: {dt} ms at depth {depth} \
      (a DAG-aware walk is sub-millisecond)"
  logInfo s!"collectDeps shared-DAG: OK ({dt} ms)"

-- Integration test: #sorry_extract should run without error
#sorry_extract
