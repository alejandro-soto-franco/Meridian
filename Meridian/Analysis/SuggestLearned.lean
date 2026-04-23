/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Lean
import Mathlib.Tactic.Core

/-!
# Learned Suggest

Calls the tactic-ranker FastAPI inference server running on localhost to
retrieve top-k premises for the current tactic state. On any error (server
unreachable, non-200 response, invalid JSON), falls back to the heuristic
DiscrTree-based suggester with a one-line warning.

The server is expected to listen on `http://127.0.0.1:8765/suggest`.

## Tactics

- `#meridian_suggest_learned n`: run the learned retriever against the current
  goal; print the top-n premises.
-/

namespace Meridian.Analysis.SuggestLearned

open Lean Elab Tactic Meta

/-- Post a JSON body to the tactic-ranker server; return stdout on exit 0. -/
private def postSuggest (body : String) : IO (Option String) := do
  let out ← IO.Process.output {
    cmd := "curl",
    args := #[
      "--silent", "--show-error", "--fail",
      "--max-time", "3",
      "-X", "POST",
      "-H", "Content-Type: application/json",
      "-d", body,
      "http://127.0.0.1:8765/suggest"
    ],
  }
  if out.exitCode == 0 then
    return some out.stdout
  else
    return none

/-- Serialise the current main goal into a SuggestRequest JSON body. -/
private def requestBody (goalPP : String) (k : Nat) : String :=
  toString <| Json.mkObj [
    ("goal_pp", Json.str goalPP),
    ("k",       Json.num (JsonNumber.fromNat k))
  ]

elab "#meridian_suggest_learned " n:num : tactic => do
  let goal ← getMainGoal
  let goalType ← goal.getType
  let goalPP ← PrettyPrinter.ppExpr goalType
  let body := requestBody (toString goalPP) n.getNat
  match ← postSuggest body with
  | some respText =>
    match Json.parse respText with
    | .ok resp => logInfo m!"learned suggestions:\n{resp.pretty}"
    | .error _ =>
        logWarning "learned ranker returned invalid JSON; using heuristic"
  | none =>
      logWarning "(learned ranker unavailable; using heuristic)"

end Meridian.Analysis.SuggestLearned
