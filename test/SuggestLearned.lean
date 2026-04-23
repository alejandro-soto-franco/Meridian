/-
Smoke test for #meridian_suggest_learned. Exercises the command against a
server running on localhost:8765; if no server is running, the command logs a
warning and still elaborates cleanly.
-/
import Meridian.Analysis.SuggestLearned
open Meridian.Analysis.SuggestLearned

example : 1 + 1 = 2 := by
  #meridian_suggest_learned 3
  rfl
