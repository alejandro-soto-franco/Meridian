/-
Copyright 2026 Alejandro Jose Soto Franco. Licensed under Apache 2.0.
-/
import Meridian.Core.SorryExtract
import Plausible

/-!
# Counterexample Search

Attempt to find a counterexample for a declaration using Plausible (property-based
testing). Sanity check before spending hours on a sorry that is actually false.

## Commands

- `#disprove declName`: search for counterexamples
-/

namespace Meridian.Core.Disprove

open Lean Elab Command Term Meta
open Meridian.Core.SorryExtract

/-! ## Types -/

inductive DisproveResult where
  | counterexampleFound (description : String)
  | noCounterexample
  | untestable (reason : String)
  deriving Inhabited, Repr

instance : ToString DisproveResult where
  toString
    | .counterexampleFound d => s!"COUNTEREXAMPLE FOUND:\n{d}"
    | .noCounterexample      => "No counterexample found"
    | .untestable r          => s!"UNTESTABLE: {r}"

/-! ## Commands -/

/-- `#disprove declName` attempts to find a counterexample using Plausible.
    Internally delegates to Plausible's `Testable.check` by elaborating a synthetic
    `#check_failure` style term. -/
elab "#disprove" declName:ident : command => do
  let name := declName.getId
  let env ← getEnv
  match env.find? name with
  | none => throwError "Declaration '{name}' not found"
  | some ci =>
    -- Delab the type, construct `Plausible.Testable.check <type>`, elaborate, and
    -- run via unsafe native evaluation
    let typeStx ← liftTermElabM <| PrettyPrinter.delab ci.type
    let termStx ← `(Plausible.Testable.check $typeStx)
    -- Elaborate `#eval`-style: capture messages rather than letting them escape
    let savedMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    let cmdStx ← `(command| #eval $termStx)
    elabCommand cmdStx
    let newMsgs ← modifyGet fun st => (st.messages, { st with messages := savedMsgs })
    -- Check if any message contains a counter-example
    let msgList := newMsgs.toList
    let mut foundCounter := false
    for msg in msgList do
      let txt ← msg.data.toString
      if (txt.splitOn "Found a counter-example").length > 1 then
        logInfo s!"COUNTEREXAMPLE FOUND:\n{txt}"
        foundCounter := true
    if !foundCounter then
      -- Check if there are error messages (untestable)
      let errors := msgList.filter (·.severity == .error)
      if !errors.isEmpty then
        let errTxt ← (errors.head!).data.toString
        logInfo s!"UNTESTABLE: {errTxt}"
      else
        logInfo "No counterexample found (Plausible check passed)"

end Meridian.Core.Disprove
