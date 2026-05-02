import Meridian.Core.ExportRdf

/-!
# TestExportRdf

End-to-end test of `#export_rdf_local`. Defines:

- a definition,
- a proven theorem (no sorry, no axiom),
- a sorry-bearing theorem (uses `sorryAx`),
- a theorem that explicitly uses `Classical.choice`,
- an inductive type with constructors and a recursor,
- an opaque definition,
- a structure with projections,
- a declaration whose name uses French quotes (forces percent-encoding).

Then runs the export and asserts on substrings that probe each of those
shapes individually.
-/

open Meridian.Core.ExportRdf

namespace MeridianTest.ExportRdf

-- A definition.
def baseConstant : Nat := 7

-- A proven theorem.
theorem baseConstantPos : baseConstant > 0 := by decide

-- A sorry-bearing theorem.
theorem baseConstantBig : baseConstant > 1000 := sorry

-- A theorem that explicitly uses Classical.choice.
noncomputable def someValue (P : Nat → Prop) (h : ∃ n, P n) : Nat :=
  Classical.choose h

-- An inductive type. Lean auto-generates constructors and a recursor.
inductive Tree (α : Type) where
  | leaf : Tree α
  | node : α → Tree α → Tree α → Tree α

-- An opaque definition.
opaque opaqueOne : Nat := 1

-- A structure with projections.
structure Pair (α β : Type) where
  fst : α
  snd : β

-- A declaration whose name forces percent-encoding via French quotes.
def «hard name» : Nat := 0

end MeridianTest.ExportRdf

private def testOutPath : String := "/tmp/meridian-test-export.ttl"

/-- Substring search using `splitOn`. The empty needle is treated as present. -/
private def hasSubstr (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

#export_rdf_local "/tmp/meridian-test-export.ttl"

-- Check that the dump contains the expected subjects, classes, and properties.
#eval show IO Unit from do
  let txt ← IO.FS.readFile testOutPath
  let mustContain : List String := [
    "@prefix mer:",
    "@prefix dct:",
    -- Subjects
    "MeridianTest.ExportRdf.baseConstant",
    "MeridianTest.ExportRdf.baseConstantPos",
    "MeridianTest.ExportRdf.baseConstantBig",
    "MeridianTest.ExportRdf.someValue",
    "MeridianTest.ExportRdf.Tree",
    "MeridianTest.ExportRdf.Tree.leaf",
    "MeridianTest.ExportRdf.Tree.node",
    "MeridianTest.ExportRdf.Pair",
    "MeridianTest.ExportRdf.opaqueOne",
    -- The French-quote brackets are syntactic; Lean's name representation is
    -- `hard name` (with a space). The space must be percent-encoded in the IRI.
    "MeridianTest.ExportRdf.hard%20name",
    -- Classes
    "mer:Definition",
    "mer:Theorem",
    "mer:Inductive",
    "mer:Constructor",
    "mer:OpaqueDef",
    -- Properties
    "mer:hasSorry \"true\"^^xsd:boolean",
    "mer:hasSorry \"false\"^^xsd:boolean",
    "mer:directlyDependsOn",
    "mer:typeSize",
    -- sorryAx and Classical.choice usage should populate mer:usesAxiom
    "mer:usesAxiom",
    -- Dump metadata block
    "a mer:Dump",
    "dct:source \"Lean ",
    "mer:declCount",
    "mer:moduleCount"
  ]
  for needle in mustContain do
    if !hasSubstr txt needle then
      throw <| IO.userError s!"export missing expected substring: {needle}"
  IO.println s!"export OK ({txt.length} bytes, {mustContain.length} substring assertions passed)"
