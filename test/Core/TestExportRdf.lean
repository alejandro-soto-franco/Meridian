import Meridian.Core.ExportRdf

/-!
# TestExportRdf

End-to-end test of `#export_rdf_local`: defines a handful of declarations with
known structure (definition, theorem, sorry-bearing theorem with axiom usage),
emits Turtle to a temp file, reads it back, and asserts on key substrings.
-/

open Meridian.Core.ExportRdf

namespace MeridianTest.ExportRdf

-- A definition.
def baseConstant : Nat := 7

-- A proven theorem (no sorry, no axiom).
theorem baseConstantPos : baseConstant > 0 := by decide

-- A sorry-bearing theorem.
theorem baseConstantBig : baseConstant > 1000 := sorry

end MeridianTest.ExportRdf

private def testOutPath : String := "/tmp/meridian-test-export.ttl"

/-- Substring search using `splitOn`. The empty needle is treated as present. -/
private def hasSubstr (haystack needle : String) : Bool :=
  needle.isEmpty || (haystack.splitOn needle).length > 1

#export_rdf_local "/tmp/meridian-test-export.ttl"

-- Check that the dump contains the expected subjects and properties.
#eval show IO Unit from do
  let txt ← IO.FS.readFile testOutPath
  let mustContain : List String := [
    "@prefix mer:",
    "MeridianTest.ExportRdf.baseConstant",
    "MeridianTest.ExportRdf.baseConstantPos",
    "MeridianTest.ExportRdf.baseConstantBig",
    "mer:Definition",
    "mer:Theorem",
    "mer:hasSorry \"true\"^^xsd:boolean",
    "mer:hasSorry \"false\"^^xsd:boolean",
    "mer:directlyDependsOn",
    "mer:typeSize"
  ]
  for needle in mustContain do
    if !hasSubstr txt needle then
      throw <| IO.userError s!"export missing expected substring: {needle}"
  IO.println s!"export OK ({txt.length} bytes, {mustContain.length} substring assertions passed)"
