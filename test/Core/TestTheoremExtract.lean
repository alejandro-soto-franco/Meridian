import Meridian.Core.TheoremExtract

/-- A documented theorem. -/
theorem documented_thm : 1 = 1 := rfl

theorem undocumented_sorry : 2 = 3 := sorry

#extract_theorems
