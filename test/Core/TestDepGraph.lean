import Meridian.Core.DepGraph

open Meridian.Core.SorryExtract
open Meridian.Core.DepGraph

-- Test declarations with known dependency structure
def baseValue : Nat := 42
theorem uses_base : baseValue = 42 := rfl
theorem sorry_uses_base : baseValue > 0 := sorry

-- Integration test
#dep_graph
