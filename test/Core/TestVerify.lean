import Meridian.Core.Verify

theorem verify_target : 1 + 1 = 2 := sorry
theorem verify_target2 : ∀ n : Nat, n = n := sorry

-- Should succeed
#verify_proof verify_target rfl
#verify_proof verify_target2 (fun n => rfl)
