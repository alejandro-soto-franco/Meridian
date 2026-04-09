import Meridian.Core.Disprove

-- A false proposition
theorem false_claim : ∀ n : Nat, n < 5 := sorry

-- A true proposition
theorem true_claim : ∀ n : Nat, n = n := sorry

#disprove false_claim
#disprove true_claim
