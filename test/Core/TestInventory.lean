import Meridian.Core.Inventory

def inv_base : Nat := 42
theorem inv_sorry1 : inv_base > 0 := sorry
theorem inv_sorry2 : inv_base < 100 := sorry
theorem inv_proved : inv_base = 42 := rfl

#sorry_inventory
