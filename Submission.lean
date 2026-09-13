theorem foo : ∀ x : Nat, ∃ y : Nat, 1 + 1 = 2 := by
                     
  intro x; exists 0                   