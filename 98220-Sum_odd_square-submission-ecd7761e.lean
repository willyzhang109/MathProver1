import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring

/-- 
Computes the sum of the first `n` odd natural numbers: 1 + 3 + 5 + ... + (2n - 1).
-/
def sumOdd : ℕ → ℕ
  | 0     => 0
  | n + 1 => sumOdd n + (2 * n + 1)

/-- 
Lemma 1: Base case verification for the sum of odd numbers when n = 0.
-/
lemma sumOdd_zero : sumOdd 0 = 0^2 := by
                     
  rfl
                   

/-- 
Lemma 2: Algebraic step establishing that `n^2 + (2n + 1) = (n + 1)^2`.
-/
lemma odd_sum_succ_identity (n : ℕ) : n^2 + (2 * n + 1) = (n + 1)^2 := by
                     
  ring
                   

/-- 
Main Theorem: The sum of the first `n` odd numbers is equal to `n^2`.
-/
theorem sum_of_odds_eq_sq (n : ℕ) : sumOdd n = n^2 := by
                     
  induction n with
  | zero => exact sumOdd_zero
  | succ n ih =>
    simp [sumOdd, ih, odd_sum_succ_identity]
                   