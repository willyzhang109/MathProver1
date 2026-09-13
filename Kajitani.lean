import Mathlib.Data.Matroid.Basic
import Mathlib.Data.List.Cycle

open Set Matroid

variable {α : Type*} [DecidableEq α]

/-- 
A matroid is cyclically orderable if there exists a cyclic ordering of its ground set 
such that every consecutive subsequence of length equal to the rank of the matroid is a basis.
-/
def IsCyclicallyOrderable (M : Matroid α) [Finite M.E] : Prop :=
  ∃ (cyc : Cycle α), 
    cyc.support.toFinset = M.E.toFinset ∧ 
    ∀ (xs : List α), xs.Sublist cyc.coe → xs.length = M.r M.E → M.Basis (xs.toFinset) M.E

/-- 
A matroid is uniformly dense if for all subsets X of its ground set,
the size of the ground set times the rank of X is at least the total rank times the size of X.
-/
def IsUniformlyDense (M : Matroid α) [Finite M.E] : Prop :=
  ∀ (X : Set α), X ⊆ M.E → 
    (Nat.card M.E) * (M.r X) ≥ (M.r M.E) * (Nat.card X)

/-- 
The Kajitani Conjecture (Kajitani, Ueno, Miyano 1988):
For any finite matroid, being uniformly dense is equivalent to being cyclically orderable.
-/
conjecture kajitani_conjecture (M : Matroid α) [Finite M.E] :
    IsUniformlyDense M ↔ IsCyclicallyOrderable M := by
  sorry