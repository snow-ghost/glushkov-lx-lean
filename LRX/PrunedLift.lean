import LRX.ReachableService

/-! Restrict a permutation and its lift to an invariant union of cycles.
Balance of the retained lift is stated separately from invariance. -/
namespace LRX.PrunedLift
open scoped BigOperators
variable {n : ℕ}

def permutation (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) : State n where
  toFun i := if i ∈ S then p i else i
  invFun i := if i ∈ S then p.symm i else i
  left_inv i := by
    by_cases hi : i ∈ S
    · simp [hi, (hS i).mpr hi]
    · simp [hi]
  right_inv i := by
    by_cases hi : i ∈ S
    · have hm : p.symm i ∈ S := (hS (p.symm i)).mp (by simpa using hi)
      simp [hi, hm]
    · simp [hi]

def displacement (S : Finset (Fin n)) (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  if i ∈ S then d i else 0

@[simp] theorem permutation_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    permutation p S hS i=if i ∈ S then p i else i := rfl

@[simp] theorem permutation_symm_apply (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) :
    (permutation p S hS).symm i=if i ∈ S then p.symm i else i := rfl

theorem is_lift {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (S : Finset (Fin n)) (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hbalance : ∑ i ∈ S, d i=0) :
    AffineLift.IsLift (permutation p S hS) 0 (displacement S d) := by
  constructor
  · simpa [displacement] using hbalance
  · intro i
    by_cases hi : i ∈ S
    · simpa [displacement, hi] using hd.2 i
    · simp [displacement, hi]

theorem short {d : Fin n → ℤ} (hshort : ∀ i, |d i| < (n : ℤ))
    (S : Finset (Fin n)) (i : Fin n) : |displacement S d i| < (n : ℤ) := by
  by_cases hi : i ∈ S
  · simpa [displacement, hi] using hshort i
  · have hn := i.isLt
    simp [displacement, hi]
    omega

#print axioms is_lift
end LRX.PrunedLift
