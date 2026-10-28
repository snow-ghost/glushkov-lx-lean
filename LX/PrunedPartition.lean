import LX.PrunedLift
import Mathlib

/-! The retained and removed unions of cycles partition both the permutation
and every integer displacement, with disjoint physical targets. -/
namespace LX.Core.PrunedLift
variable {n : ℕ}

theorem complement_invariant (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) : p i ∈ Sᶜ ↔ i ∈ Sᶜ := by simp [hS]

theorem permutation_disjoint (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) :
    (permutation p S hS).Disjoint (permutation p Sᶜ (complement_invariant p S hS)) := by
  intro i
  by_cases hi : i ∈ S
  · right; simp [hi]
  · left; simp [hi]

theorem permutation_partition (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) :
    permutation p S hS * permutation p Sᶜ (complement_invariant p S hS)=p := by
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ S
  · simp [Equiv.Perm.mul_apply,hi]
  · simp [Equiv.Perm.mul_apply,hi,hS]


#print axioms permutation_partition
end LX.Core.PrunedLift
