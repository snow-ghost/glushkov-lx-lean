import LRX.PrunedExactService
import LRX.PrunedPartition

/-! Deleting canonical finite cycles away from the root preserves the root
port load. Thus the root discount remains available to the retained service. -/
namespace LRX.PrunedLift
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem positive_endpoint_passages (a b : Fin n) (ha : a ≠ 0) (hb : b ≠ 0) :
    PeriodicBuffer.edgePassages (n : ℤ) (a : ℤ) (b : ℤ)=0 := by
  have hdiv (i : Fin n) (hi : i ≠ 0) : -(i : ℤ)/(n : ℤ) = -1 := by
    have hn := i.isLt
    have hp := Fin.val_ne_zero_iff.mpr hi
    exact Int.ediv_eq_neg_one_of_neg_of_le (by omega) (by omega)
  simp only [PeriodicBuffer.edgePassages, hdiv a ha, hdiv b hb, sub_self, abs_zero]

theorem canonical_pruned_port_load (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S) :
    portLoad (displacement S (fun i => (p.symm i : ℤ)-(i : ℤ))) 0=
      portLoad (fun i => (p.symm i : ℤ)-(i : ℤ)) 0 := by
  simp only [portLoad, localDisplacement, Fin.val_zero, pow_zero, Equiv.Perm.one_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmem : i ∈ S
  · simp [displacement,hmem]
  · have hi0 : i ≠ 0 := by intro h; subst i; exact hmem hkeep
    have hp0 : p.symm i ≠ 0 := by
      intro h
      have hm : p.symm i ∈ S := by rw [h]; exact hkeep
      exact hmem ((inverse_mem_iff p S hS i).mp hm)
    simp only [displacement, ite_eq_right hmem, add_zero, add_sub_cancel,
      positive_endpoint_passages i (p.symm i) hi0 hp0]
    simp [PeriodicBuffer.edgePassages]

#print axioms canonical_pruned_port_load
end LRX.PrunedLift
