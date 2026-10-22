import LRX.PrunedLoad
import LRX.ReflectedRootStar

/-! Canonical finite cycles strictly to the left of a root vertex do not
contribute to its left incident port. Pruning them preserves that discount. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem left_incident_no_passages (r a b : Fin n) (hr : r ≠ 0)
    (ha : a.val < r.val) (hb : b.val < r.val) :
    PeriodicBuffer.edgePassages (n : ℤ) ((a : ℤ)-((r-1 : Fin n) : ℤ))
      ((b : ℤ)-((r-1 : Fin n) : ℤ))=0 := by
  have hv : (r-1 : Fin n).val+1=r.val := by
    rw [Fin.val_sub_one_of_ne_zero hr]
    have := Fin.val_ne_zero_iff.mpr hr
    omega
  have hdiv (i : Fin n) (hi : i.val < r.val) :
      (-((i : ℤ)-((r-1 : Fin n) : ℤ)))/(n : ℤ)=0 := by
    have hn := r.isLt
    exact Int.ediv_eq_zero_of_lt (by omega) (by omega)
  simp only [PeriodicBuffer.edgePassages,hdiv a ha,hdiv b hb,sub_self,abs_zero]

theorem pruned_left_port_load (p : State n) (d : Fin n → ℤ) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (r : Fin n) (hr : r ≠ 0)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i, i ∉ S → i.val < r.val) :
    portLoad (displacement S d) (r-1)=portLoad d (r-1) := by
  rw [port_load_original,port_load_original]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : i ∈ S
  · simp [displacement,hm]
  · have hp : p.symm i ∉ S := by
      intro h
      exact hm ((inverse_mem_iff p S hS i).mp h)
    have he : (i : ℤ)-((r-1 : Fin n) : ℤ)+d i=
        (p.symm i : ℤ)-((r-1 : Fin n) : ℤ) := by rw [hfinite i hm]; ring
    rw [he,left_incident_no_passages r i (p.symm i) hr (hleft i hm) (hleft _ hp)]
    simp [displacement,hm,PeriodicBuffer.edgePassages]

#print axioms pruned_left_port_load
end LRX.PrunedLift
