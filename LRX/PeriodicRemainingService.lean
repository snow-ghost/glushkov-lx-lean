import LRX.FiniteRemovalBalance
import LRX.PrunedLoad

/-! The full root lift may be periodic. Removing canonical finite leaf cycles
preserves both balance and its original root-port load. -/
namespace LRX.PrunedLift
open scoped BigOperators
open RotationWords
variable {n : ℕ} [NeZero n]

theorem port_load_of_finite_removal (p : State n) (d : Fin n → ℤ) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ)) :
    portLoad (displacement S d) 0=portLoad d 0 := by
  simp only [portLoad,localDisplacement,Fin.val_zero,pow_zero,Equiv.Perm.one_apply]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hmem : i ∈ S
  · simp [displacement,hmem]
  · have hi0 : i ≠ 0 := by intro h; subst i; exact hmem hkeep
    have hp0 : p.symm i ≠ 0 := by
      intro h
      have hm : p.symm i ∈ S := by rw [h]; exact hkeep
      exact hmem ((inverse_mem_iff p S hS i).mp hm)
    rw [hfinite i hmem]
    simp only [displacement,ite_eq_right hmem,add_zero,add_sub_cancel,
      positive_endpoint_passages i (p.symm i) hi0 hp0]
    simp [PeriodicBuffer.edgePassages]

theorem periodic_remaining_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : RootStar p d 0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : (0 : Fin n) ∈ S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ)) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad d 0 := by
  obtain ⟨a,hp,ht,hdisp,hprice⟩ := exists_pruned_exact_service hn hd hshort hroot hstar S hS hkeep
    (balance_of_finite_removal hd S hS hfinite)
  rw [port_load_of_finite_removal p d S hS hkeep hfinite] at hprice
  exact ⟨a,hp,ht,hdisp,hprice⟩

#print axioms port_load_of_finite_removal
#print axioms periodic_remaining_service
end LRX.PrunedLift
