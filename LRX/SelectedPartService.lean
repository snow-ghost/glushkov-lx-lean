import LRX.CyclePartSelection
import LRX.PeriodicRemainingService

/-! Exact removal and service of a selected finite part of a periodic lift. -/
namespace LRX.CyclePart
open scoped BigOperators
open RotationWords
variable {n : ℕ}

theorem displacement_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    PrunedLift.displacement selected.supportᶜ d i+
      ((selected.symm i : ℤ)-(i : ℤ))=d i := by
  by_cases hi : i ∈ selected.support
  · simp [PrunedLift.displacement,hi,hfinite i hi]
  · have hf : selected i=i := Equiv.Perm.notMem_support.mp hi
    have hfi : selected.symm i=i := by apply selected.injective; simpa using hf.symm
    simp [PrunedLift.displacement,hi,hfi]

theorem absolute_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) (i : Fin n) :
    |PrunedLift.displacement selected.supportᶜ d i|+
      |(selected.symm i : ℤ)-(i : ℤ)|=|d i| := by
  by_cases hi : i ∈ selected.support
  · simp [PrunedLift.displacement,hi,hfinite i hi]
  · have hf : selected i=i := Equiv.Perm.notMem_support.mp hi
    have hfi : selected.symm i=i := by apply selected.injective; simpa using hf.symm
    simp [PrunedLift.displacement,hi,hfi]

theorem mass_split (selected : State n) (d : Fin n → ℤ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) :
    (∑ i, |PrunedLift.displacement selected.supportᶜ d i|)+
      (∑ i, |(selected.symm i : ℤ)-(i : ℤ)|)=∑ i, |d i| := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => absolute_split selected d hfinite i)

variable [NeZero n]

theorem selected_part_root_service (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (hpart : IsPart selected p) (hfix : selected 0=0)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=remaining selected p hpart ∧
      a.displacement=PrunedLift.displacement selected.supportᶜ d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d 0 := by
  have hS := PrunedLift.complement_invariant p selected.support (support_invariant selected p hpart)
  have hkeep : (0 : Fin n) ∈ selected.supportᶜ := by simp [hfix]
  apply PrunedLift.periodic_remaining_service hn hd hshort hroot hstar selected.supportᶜ hS hkeep
  intro i hi
  have hm : i ∈ selected.support := by simpa using hi
  rw [inverse_on_support selected p hpart i hm]
  exact hfinite i hm

#print axioms displacement_split
#print axioms mass_split
#print axioms selected_part_root_service
end LRX.CyclePart
