import LRX.LoadComponentSet

/-! Removing other load components preserves every load at a port belonging
to the retained component. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem arrow_passage_load_path (d : Fin n → ℤ) (i r : Fin n)
    (hp : 0 < PeriodicBuffer.edgePassages (n : ℤ) ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i)) :
    LoadPath d i r := by
  obtain ⟨k,hlo,hhi⟩ := passage_interval (show (0 : ℤ) < n by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)) hp
  have hrange : min (i : ℤ) ((i : ℤ)+d i) ≤ (r : ℤ)+k*(n : ℤ) ∧
      (r : ℤ)+k*(n : ℤ) ≤ max (i : ℤ) ((i : ℤ)+d i) := by omega
  have h := arrow_load_path d i ((r : ℤ)+k*(n : ℤ)) hrange
  simpa only [copy_cast] using h

theorem other_component_zero_passage (d : Fin n → ℤ) (start i r : Fin n)
    (hr : r ∈ component d start) (hi : i ∉ component d start) :
    PeriodicBuffer.edgePassages (n : ℤ) ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i)=0 := by
  by_contra hn
  have hnon : 0 ≤ PeriodicBuffer.edgePassages (n : ℤ) ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i) := abs_nonneg _
  have hp : 0 < PeriodicBuffer.edgePassages (n : ℤ) ((i : ℤ)-(r : ℤ)) ((i : ℤ)-(r : ℤ)+d i) := by omega
  have hir := arrow_passage_load_path d i r hp
  exact hi ((mem_component d start i).mpr (((mem_component d start r).mp hr).trans (load_path_symm d hir)))

theorem component_port_load (d : Fin n → ℤ) (start r : Fin n) (hr : r ∈ component d start) :
    RotationWords.portLoad (PrunedLift.displacement (component d start) d) r=RotationWords.portLoad d r := by
  classical
  rw [RotationWords.port_load_original,RotationWords.port_load_original]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ component d start
  · simp only [PrunedLift.displacement,ite_eq_left hi]
  · rw [other_component_zero_passage d start i r hr hi]
    simp only [PrunedLift.displacement,ite_eq_right hi,add_zero,PeriodicBuffer.edgePassages,sub_self,abs_zero]

#print axioms component_port_load
end LRX.CycleFootprint
