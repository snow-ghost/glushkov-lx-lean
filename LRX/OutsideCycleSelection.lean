import LRX.OutsideCycleServiceFamily
import LRX.PacketRetainedIncidentService

namespace LRX.ZeroGap
open RotationWords
variable {n : ℕ} [NeZero n]

theorem outside_selected_part {p : State n} {d : Fin n → ℤ} (cycles : List (State n))
    (hdis : cycles.Pairwise Equiv.Perm.Disjoint) (hc : ∀ q ∈ cycles, q ∈ outsideCycles p d 0) :
    CyclePart.IsPart (cycles.map (fun q => q⁻¹)).prod p := by
  apply CyclePart.product _ p (FiniteCuts.inverse_targets_disjoint cycles hdis)
  intro t ht
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
  simpa only [inv_inv] using CyclePart.inverse
    (CyclePart.cycle_factor (Finset.mem_filter.mp (hc q hq)).1)

theorem outside_selected_keeps_core {p : State n} {d : Fin n → ℤ} (cycles : List (State n))
    (hc : ∀ q ∈ cycles, q ∈ outsideCycles p d 0) :
    PrunedLift.KeepsCore p d 0 (cycles.map (fun q => q⁻¹)).prod.supportᶜ := by
  classical
  intro i hforward hback
  apply Finset.mem_compl.mpr
  intro hi
  obtain ⟨t,ht,hit⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod hi
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp ht
  have hiq : i ∈ q.support := by simpa only [Equiv.Perm.support_inv] using hit
  exact Finset.disjoint_left.mp (outside_cycle_avoids_core (hc q hq)) hiq
    ((PrunedLift.mem_core p d 0 i).mpr ⟨hforward,hback⟩)

theorem outside_selected_canonical {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (cycles : List (State n)) (hdis : cycles.Pairwise Equiv.Perm.Disjoint)
    (hc : ∀ q ∈ cycles, q ∈ outsideCycles p d 0) :
    ∀ i ∈ (cycles.map (fun q => q⁻¹)).prod.support,
      d i=(((cycles.map (fun q => q⁻¹)).prod.symm i : ℤ)-(i : ℤ)) := by
  intro i hi
  have hkeep := outside_selected_keeps_core cycles hc
  have hout : ¬PrunedLift.InCore p d 0 i := fun h =>
    (Finset.mem_compl.mp (hkeep i h.1 h.2)) hi
  have hcan := PrunedLift.outside_core_canonical hd hcover hroot i hout
  rw [CyclePart.inverse_on_support _ p (outside_selected_part cycles hdis hc) i hi] at hcan
  exact hcan

#print axioms outside_selected_part
#print axioms outside_selected_keeps_core
#print axioms outside_selected_canonical
end LRX.ZeroGap
