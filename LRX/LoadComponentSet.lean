import LRX.LoadComponents
import LRX.ZeroCutBalance

/-! Physical load components are invariant under the permutation and closed
under all service paths. -/
namespace LRX.CycleFootprint
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

noncomputable def component (d : Fin n → ℤ) (start : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => LoadPath d start i)

@[simp] theorem mem_component (d : Fin n → ℤ) (start i : Fin n) :
    i ∈ component d start ↔ LoadPath d start i := by
  classical
  simp [component]

theorem component_invariant {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (start i : Fin n) : p i ∈ component d start ↔ i ∈ component d start := by
  have hp : LoadPath d (p i) i := by simpa using arrow_target_load_path hd (p i)
  simp only [mem_component]
  exact ⟨fun h => h.trans hp,fun h => h.trans (load_path_symm d hp)⟩

theorem service_edge_load_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {i j : Fin n} (he : BufferProgram.ServiceEdge p d i j) :
    LoadPath d i j := by
  rcases he with hc | ⟨_,k,hlo,hhi⟩
  · exact same_cycle_load_path hd hc
  · have hp := arrow_load_path d i ((j : ℤ)+k*(n : ℤ)) ⟨hlo,hhi⟩
    simpa only [copy_cast] using hp

theorem service_path_load_path {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) {i j : Fin n} (hp : PrunedLift.Reaches p d i j) : LoadPath d i j := by
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (service_edge_load_path hd he)

theorem component_keeps_core {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (start root : Fin n) (hr : root ∈ component d start) :
    PrunedLift.KeepsCore p d root (component d start) := by
  intro a hra _
  exact (mem_component d start a).mpr ((mem_component d start root).mp hr |>.trans (service_path_load_path hd hra))

theorem component_balanced {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (cut : Fin n) (hz : RotationWords.portLoad d cut=0)
    (start : Fin n) : (∑ i ∈ component d start, d i)=0 :=
  zero_cut_balance hd cut hz (component d start) (component_invariant hd start)

#print axioms component_invariant
#print axioms component_keeps_core
#print axioms component_balanced
end LRX.CycleFootprint
