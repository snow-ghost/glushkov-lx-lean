import LRX.ComponentCutBlockCount
import LRX.PrefixCoreEnergy

namespace LRX.FiniteCuts
open RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem source_packets_recenter (p : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r =
      displacement (localTarget p 0 r).symm) (i : Fin n) :
    i ∈ sourcePackets (localTarget p 0 r) ↔ rotation r i ∈ sourcePackets p := by
  have hp (a b : Fin n) : FiniteReach (localTarget p 0 r) a b ↔
      FiniteReach p (rotation r a) (rotation r b) := by
    change PrunedLift.Reaches _ _ _ _ ↔ PrunedLift.Reaches _ _ _ _
    rw [← hcan]
    exact reaches_recenter p (displacement p.symm) r
  simp only [mem_source_packets,SourceVertex]
  have hm : (localTarget p 0 r).symm i ≠ i ↔
      p.symm (rotation r i) ≠ rotation r i := moving_recenter p r i
  rw [hm]
  constructor
  · rintro ⟨hi,hs⟩
    refine ⟨hi,?_⟩
    intro j hj
    obtain ⟨a,rfl⟩ := (rotation r).surjective j
    exact (hp i a).mp (hs a ((hp a i).mpr hj))
  · rintro ⟨hi,hs⟩
    exact ⟨hi,fun j hj => (hp i j).mpr (hs _ ((hp j i).mp hj))⟩

theorem source_target_displacement_recenter (p : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r =
      displacement (localTarget p 0 r).symm) :
    displacement (sourceTarget (localTarget p 0 r)).symm =
      localDisplacement (displacement (sourceTarget p).symm) r := by
  classical
  funext i
  simp only [localDisplacement,source_target_displacement]
  have hs := source_packets_recenter p r hcan i
  have hd := congrFun hcan i
  change (if i ∈ sourcePackets (localTarget p 0 r) then
    displacement (localTarget p 0 r).symm i else 0) =
    (if rotation r i ∈ sourcePackets p then displacement p.symm (rotation r i) else 0)
  exact if_congr hs hd.symm rfl

theorem left_peak_le_of_port_bound (p : State n) (K : ℕ)
    (hb : ∀ i : Fin n, halfLoad p (i.val+1) ≤ K) : leftPeak p n ≤ K := by
  apply Finset.sup_le
  intro e he
  have he' : e ≤ n := by
    have := Finset.mem_range.mp he
    omega
  by_cases hz : e=0
  · simp [hz]
  · simpa only [Nat.sub_add_cancel (show 1 ≤ e by omega)] using
      hb ⟨e-1,by omega⟩

theorem left_peak_eq_of_recentered_load (p q : State n) (r : Fin n)
    (hload : ∀ i : Fin n, portLoad (displacement q) i =
      portLoad (displacement p) (i+r)) : leftPeak q n=leftPeak p n := by
  apply Nat.le_antisymm
  · apply left_peak_le_of_port_bound
    intro i
    have he := hload i
    rw [port_load_eq_twice_half,port_load_eq_twice_half] at he
    have hb : halfLoad p ((i+r).val+1) ≤ leftPeak p n :=
      Finset.le_sup (Finset.mem_range.mpr (by have := (i+r).isLt; omega))
    omega
  · apply left_peak_le_of_port_bound
    intro i
    have he := hload (i-r)
    rw [sub_add_cancel,port_load_eq_twice_half,port_load_eq_twice_half] at he
    have hb : halfLoad q ((i-r).val+1) ≤ leftPeak q n :=
      Finset.le_sup (Finset.mem_range.mpr (by have := (i-r).isLt; omega))
    omega

theorem source_half_peak_recenter (p : State n) (r : Fin n)
    (hcan : localDisplacement (displacement p.symm) r =
      displacement (localTarget p 0 r).symm) :
    sourceHalfPeak (localTarget p 0 r)=sourceHalfPeak p := by
  apply left_peak_eq_of_recentered_load _ _ r
  intro i
  rw [source_target_displacement_recenter p r hcan,port_load_recenter]

theorem component_cut_canonical_displacement (p : State n) (root : Fin n) :
    localDisplacement (displacement p.symm) (componentLeft p root) =
      displacement (localTarget p 0 (componentLeft p root)).symm := by
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hh := phase_zero_cut_canonical 0 (componentLeft p root-1) hd
    (component_left_port_zero p root)
  simpa only [sub_add_cancel] using hh

theorem component_cut_source_half_peak (p : State n) (root : Fin n) :
    sourceHalfPeak (localTarget p 0 (componentLeft p root))=sourceHalfPeak p :=
  source_half_peak_recenter p _ (component_cut_canonical_displacement p root)

theorem component_cut_displacement_mass (p : State n) (root : Fin n) :
    (∑ i, |displacement (localTarget p 0 (componentLeft p root)).symm i|) =
      ∑ i, |displacement p.symm i| := by
  rw [← component_cut_canonical_displacement]
  exact local_displacement_mass _ _

#print axioms component_cut_source_half_peak
#print axioms component_cut_displacement_mass
end LRX.FiniteCuts
