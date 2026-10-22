import LRX.ComponentInterval
import LRX.LoadComponentPartition
import LRX.JoinedSourcePeak

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- All arrows crossing a finite cut start in its actual load component. -/
theorem crossing_positions_in_component (p : State n) (r : Fin n) :
    forward p.symm (r.val+1) ∪ backward p.symm (r.val+1) ⊆ componentSet p r := by
  intro i hi
  have hp : CycleFootprint.LoadPath (displacement p.symm) i r := by
    have hz : min (i : ℤ) ((i : ℤ)+displacement p.symm i) ≤ (r : ℤ) ∧
        (r : ℤ) ≤ max (i : ℤ) ((i : ℤ)+displacement p.symm i) := by
      unfold displacement
      rcases Finset.mem_union.mp hi with hi | hi
      · have hh := (mem_forward p.symm _ i).mp hi
        constructor <;> omega
      · have hh := (mem_backward p.symm _ i).mp hi
        constructor <;> omega
    simpa only [Int.cast_natCast,Fin.cast_val_eq_self] using
      CycleFootprint.arrow_load_path (displacement p.symm) i (r : ℤ) hz
  exact (CycleFootprint.mem_component _ _ _).mpr (CycleFootprint.load_path_symm _ hp)

/-- Twice the actual half-load fits in the component containing that port. -/
theorem twice_half_load_le_component (p : State n) (r : Fin n) :
    2*halfLoad p.symm (r.val+1) ≤ (componentSet p r).card := by
  have hdis : Disjoint (forward p.symm (r.val+1)) (backward p.symm (r.val+1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hf := (mem_forward p.symm _ i).mp hi
    have hb := (mem_backward p.symm _ i).mp hj
    omega
  have hh := Finset.card_le_card (crossing_positions_in_component p r)
  rw [Finset.card_union_of_disjoint hdis,← cut_balance] at hh
  change halfLoad p.symm (r.val+1)+halfLoad p.symm (r.val+1) ≤ _ at hh
  omega

theorem global_peak_component_capacity (p : State n) (L : ℕ)
    (hcap : ∀ i, (componentSet p i).card ≤ L) : 2*leftPeak p.symm n ≤ L := by
  have hh : leftPeak p.symm n ≤ L/2 := by
    apply Finset.sup_le
    intro e he
    have heN : e ≤ n := by have := Finset.mem_range.mp he; omega
    by_cases hz : e = 0
    · simp [hz]
    · let r : Fin n := ⟨e-1,by omega⟩
      have hr : r.val+1 = e := by dsimp [r]; omega
      have hb := twice_half_load_le_component p r
      rw [hr] at hb
      have hc := hcap r
      omega
  omega

theorem source_half_load_le_original (p : State n) (e : ℕ) :
    halfLoad (sourceTarget p).symm e ≤ halfLoad p.symm e := by
  classical
  apply Finset.card_le_card
  intro i hi
  have hh := (mem_forward (sourceTarget p).symm e i).mp hi
  by_cases hs : i ∈ sourcePackets p
  · have he : (sourceTarget p).symm i = p.symm i := by
      simp only [sourceTarget,PrunedLift.permutation_symm_apply,if_pos hs]
    rw [he] at hh
    exact (mem_forward p.symm e i).mpr hh
  · have he : (sourceTarget p).symm i = i := by
      simp only [sourceTarget,PrunedLift.permutation_symm_apply,if_neg hs]
    rw [he] at hh
    omega

theorem source_peak_component_capacity (p : State n) (L : ℕ)
    (hcap : ∀ i, (componentSet p i).card ≤ L) : 2*sourceHalfPeak p ≤ L := by
  have hh : sourceHalfPeak p ≤ leftPeak p.symm n := by
    change leftPeak (sourceTarget p).symm n ≤ leftPeak p.symm n
    apply Finset.sup_le
    intro e he
    exact (source_half_load_le_original p e).trans (Finset.le_sup he)
  have hb := global_peak_component_capacity p L hcap
  omega

#print axioms twice_half_load_le_component
#print axioms source_peak_component_capacity
end LRX.FiniteCuts
