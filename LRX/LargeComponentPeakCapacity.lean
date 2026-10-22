import LRX.ComponentPeakCapacity

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A component larger than half the circle is maximal by disjointness. -/
theorem large_component_card_maximal (p : State n) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    ∀ i, (componentSet p i).card ≤ (componentSet p root).card := by
  classical
  intro i
  by_cases he : componentSet p root = componentSet p i
  · rw [he]
  · have ha : componentSet p root ∈ CycleFootprint.componentBlocks
        (displacement p.symm) Finset.univ :=
      Finset.mem_image.mpr ⟨root,Finset.mem_univ _,rfl⟩
    have hb : componentSet p i ∈ CycleFootprint.componentBlocks
        (displacement p.symm) Finset.univ :=
      Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hd : Disjoint (componentSet p root) (componentSet p i) :=
      CycleFootprint.component_blocks_disjoint (displacement p.symm) Finset.univ ha hb he
    have hle : (componentSet p root ∪ componentSet p i).card ≤ n := by
      exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
    rw [Finset.card_union_of_disjoint hd] at hle
    omega

/-- The width condition 2U≤L used by C10, with the real global source peak. -/
theorem large_component_source_peak_capacity (p : State n) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    2*sourceHalfPeak p ≤ (componentSet p root).card :=
  source_peak_component_capacity p _ (large_component_card_maximal p root hlarge)

#print axioms large_component_card_maximal
#print axioms large_component_source_peak_capacity
end LRX.FiniteCuts
