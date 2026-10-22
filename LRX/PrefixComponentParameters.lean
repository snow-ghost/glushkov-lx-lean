import LRX.IsolatedBridgeBudget

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The component containing zero is precisely the prefix of its own cardinality. -/
theorem zero_component_prefix (p : State n) (i : Fin n) :
    i ∈ componentSet p 0 ↔ i.val < (componentSet p 0).card := by
  have hl := component_left_bound p 0 0 Relation.ReflTransGen.refl
  have hw := component_card_eq_width p 0
  rw [component_card_eq_width,component_set_eq_interval,Finset.mem_Icc]
  change ((componentLeft p 0).val ≤ i.val ∧ i.val ≤ (componentRight p 0).val) ↔ _
  have hz : (componentLeft p 0).val = 0 := by change (componentLeft p 0).val ≤ 0 at hl; omega
  omega

theorem prefix_nontrivial_components (p : State n) (L : ℕ)
    (hc : 2 ≤ (componentSet p 0).card)
    (hpref : ∀ i : Fin n, i ∈ componentSet p 0 ↔ i.val < L) :
    nontrivialSuffixComponents p 0 = insert (componentSet p 0) (nontrivialSuffixComponents p L) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    by_cases h : i.val < L
    · apply Finset.mem_insert.mpr
      left
      exact (CycleFootprint.component_eq_of_path _
        ((CycleFootprint.mem_component _ _ _).mp ((hpref i).mpr h))).symm
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨i,(mem_suffix_vertices L i).mpr (by omega),rfl⟩,hsize⟩
  · intro hC
    rcases Finset.mem_insert.mp hC with rfl | hC
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨0,by simp,rfl⟩,hc⟩
    · obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_image.mpr ⟨i,by simp,rfl⟩,hsize⟩

theorem prefix_component_not_external (p : State n) (L : ℕ)
    (hpref : ∀ i : Fin n, i ∈ componentSet p 0 ↔ i.val < L) :
    componentSet p 0 ∉ nontrivialSuffixComponents p L := by
  classical
  intro h
  obtain ⟨h,hsize⟩ := Finset.mem_filter.mp h
  obtain ⟨i,hi,he⟩ := Finset.mem_image.mp h
  have hi' : i ∈ componentSet p 0 := by
    rw [← he]
    exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
  have hl := (hpref i).mp hi'
  have hr := (mem_suffix_vertices L i).mp hi
  omega

theorem prefix_singleton_components (p : State n) (L : ℕ)
    (hc : 2 ≤ (componentSet p 0).card)
    (hpref : ∀ i : Fin n, i ∈ componentSet p 0 ↔ i.val < L) :
    singletonSuffixComponents p 0 = singletonSuffixComponents p L := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    have hout : L ≤ i.val := by
      by_contra hh
      have he := CycleFootprint.component_eq_of_path _
        ((CycleFootprint.mem_component _ _ _).mp ((hpref i).mpr (by omega)))
      change componentSet p 0 = componentSet p i at he
      change (componentSet p i).card = 1 at hsize
      rw [he,hsize] at hc
      omega
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i,(mem_suffix_vertices L i).mpr hout,rfl⟩,hsize⟩
  · intro hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i,by simp,rfl⟩,hsize⟩

/-- Routing roots and C7's external component parameter agree exactly. -/
theorem prefix_component_root_count (p : State n) (L : ℕ)
    (hc : 2 ≤ (componentSet p 0).card)
    (hpref : ∀ i : Fin n, i ∈ componentSet p 0 ↔ i.val < L) :
    (componentRoots p).card = (nontrivialSuffixComponents p L).card+1 := by
  classical
  rw [component_roots_card_eq_blocks,prefix_nontrivial_components p L hc hpref,
    Finset.card_insert_of_notMem (prefix_component_not_external p L hpref)]

#print axioms prefix_singleton_components
#print axioms prefix_component_root_count
end LRX.FiniteCuts
