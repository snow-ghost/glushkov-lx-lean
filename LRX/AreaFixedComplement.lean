import LRX.PrefixAreaCoverage

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Every position selected by an exterior component window is non-isolated. -/
theorem suffix_family_position_nontrivial (p : State n) (L : ℕ) (i : Fin n)
    (hi : i ∈ familyPositions (suffixComponentFamily p L)) :
    2 ≤ (componentSet p i).card := by
  classical
  obtain ⟨A,hA,hi⟩ := (mem_family_positions _ _).mp hi
  obtain ⟨C,_,rfl⟩ := List.mem_map.mp hA
  have hiC := (suffix_component_filling_spec p L C).2.1 i |>.mp hi
  obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp C.property
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hC
  rw [← he] at hiC hsize
  have heq := CycleFootprint.component_eq_of_path _
    ((CycleFootprint.mem_component _ _ _).mp hiC)
  change componentSet p a = componentSet p i at heq
  change 2 ≤ (componentSet p a).card at hsize
  rwa [heq] at hsize

/-- Every nontrivial exterior component is included in the selected family. -/
theorem exterior_nontrivial_in_area_family (p : State n) (L : ℕ) (i : Fin n)
    (hi : L ≤ i.val) (hc : 2 ≤ (componentSet p i).card) :
    i ∈ familyPositions (areaWindowFamily p L) := by
  classical
  have hC : componentSet p i ∈ nontrivialSuffixComponents p L :=
    Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i,(mem_suffix_vertices L i).mpr hi,rfl⟩,hc⟩
  let C : {C // C ∈ nontrivialSuffixComponents p L} := ⟨componentSet p i,hC⟩
  apply (mem_family_positions _ _).mpr
  refine ⟨suffixComponentFilling p L C,?_,?_⟩
  · apply List.mem_append.mpr
    apply Or.inr
    exact List.mem_map.mpr ⟨C,by simp,rfl⟩
  · apply ((suffix_component_filling_spec p L C).2.1 i).mpr
    exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl

/-- The fixed complement of the actual area family consists exactly of isolated vertices. -/
theorem area_fixed_complement_eq_isolated (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    (familyPositions (areaWindowFamily p (componentSet p 0).card) ∪ p.support)ᶜ =
      isolatedVertices p := by
  classical
  ext i
  constructor
  · intro hi
    have hnot := Finset.mem_compl.mp hi
    have hnW : i ∉ familyPositions (areaWindowFamily p (componentSet p 0).card) :=
      fun h => hnot (Finset.mem_union.mpr (Or.inl h))
    have hnS : i ∉ p.support := fun h => hnot (Finset.mem_union.mpr (Or.inr h))
    have hout : (componentSet p 0).card ≤ i.val := by
      by_contra h
      apply hnW
      apply prefix_non_source_in_area_family p hc hproper i (by omega)
      intro hs
      exact hnS ((mem_support_inverse p i).mpr ((mem_source_packets p i).mp hs).1)
    have hpos := Finset.card_pos.mpr (component_set_nonempty p i)
    apply (mem_isolated_vertices p i).mpr
    by_contra h
    exact hnW (exterior_nontrivial_in_area_family p _ i hout (by omega))
  · intro hi
    have hsize := (mem_isolated_vertices p i).mp hi
    apply Finset.mem_compl.mpr
    intro hm
    rcases Finset.mem_union.mp hm with hm | hm
    · obtain ⟨A,hA,hiA⟩ := (mem_family_positions _ _).mp hm
      rcases List.mem_append.mp hA with hA | hA
      · have hend := (positive_source_family_spec p (componentSet p 0).card).2.2.1 A hA
        have hin : i.val < (componentSet p 0).card := by
          unfold Contains at hiA
          omega
        have hp := (CycleFootprint.mem_component _ _ _).mp ((zero_component_prefix p i).mpr hin)
        have he := CycleFootprint.component_eq_of_path _ hp
        change componentSet p 0 = componentSet p i at he
        rw [he,hsize] at hc
        omega
      · have hnon := suffix_family_position_nontrivial p (componentSet p 0).card i
          ((mem_family_positions _ _).mpr ⟨A,hA,hiA⟩)
        omega
    · exact (Equiv.Perm.mem_support.mp hm) (isolated_vertex_fixed p i hi)

/-- The a parameter of C9 equals the actual external singleton count of C7. -/
theorem area_fixed_complement_card (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ((familyPositions (areaWindowFamily p (componentSet p 0).card) ∪
      Equiv.Perm.support p.symm)ᶜ).card =
      (singletonSuffixComponents p (componentSet p 0).card).card := by
  have hs : Equiv.Perm.support p.symm = p.support := Equiv.Perm.support_inv p
  rw [hs,area_fixed_complement_eq_isolated p hc hproper,isolated_vertices_card,
    prefix_singleton_components p (componentSet p 0).card hc (zero_component_prefix p)]

#print axioms area_fixed_complement_eq_isolated
#print axioms area_fixed_complement_card
end LRX.FiniteCuts
