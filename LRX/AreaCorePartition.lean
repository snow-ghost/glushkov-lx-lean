import LRX.ComponentAreaDeficit

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

noncomputable def prefixSourceCore (p : State n) : Finset (Fin n) := by
  classical
  exact (sourcePackets p).filter (fun i => i.val < (componentSet p 0).card)

/-- The unselected positions are exactly the original prefix core and isolated vertices. -/
theorem area_positions_complement (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    (familyPositions (areaWindowFamily p (componentSet p 0).card))ᶜ =
      prefixSourceCore p ∪ isolatedVertices p := by
  classical
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  ext i
  constructor
  · intro hi
    have hn := Finset.mem_compl.mp hi
    by_cases hiso : i ∈ isolatedVertices p
    · exact Finset.mem_union.mpr (Or.inr hiso)
    · have hsize : 2 ≤ (componentSet p i).card := by
        have hpos := Finset.card_pos.mpr (component_set_nonempty p i)
        have hh : (componentSet p i).card ≠ 1 := fun h => hiso ((mem_isolated_vertices p i).mpr h)
        omega
      have hprefix : i.val < L := by
        by_contra h
        exact hn (exterior_nontrivial_in_area_family p L i (by omega) hsize)
      have hsource : i ∈ sourcePackets p := by
        by_contra h
        exact hn (prefix_non_source_in_area_family p hc hproper i hprefix h)
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hsource,hprefix⟩))
  · intro hi
    apply Finset.mem_compl.mpr
    intro hW
    rcases Finset.mem_union.mp hi with hcore | hiso
    · obtain ⟨hsource,hprefix⟩ := Finset.mem_filter.mp hcore
      obtain ⟨A,hA,hiA⟩ := (mem_family_positions _ _).mp hW
      rcases List.mem_append.mp hA with hA | hA
      · obtain ⟨u,_,rfl⟩ := List.mem_map.mp hA
        have hiGap : i ∈ FiniteGaps.positions (sourcePackets p) u.val :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _,hiA⟩
        exact FiniteGaps.gap_avoids_marks _ _ _ hiGap hsource
      · have hb := (suffix_component_family_spec p L hproper.le hcut).2.2 A hA
        unfold Contains at hiA
        change i.val < L at hprefix
        omega
    · have hh : i ∈ (familyPositions (areaWindowFamily p L) ∪ p.support)ᶜ := by
        rw [area_fixed_complement_eq_isolated p hc hproper]
        exact hiso
      exact (Finset.mem_compl.mp hh) (Finset.mem_union.mpr (Or.inl hW))

/-- Exact C5 bookkeeping for the actual windows, original core and C7 singletons. -/
theorem area_core_size_partition (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    ((areaWindowFamily p (componentSet p 0).card).map (fun A => A.size)).sum +
      (prefixSourceCore p).card + (singletonSuffixComponents p (componentSet p 0).card).card = n := by
  classical
  let L := (componentSet p 0).card
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hcut (i : Fin n) : (p i).val < L ↔ i.val < L := by
    change (p i).val < (componentSet p 0).card ↔ i.val < (componentSet p 0).card
    rw [← zero_component_prefix,← zero_component_prefix]
    exact CycleFootprint.component_invariant hd 0 i
  obtain ⟨hm,ha⟩ := area_window_family_spec p L hproper.le hcut
  have hcard := (window_family_selected_energy (areaWindowFamily p L) p.symm hm ha).1
  have hdis : Disjoint (prefixSourceCore p) (isolatedVertices p) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hsource := (mem_source_packets p i).mp (Finset.mem_filter.mp hi).1
    have he := isolated_vertex_fixed p i hj
    have hinv : p.symm i = i := by
      apply p.injective
      simpa only [Equiv.apply_symm_apply] using he.symm
    exact hsource.1 hinv
  have hcomp := congrArg Finset.card (area_positions_complement p hc hproper)
  rw [Finset.card_compl,Fintype.card_fin,Finset.card_union_of_disjoint hdis,
    isolated_vertices_card,prefix_singleton_components p L hc (zero_component_prefix p)] at hcomp
  have hle : (familyPositions (areaWindowFamily p L)).card ≤ n := by
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  change n-(familyPositions (areaWindowFamily p L)).card =
    (prefixSourceCore p).card + (singletonSuffixComponents p L).card at hcomp
  change ((areaWindowFamily p L).map (fun A => A.size)).sum +
    (prefixSourceCore p).card + (singletonSuffixComponents p L).card = n
  omega

#print axioms area_positions_complement
#print axioms area_core_size_partition
end LRX.FiniteCuts
