import LRX.ActualAreaWindowFamily
import LRX.FiniteOuterSource
import LRX.PrefixComponentParameters
import LRX.SourceGapComponent

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- Both ends of a nontrivial proper initial component are source vertices. -/
theorem prefix_component_source_ends (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n) :
    (0 : Fin n) ∈ sourcePackets p ∧
      componentRight p 0 ∈ sourcePackets p ∧
      (componentRight p 0).val+1 = (componentSet p 0).card := by
  have hl := component_left_bound p 0 0 Relation.ReflTransGen.refl
  have hz : componentLeft p 0 = 0 := by
    apply Fin.ext
    change (componentLeft p 0).val ≤ 0 at hl
    change (componentLeft p 0).val = 0
    omega
  have hw := component_card_eq_width p 0
  rw [hz,Fin.val_zero,Nat.sub_zero] at hw
  have hm : p.symm 0 ≠ 0 := by
    simpa only [hz] using nontrivial_component_left_moved p 0 hc
  have he := left_component_outer_source (by omega) p ⟨0,hm⟩ (by change (componentRight p 0).val+1 < n; omega)
  refine ⟨?_,nonwrapping_component_right_source p ⟨0,hm⟩ (by change (componentRight p 0).val+1 < n; omega),hw.symm⟩
  simpa only [hz] using he.1

/-- Every non-source position in the initial component is in a selected gap. -/
theorem prefix_non_source_in_area_family (p : State n)
    (hc : 2 ≤ (componentSet p 0).card) (hproper : (componentSet p 0).card < n)
    (i : Fin n) (hi : i.val < (componentSet p 0).card)
    (hnot : i ∉ sourcePackets p) :
    i ∈ familyPositions (areaWindowFamily p (componentSet p 0).card) := by
  classical
  obtain ⟨hzero,hr,hw⟩ := prefix_component_source_ends p hc hproper
  obtain ⟨u,hu,hiu⟩ := FiniteGaps.outside_in_gap (sourcePackets p) hzero i hnot
  obtain ⟨hui,hinext⟩ := (FiniteGaps.mem_positions _ _ _).mp hiu
  have hur : u.val < (componentRight p 0).val := by omega
  have hn := FiniteGaps.next_le_member (sourcePackets p) u (componentRight p 0) hr hur
  have hpos := load_path_crossed_port_positive p (component_right_path p 0) u
    (by change 0 ≤ u.val; omega) hur
  have hselected : u ∈ positiveSourceGapStarts p (componentSet p 0).card :=
    (mem_positive_source_gap_starts _ _ _).mpr ⟨hu,by omega,by omega,hpos⟩
  let us : {u // u ∈ positiveSourceGapStarts p (componentSet p 0).card} := ⟨u,hselected⟩
  apply (mem_family_positions _ _).mpr
  refine ⟨positiveSourceFilling p (componentSet p 0).card us,?_,?_⟩
  · apply List.mem_append.mpr
    apply Or.inl
    apply List.mem_map.mpr
    exact ⟨us,by simp,rfl⟩
  · exact (FiniteGaps.contains_window _ _ _).mpr ⟨hui,hinext⟩

#print axioms prefix_component_source_ends
#print axioms prefix_non_source_in_area_family
end LRX.FiniteCuts
