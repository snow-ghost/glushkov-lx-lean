import LRX.SourceGapReversalFamily
import LRX.ComponentInterval

namespace LRX.FiniteCuts
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The right boundary is an original source vertex when its successor does not wrap. -/
theorem nonwrapping_component_right_source (p : State n) (a : CycleFootprint.Active p)
    (hr : (componentRight p a.val).val+1 < n) :
    componentRight p a.val ∈ sourcePackets p := by
  let r := componentRight p a.val
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hadj : CycleFootprint.Adjacent r (r+1) := Or.inl rfl
  have hout : ¬CycleFootprint.LoadPath (displacement p.symm) r (r+1) := by
    intro hp
    have hb := component_right_bound p a.val (r+1) ((component_right_path p a.val).trans hp)
    rw [Fin.val_add_one_of_lt' hr] at hb
    omega
  have hm := CycleFootprint.load_boundary_active hd (displacement_short p.symm) a r (r+1)
    (component_right_path p a.val) hadj hout
  apply component_universal_source p r hm
  intro x hx hp
  exact CycleFootprint.boundary_load_reaches hd (displacement_short p.symm)
    ⟨r,hm⟩ (r+1) hadj hout ⟨x,hx⟩ hp

/-- Consecutive source vertices with a positive left port lie in one component. -/
theorem positive_source_gap_load_path (p : State n) (u v : Fin n)
    (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p) (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u) :
    CycleFootprint.LoadPath (displacement p.symm) u v := by
  have hm := ((mem_source_packets p u).mp hu).1
  have hur := component_right_bound p u u Relation.ReflTransGen.refl
  have hul := component_left_bound p u u Relation.ReflTransGen.refl
  have hvr : v.val ≤ (componentRight p u).val := by
    by_contra h
    have hr : (componentRight p u).val < v.val := by omega
    have hrs := nonwrapping_component_right_source p ⟨u,hm⟩ (by change (componentRight p u).val+1 < n; have := v.isLt; omega)
    have huz : u ≠ componentRight p u := by
      intro he
      have hz := component_right_port_zero p u
      rw [← he] at hz
      omega
    have hune : u.val ≠ (componentRight p u).val := fun he => huz (Fin.ext he)
    exact hgap _ (by omega) hr hrs
  apply (CycleFootprint.mem_component _ _ _).mp
  change v ∈ componentSet p u
  rw [component_set_eq_interval]
  exact Finset.mem_Icc.mpr ⟨by change (componentLeft p u).val ≤ v.val; omega,hvr⟩

/-- Every port of an extracted source gap is positive in the original graph. -/
theorem selected_source_gap_ports_positive (p : State n) (L : ℕ)
    (u : {u // u ∈ positiveSourceGapStarts p L}) (r : Fin n)
    (hur : u.val.val ≤ r.val) (hrv : r.val < FiniteGaps.next (sourcePackets p) u.val) :
    0 < portLoad (displacement p.symm) r := by
  have hu := (mem_positive_source_gap_starts p L u.val).mp u.property
  obtain ⟨v,hv,he⟩ := FiniteGaps.next_is_member (sourcePackets p) u.val hu.2.1
  have huv := FiniteGaps.lt_next (sourcePackets p) u.val
  have hgap (x : Fin n) (hux : u.val.val < x.val) (hxv : x.val < v.val) :
      x ∉ sourcePackets p := by
    exact FiniteGaps.gap_avoids_marks (sourcePackets p) u.val x
      ((FiniteGaps.mem_positions _ _ _).mpr ⟨hux,by omega⟩)
  have hp := positive_source_gap_load_path p u.val v hu.1 hv (by omega) hgap hu.2.2.2
  exact load_path_crossed_port_positive p hp r hur (by omega)

#print axioms positive_source_gap_load_path
#print axioms selected_source_gap_ports_positive
end LRX.FiniteCuts
