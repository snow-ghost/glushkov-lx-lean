import LRX.FiniteComponentExtrema

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem two_components_gap_fixed (p : State n) (a b : CycleFootprint.Active p)
    (hcomponents : ∀ i, p.symm i ≠ i →
      CycleFootprint.LoadPath (displacement p.symm) a.val i ∨
      CycleFootprint.LoadPath (displacement p.symm) b.val i)
    (x : Fin n) (hx : (componentRight p a.val).val < x.val)
    (hy : x.val < (componentLeft p b.val).val) : p x=x := by
  by_contra hfix
  have hm : p.symm x ≠ x := by
    intro he
    exact hfix (by simpa only [Equiv.apply_symm_apply] using (congrArg p he).symm)
  rcases hcomponents x hm with h | h
  · have := component_right_bound p a.val x h
    omega
  · have := component_left_bound p b.val x h
    omega

theorem two_component_bridge_inversions (p : State n) (a b : CycleFootprint.Active p)
    (horder : (componentRight p a.val).val < (componentLeft p b.val).val)
    (hcomponents : ∀ i, p.symm i ≠ i →
      CycleFootprint.LoadPath (displacement p.symm) a.val i ∨
      CycleFootprint.LoadPath (displacement p.symm) b.val i) :
    inversionNumber (componentBridge p (componentRight p a.val) (componentLeft p b.val))=
      inversionNumber p+(2*((componentLeft p b.val).val-(componentRight p a.val).val)-1) := by
  obtain ⟨_,_,ha,hb⟩ := component_extreme_bridge_data p a b horder
  exact component_bridge_inversions p _ _ horder (by omega) (by omega)
    (two_components_gap_fixed p a b hcomponents)

/-- The bridge hypotheses are extracted from two actual ordered load components.
The root is supplied by the already constructed source packet of the left
component; no separate service-reachability hypothesis is imposed. -/
theorem two_component_bridge_word (hn : 2 ≤ n) (p : State n) (a b : CycleFootprint.Active p)
    (horder : (componentRight p a.val).val < (componentLeft p b.val).val)
    (hcomponents : ∀ i, p.symm i ≠ i →
      CycleFootprint.LoadPath (displacement p.symm) a.val i ∨
      CycleFootprint.LoadPath (displacement p.symm) b.val i)
    (start finish : Fin n) :
    ∃ (r : Fin n) (w : List Letter), CycleFootprint.LoadPath (displacement p.symm) a.val r ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*((componentLeft p b.val : ℤ)-(componentRight p a.val : ℤ))-
        RotationWords.portLoad (displacement p.symm) r+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) := by
  let u := componentRight p a.val
  let v := componentLeft p b.val
  change u.val < v.val at horder
  obtain ⟨hu,hv,ha,hb⟩ := component_extreme_bridge_data p a b horder
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hau := component_right_path p a.val
  have hbv := component_left_path p b.val
  have hmax : ∀ x, CycleFootprint.LoadPath (displacement p.symm) u x → x.val ≤ u.val := by
    intro x hx
    exact component_right_bound p a.val x (hau.trans hx)
  have hmin : ∀ x, CycleFootprint.LoadPath (displacement p.symm) v x → v.val ≤ x.val := by
    intro x hx
    exact component_left_bound p b.val x (hbv.trans hx)
  have hr : ∀ i, p.symm i ≠ i → FiniteReach p u i ∨ FiniteReach p v i := by
    intro i hi
    rcases hcomponents i hi with hh | hh
    · exact Or.inl (finite_component_right_reaches p u v hu horder hmax i hi
        ((CycleFootprint.load_path_symm _ hau).trans hh))
    · exact Or.inr (finite_component_left_reaches p u v hv horder hmin i hi
        ((CycleFootprint.load_path_symm _ hbv).trans hh))
  obtain ⟨root,hrootpath,hsource,_⟩ := CycleFootprint.load_component_source_packet hd
    (displacement_short p.symm) a
  have huroot := finite_component_right_reaches p u v hu horder hmax root.val root.property
    ((CycleFootprint.load_path_symm _ hau).trans hrootpath)
  have hru : FiniteReach p root.val u := hsource ⟨u,hu⟩ huroot
  obtain ⟨w,he,hlen⟩ := component_bridge_word hn p u v root.val start finish horder
    (le_of_lt ha) (le_of_lt hb) root.property hru hr
  exact ⟨root.val,w,hrootpath,he,hlen⟩

#print axioms two_component_bridge_inversions
#print axioms two_component_bridge_word
end LRX.FiniteCuts
