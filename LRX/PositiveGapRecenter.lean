import LRX.ComponentCutPeakInvariant
import LRX.ManyComponentPeakReduction

namespace LRX.FiniteCuts
open RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- A nonwrapping interval disjoint from the cut preserves both its open
and half-open membership under the cyclic change of coordinates. -/
theorem interval_recenter_outside (u v r : Fin n) (huv : u.val < v.val)
    (hout : r.val ≤ u.val ∨ v.val < r.val) :
    (u-r).val < (v-r).val ∧
    (∀ x : Fin n, (u.val ≤ x.val ∧ x.val < v.val) ↔
      ((u-r).val ≤ (x-r).val ∧ (x-r).val < (v-r).val)) ∧
    (∀ x : Fin n, (u.val < x.val ∧ x.val < v.val) ↔
      ((u-r).val < (x-r).val ∧ (x-r).val < (v-r).val)) := by
  have shift (x : Fin n) : (x-r).val =
      if r.val ≤ x.val then x.val-r.val else n+x.val-r.val := by
    by_cases hx : r.val ≤ x.val
    · rw [if_pos hx]
      exact Fin.sub_val_of_le hx
    · rw [if_neg hx]
      exact Fin.coe_sub_iff_lt.mpr (show x < r by omega)
  rw [shift u,shift v]
  rcases hout with hout | hout
  · rw [if_pos hout,if_pos (show r.val ≤ v.val by omega)]
    refine ⟨by omega,?_,?_⟩ <;> intro x <;> rw [shift x] <;>
      split_ifs <;> have := x.isLt <;> have := r.isLt <;> omega
  · rw [if_neg (show ¬r.val ≤ u.val by omega),if_neg (show ¬r.val ≤ v.val by omega)]
    refine ⟨by omega,?_,?_⟩ <;> intro x <;> rw [shift x] <;>
      split_ifs <;> have := x.isLt <;> have := r.isLt <;> omega

/-- The component cut lies outside every positive source gap. -/
theorem positive_source_gap_cut_outside (p : State n) (root u v : Fin n)
    (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p) (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u) :
    (componentLeft p root).val ≤ u.val ∨ v.val < (componentLeft p root).val := by
  let r := componentLeft p root
  have hp := positive_source_gap_load_path p u v hu hv huv hgap hpos
  have hz := component_left_port_zero p root
  by_contra hh
  have hur : u.val < r.val := by dsimp [r]; omega
  have hrv : r.val ≤ v.val := by dsimp [r]; omega
  have hr0 : r ≠ 0 := by intro h; rw [h,Fin.val_zero] at hur; omega
  have he : (r-1).val=r.val-1 := Fin.val_sub_one_of_ne_zero hr0
  have hload := load_path_crossed_port_positive p hp (r-1) (by omega) (by omega)
  change portLoad (displacement p.symm) (r-1)=0 at hz
  omega

/-- A positive source gap and both cursors transfer to the component cut,
where the existing sharp internal-gap word already applies. -/
theorem original_positive_source_gap_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (u v : Fin n) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (huv : u.val < v.val)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (hpos : 0 < portLoad (displacement p.symm) u)
    (start finish : Fin n) (hs : u.val ≤ start.val ∧ start.val < v.val)
    (hf : u.val ≤ finish.val ∧ finish.val < v.val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hcan := component_cut_canonical_displacement p root
  have hsource (x : Fin n) : x-r ∈ sourcePackets q ↔ x ∈ sourcePackets p := by
    have h := source_packets_recenter p r hcan (x-r)
    simpa only [RotationWords.rotation,AffineLift.rotation_power_apply,Fin.cast_val_eq_self,sub_add_cancel] using h
  have hinterval := interval_recenter_outside u v r huv
    (positive_source_gap_cut_outside p root u v hu hv huv hgap hpos)
  have hu' := (hsource u).mpr hu
  have hv' := (hsource v).mpr hv
  have hgap' (x : Fin n) (hux : (u-r).val < x.val) (hxv : x.val < (v-r).val) :
      x ∉ sourcePackets q := by
    have hx := (hinterval.2.2 (x+r)).mpr (by simpa only [add_sub_cancel_right] using And.intro hux hxv)
    intro hxs
    apply hgap (x+r) hx.1 hx.2
    exact (hsource (x+r)).mp (by simpa only [add_sub_cancel_right] using hxs)
  have hpos' : 0 < portLoad (displacement q.symm) (u-r) := by
    rw [← hcan,port_load_recenter,sub_add_cancel]
    exact hpos
  obtain ⟨hnext,hselected⟩ := consecutive_positive_gap_selected q n (u-r) (v-r)
    hu' hv' hinterval.1 hgap' hpos' (v-r).isLt.le
  have hs' := (hinterval.2.1 start).mp hs
  have hf' := (hinterval.2.1 finish).mp hf
  apply large_component_internal_gap_sharp_word hn p hmaj hm root hlarge ht
    ⟨u-r,hselected⟩ start finish hs'.1 ?_ hf'.1 ?_
  · change (start-r).val < FiniteGaps.next (sourcePackets q) (u-r)
    simpa only [hnext] using hs'.2
  · change (finish-r).val < FiniteGaps.next (sourcePackets q) (u-r)
    simpa only [hnext] using hf'.2

#print axioms original_positive_source_gap_sharp_word
end LRX.FiniteCuts
