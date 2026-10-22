import LRX.TwoComponentActivityRouting

namespace LRX.FiniteCuts
open RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Cutting between the outer source endpoints turns their wrapping gap into
an ordinary interval and preserves both endpoint and cursor membership. -/
theorem exterior_interval_recenter_inside (l h r : Fin n)
    (hlr : l.val < r.val) (hrh : r.val ≤ h.val) :
    (h-r).val < (l-r).val ∧
    (∀ x : Fin n, (h.val ≤ x.val ∨ x.val < l.val) ↔
      ((h-r).val ≤ (x-r).val ∧ (x-r).val < (l-r).val)) ∧
    (∀ x : Fin n, (h.val < x.val ∨ x.val < l.val) ↔
      ((h-r).val < (x-r).val ∧ (x-r).val < (l-r).val)) := by
  have shift (x : Fin n) : (x-r).val =
      if r.val ≤ x.val then x.val-r.val else n+x.val-r.val := by
    by_cases hx : r.val ≤ x.val
    · rw [if_pos hx]
      exact Fin.sub_val_of_le hx
    · rw [if_neg hx]
      exact Fin.coe_sub_iff_lt.mpr (show x < r by omega)
  rw [shift h,shift l,if_pos hrh,if_neg (show ¬r.val ≤ l.val by omega)]
  have hhn := h.isLt
  have hrn := r.isLt
  refine ⟨by omega,?_,?_⟩ <;> intro x <;> rw [shift x] <;>
    split_ifs <;> have := x.isLt <;> omega

/-- The exterior two-component case is a previously paid source gap after
cutting at the second component. No numerical exceptional case remains. -/
theorem two_component_exterior_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (start finish : Fin n) (hout : OuterCursorPair p hc start finish) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  let a := componentOrder p hc (Fin.last 1)
  let r := componentLeft p a
  let q := localTarget p 0 r
  let l := outerLeft p hc
  let h := outerRight p hc
  have horder := ordered_component_roots p (component_order_mem p hc 0)
    (component_order_mem p hc (Fin.last 1)) ((componentOrder p hc).strictMono (by decide))
  have hl := component_left_bound p (componentOrder p hc 0)
    (componentRight p (componentOrder p hc 0)) (component_right_path p (componentOrder p hc 0))
  have hr := component_right_bound p a r (component_left_path p a)
  have hlr : l.val < r.val := by
    change (componentRight p (componentOrder p hc 0)).val < r.val at horder
    change l.val ≤ (componentRight p (componentOrder p hc 0)).val at hl
    omega
  have hrh : r.val ≤ h.val := hr
  have hinterval := exterior_interval_recenter_inside l h r hlr hrh
  have hcan := component_cut_canonical_displacement p a
  have hqm : AffineLift.Majorized (displacement q.symm) := by
    rw [← hcan]
    exact majorized_recenter hmaj r
  have hqc : (componentRoots q).card=1+1 := by
    have hh := component_cut_nontrivial_count p a
    rw [component_roots_card_eq_blocks] at hc ⊢
    change (nontrivialSuffixComponents q 0).card = (nontrivialSuffixComponents p 0).card at hh
    exact hh.trans hc
  have hlargeq : (n+1)/2 < (componentSet q (root-r)).card := by
    have hh := (component_recenter_cut p a).2 (root-r)
    change (componentSet q (root-r)).card = (componentSet p (root-r+r)).card at hh
    rw [sub_add_cancel] at hh
    omega
  have hsource (x : Fin n) : x-r ∈ sourcePackets q ↔ x ∈ sourcePackets p := by
    have hh := source_packets_recenter p r hcan (x-r)
    simpa only [RotationWords.rotation,AffineLift.rotation_power_apply,
      Fin.cast_val_eq_self,sub_add_cancel] using hh
  obtain ⟨_,hL,hR,_,_⟩ := joined_outer_ports (by omega) p hc (by omega)
  have hgap (x : Fin n) (hux : (h-r).val < x.val) (hxv : x.val < (l-r).val) :
      x ∉ sourcePackets q := by
    have hx := (hinterval.2.2 (x+r)).mpr (by
      simpa only [add_sub_cancel_right] using And.intro hux hxv)
    intro hxs
    have hxs' := (hsource (x+r)).mp (by simpa only [add_sub_cancel_right] using hxs)
    have hb := moving_between_outer p hc (x+r) ((mem_source_packets p (x+r)).mp hxs').1
    change l.val ≤ (x+r).val ∧ (x+r).val ≤ h.val at hb
    omega
  have hs := (hinterval.2.1 start).mp hout.1
  have hf := (hinterval.2.1 finish).mp hout.2
  obtain ⟨w,he,hlen⟩ := two_component_source_gap_sharp_word hn q hqm hqc (root-r) hlargeq
    (h-r) (l-r) ((hsource h).mpr hR) ((hsource l).mpr hL) hinterval.1 hgap
    (start-r) (finish-r) hs.1 hs.2 hf.1 hf.2
  exact ⟨w,he.trans (shifted_word_target p r start finish),hlen⟩

#print axioms exterior_interval_recenter_inside
#print axioms two_component_exterior_sharp_word
end LRX.FiniteCuts
