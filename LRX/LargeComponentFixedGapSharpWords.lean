import LRX.IsolatedGapSharpPayment
import LRX.LargeComponentWidthReserve

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Both fixed-gap branches are sharp for the original input and original
cursor coordinates; all numerical payment hypotheses are derived. -/
theorem large_component_fixed_gap_sharp_words (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let r := componentLeft p root
    let q := localTarget p 0 r
    let t := (nontrivialSuffixComponents q (componentSet p root).card).card
    2 ≤ t → ∃ hc : (componentRoots q).card = t+1,
      (∀ (i : Fin t) (start finish : Fin n),
        (bridgeEndpoints q hc i).1.val ≤ (start-r).val →
        (start-r).val < (bridgeEndpoints q hc i).2.val →
        (bridgeEndpoints q hc i).1.val ≤ (finish-r).val →
        (finish-r).val < (bridgeEndpoints q hc i).2.val →
        ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∧
      (∀ start finish : Fin n,
        ((outerRight q hc).val ≤ (start-r).val ∨ (start-r).val < (outerLeft q hc).val) →
        ((outerRight q hc).val ≤ (finish-r).val ∨ (finish-r).val < (outerLeft q hc).val) →
        ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) := by
  dsimp only
  intro ht
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hz := component_left_port_zero p root
  have hr : componentLeft p root-1+1 = r := by dsimp [r]; ring
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hqm := phase_zero_cut_majorized 0 (componentLeft p root-1) hd hmaj hz
  rw [hr] at hqm
  have hI := inversion_number_zero_recenter p (componentLeft p root-1) hz
  rw [hr] at hI
  obtain ⟨hc,hreserve⟩ := large_component_width_reserve (by omega) p hmaj hm root hlarge ht
  rw [← hI] at hreserve
  refine ⟨hc,?_,?_⟩
  · intro i start finish hxs hxv hys hyv
    obtain ⟨w,he,hl⟩ := joined_bridge_gap_sharp_word (by omega) q hqm hc hreserve i
      (start-r) (finish-r) hxs hxv hys hyv
    exact ⟨w,he.trans (shifted_word_target p r start finish),hl⟩
  · intro start finish hx hy
    obtain ⟨w,he,hl⟩ := joined_exterior_gap_sharp_word (by omega) q hqm hc (by omega) hreserve
      (start-r) (finish-r) hx hy
    exact ⟨w,he.trans (shifted_word_target p r start finish),hl⟩

#print axioms large_component_fixed_gap_sharp_words
end LRX.FiniteCuts
