import LRX.CanonicalGapSharpCases
import LRX.LargeComponentFixedGapSharpWords

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- For the actual many-component input all cursor pairs have a sharp original
word except possibly the two-positive-arc geometry. No budget premise remains. -/
theorem large_component_sharp_or_peak (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let r := componentLeft p root
    let q := localTarget p 0 r
    let t := (nontrivialSuffixComponents q (componentSet p root).card).card
    2 ≤ t → ∃ hc : (componentRoots q).card = t+1, ∀ start finish : Fin n,
      (∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      ((start-r) ≠ (finish-r) ∧ JoinedPositiveArcs q hc (start-r) (finish-r)) := by
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
  obtain ⟨hc,hwidth⟩ := large_component_width_reserve (by omega) p hmaj hm root hlarge ht
  obtain ⟨hc',hdef⟩ := large_component_bridge_reserve (by omega) p hmaj hm root hlarge ht
  rw [← hI] at hwidth hdef
  refine ⟨hc,?_⟩
  intro start finish
  rcases canonical_sharp_or_two_arc (by omega) q hqm hc (by omega) hdef hwidth
    (start-r) (finish-r) with h | h
  · obtain ⟨w,he,hl⟩ := h
    exact Or.inl ⟨w,he.trans (shifted_word_target p r start finish),hl⟩
  · exact Or.inr h

#print axioms large_component_sharp_or_peak
end LRX.FiniteCuts
