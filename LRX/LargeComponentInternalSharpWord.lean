import LRX.SourceGapSharpPayment

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- A real sharp word for the positive internal-gap branch with at least two
external nontrivial components. The reserve and all filling certificates are derived. -/
theorem large_component_internal_gap_sharp_word (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let r := componentLeft p root
    let q := localTarget p 0 r
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    2 ≤ t → ∀ (u : {u // u ∈ positiveSourceGapStarts q n}) (start finish : Fin n),
      u.val.val ≤ (start-r).val → (start-r).val < FiniteGaps.next (sourcePackets q) u.val →
      u.val.val ≤ (finish-r).val → (finish-r).val < FiniteGaps.next (sourcePackets q) u.val →
      ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  dsimp only
  intro ht u start finish hsu hsv hfu hfv
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
  obtain ⟨hc,hreserve⟩ := large_component_bridge_reserve (by omega) p hmaj hm root hlarge ht
  rw [← hI] at hreserve
  obtain ⟨w,he,hl⟩ := selected_source_gap_sharp_word (by omega) q hqm hc (by omega)
    hreserve u (start-r) (finish-r) hsu hsv hfu hfv
  exact ⟨w,he.trans (shifted_word_target p r start finish),hl⟩

#print axioms large_component_internal_gap_sharp_word
end LRX.FiniteCuts
