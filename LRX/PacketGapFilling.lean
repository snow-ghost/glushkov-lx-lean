import LRX.PacketGapConfinement
import LRX.FiniteWindowRestriction
import LRX.FiniteGapPacketWordBound

/-! The finite filling required by the gap-word theorem is derived from the
absence of packet vertices in the open gap. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem packet_gap_filling {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (W : Window n b) (hoff : W.offset=1) (r : Fin n) (hedge : W.offset+b=r.val)
    (hr : PrunedLift.InCore p d 0 r)
    (hgap : ∀ i, Contains W i → ¬PrunedLift.InCore p d 0 i) :
    ∃ filling : State b, (∀ i, p.symm (embed W i)=embed W (filling i)) ∧
      (∀ i, d (embed W i)=(filling i : ℤ)-(i : ℤ)) := by
  have hncore : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬PrunedLift.InCore p d 0 i := by
    intro i hi hi'
    apply hgap i
    simp only [Contains]
    omega
  have hbounds (i : Fin n) (hi : Contains W i) :=
    PrunedLift.gap_canonical_displacement hd hcover hroot r hr hncore i
      (by unfold Contains at hi; omega) (by unfold Contains at hi; omega)
  obtain ⟨filling,hmatch⟩ := exists_restriction_of_inverse_closed W p (fun i hi => by
    obtain ⟨_,hlo,hhi⟩ := hbounds i hi
    unfold Contains
    omega)
  refine ⟨filling,hmatch,?_⟩
  intro i
  have h := (hbounds (embed W i) (contains_embed W i)).1
  rw [hmatch] at h
  simpa [embed] using h

theorem geometric_gap_word_bound (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hr : PrunedLift.InCore p d 0 r)
    (hgap : ∀ i, Contains W i → ¬PrunedLift.InCore p d 0 i)
    (hwidth : 2*b ≤ n) (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-(∑ i : Fin b, |d (embed W i)|)+
        (b*b/2 : ℕ)+(b%2 : ℕ)-portLoad d 0 := by
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hmov : p⁻¹ 0 ≠ 0 := fun hf => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) hf)
  obtain ⟨filling,hmatch,hdisp⟩ := packet_gap_filling hd hcover hmov W hoff r hedge hr hgap
  obtain ⟨w,he,hl⟩ := finite_gap_packet_word_bound hn hd hm hroot hcover W hoff r hedge hr.1 hr.2
    hwidth filling hmatch start finish hxy hy
  refine ⟨w,he,?_⟩
  simpa only [hdisp] using hl

#print axioms packet_gap_filling
#print axioms geometric_gap_word_bound
end LRX.FiniteWindow
