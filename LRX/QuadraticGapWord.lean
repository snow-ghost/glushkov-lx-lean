import LRX.FiniteQuadraticGap
import LRX.InternalGapWord

/-! A literal internal-gap word with a nonnegative service price satisfying
the quadratic bound for the original gap displacements. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem packet_gap_cost_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hr : PrunedLift.InCore p d 0 r)
    (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)+(FiniteCuts.gapCost filling : ℤ)-portLoad d 0 := by
  obtain ⟨w,he,hl⟩ := two_boundary_packet_route hn hd hm hroot hcover W hoff r hedge hr.1 hr.2
    hwidth filling hmatch start finish hxy hy
  have hload := gap_boundary_port_load hd W hoff r hedge filling hmatch
    (fun i => narrow_window_displacement hd (majorized_short hd hm) W hwidth filling hmatch i)
  rw [← hload] at hl
  have hK := FiniteCuts.charge_le_gapCost filling start.val finish.val hxy hy
  unfold FiniteCuts.cycleCharge at hK
  exact ⟨w,he,by omega⟩

theorem internal_gap_quadratic_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hr : PrunedLift.InCore p d 0 r)
    (hgap : ∀ i, Contains W i → ¬PrunedLift.InCore p d 0 i)
    (hvisit : b=0 ∨ ∃ i x : Fin n, PrunedLift.InCore p d 0 i ∧ Contains W x ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ K : ℕ, 2*(∑ i : Fin b, |d (embed W i)|)+(K : ℤ)^2 ≤ (b : ℤ)^2 ∧
      ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
        (w.length : ℤ) ≤
          (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
          (∑ i : Fin n, |d i|)+(K : ℤ)-portLoad d 0 := by
  have hwidth : 2*b ≤ n := by
    rcases hvisit with hz | ⟨i,x,hi,hx,ht⟩
    · omega
    · have h := PrunedLift.internal_gap_width hd hm r b (by omega)
        (fun j hj hj' => hgap j (by unfold Contains; omega))
        ⟨i,x,hi,by unfold Contains at hx; omega,by unfold Contains at hx; omega,ht⟩
      omega
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hmov : p⁻¹ 0 ≠ 0 := fun hf => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) hf)
  obtain ⟨filling,hmatch,hdisp⟩ := packet_gap_filling hd hcover hmov W hoff r hedge hr hgap
  refine ⟨FiniteCuts.gapCost filling,?_,?_⟩
  · simpa only [hdisp] using FiniteCuts.gapCost_quadratic filling
  · exact packet_gap_cost_word hn hd hm hroot hcover W hoff r hedge hr hwidth filling hmatch start finish hxy hy

#print axioms packet_gap_cost_word
#print axioms internal_gap_quadratic_word
end LRX.FiniteWindow
