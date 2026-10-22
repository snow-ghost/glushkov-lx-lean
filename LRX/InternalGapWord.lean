import LRX.PacketGapWidth
import LRX.PacketGapFilling

/-! An internal packet gap satisfies the width premise of the paid word
estimate. Its finite filling and width are both derived from geometry. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem internal_gap_word_bound (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hr : PrunedLift.InCore p d 0 r)
    (hgap : ∀ i, Contains W i → ¬PrunedLift.InCore p d 0 i)
    (hvisit : b=0 ∨ ∃ i x : Fin n, PrunedLift.InCore p d 0 i ∧ Contains W x ∧
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (x : ℤ))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-(∑ i : Fin b, |d (embed W i)|)+
        (b*b/2 : ℕ)+(b%2 : ℕ)-portLoad d 0 := by
  have hwidth : 2*b ≤ n := by
    rcases hvisit with hz | ⟨i,x,hi,hx,ht⟩
    · omega
    · have h := PrunedLift.internal_gap_width hd hm r b (by omega)
        (fun j hj hj' => hgap j (by unfold Contains; omega))
        ⟨i,x,hi,by unfold Contains at hx; omega,by unfold Contains at hx; omega,ht⟩
      omega
  exact geometric_gap_word_bound hn hd hm hroot hcover W hoff r hedge hr hgap hwidth start finish hxy hy

#print axioms internal_gap_word_bound
end LRX.FiniteWindow
