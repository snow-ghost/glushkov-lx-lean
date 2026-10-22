import LRX.PacketWindowRoutes
import LRX.WindowRightCycleSelection
import LRX.NarrowWindowLift

/-! Automatic profile discounts and both boundary lines for multi-cycle packets. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem packet_window_left_profile (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (y : ℕ) (hy : y ≤ b) (finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-FiniteCuts.cycleLeftLoad filling y+(finish.val : ℤ) := by
  obtain ⟨hc,hl,hparts,hpos⟩ := FiniteCuts.available_left_spec filling y
  have h := packet_window_left_route hn hd hshort hroot hcover W hoff filling hmatch hfinite
    (FiniteCuts.availableLeftCycles filling y) hc hl hparts y hy hpos finish hfinish
  rw [FiniteCuts.available_left_discount] at h
  exact h

theorem packet_window_left_line (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (y : ℕ) (hy : y ≤ b) (start finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-FiniteCuts.cycleLeftLoad filling y+
        (start.val : ℤ)+(finish.val : ℤ) := by
  obtain ⟨w,he,hl⟩ := packet_window_left_profile hn hd hshort hroot hcover W hoff filling hmatch hfinite
    y hy finish hfinish
  refine ⟨spin (-(start.val : ℤ)) ++ w,?_,?_⟩
  · rw [eval_append,spin_eval,he]
    simp [RotationWords.rotation,mul_assoc]
  · simp only [List.length_append,spin_length,Int.natAbs_neg,Int.natAbs_natCast,Nat.cast_add]
    linarith


theorem packet_window_right_profile (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (W : Window n b) (hedge : W.offset+b=r.val) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (x : ℕ) (hx : x ≤ b) (start finish : Fin n)
    (hcovert : start.val+1 ≤ W.offset+x) (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling x+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  obtain ⟨hc,hl,hparts,hpos⟩ := FiniteCuts.available_right_spec filling x
  have h := packet_window_right_route hn hd hshort r hr hroot hcover W hedge filling hmatch hfinite
    (FiniteCuts.availableRightCycles filling x) hc hl hparts x hx hpos start finish hcovert hfinish
  rw [FiniteCuts.available_right_discount] at h
  exact h

theorem majorized_packet_window_right_line (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (W : Window n b) (hedge : W.offset+b=r.val) (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (x : ℕ) (hx : x ≤ b) (start finish : Fin n)
    (hcovert : start.val+1 ≤ W.offset+x) (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling x+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  have hs := majorized_short hd hm
  exact packet_window_right_profile hn hd (fun i => by have := hs i; have := abs_nonneg (d i); omega)
    r hr hroot hcover W hedge filling hmatch
    (fun i => narrow_window_displacement hd hs W hwidth filling hmatch i) x hx start finish hcovert hfinish


theorem majorized_packet_window_left_line (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (y : ℕ) (hy : y ≤ b) (start finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-FiniteCuts.cycleLeftLoad filling y+
        (start.val : ℤ)+(finish.val : ℤ) := by
  have hs := majorized_short hd hm
  apply packet_window_left_line hn hd (fun i => by have := hs i; have := abs_nonneg (d i); omega)
    hroot hcover W hoff filling hmatch
    (fun i => narrow_window_displacement hd hs W hwidth filling hmatch i) y hy start finish hfinish

#print axioms majorized_packet_window_left_line
#print axioms majorized_packet_window_right_line
end LRX.FiniteWindow
