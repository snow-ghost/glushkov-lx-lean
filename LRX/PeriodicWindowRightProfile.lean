import LRX.PeriodicWindowRightRoute
import LRX.WindowRightCycleSelection
import LRX.NarrowWindowLift

/-! The full right-boundary route realizes the local cycle-profile right load. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem periodic_window_right_profile (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hstar : PrunedLift.RootStar p d r)
    (W : Window n b) (hedge : W.offset+b=r.val) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (x : ℕ) (hx : x ≤ b) (start finish : Fin n)
    (hstart : start.val+1 ≤ W.offset+x) (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling x+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  obtain ⟨hc,hl,hparts,hpos⟩ := FiniteCuts.available_right_spec filling x
  have h := periodic_window_right_route hn hd hshort r hr hroot hstar W hedge filling hmatch hfinite
    (FiniteCuts.availableRightCycles filling x) hc hl hparts x hx hpos start finish hstart hfinish
  rw [FiniteCuts.available_right_discount] at h
  exact h

theorem majorized_window_right_line (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hstar : PrunedLift.RootStar p d r)
    (W : Window n b) (hedge : W.offset+b=r.val) (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (x : ℕ) (hx : x ≤ b) (start finish : Fin n)
    (hstart : start.val+1 ≤ W.offset+x) (hfinish : finish.val ≤ (r-1 : Fin n).val) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling x+
        2*((r-1 : Fin n).val : ℤ)-(start.val : ℤ)-(finish.val : ℤ) := by
  have hs := majorized_short hd hm
  exact periodic_window_right_profile hn hd (fun i => by have := hs i; have := abs_nonneg (d i); omega)
    r hr hroot hstar W hedge filling hmatch
    (fun i => narrow_window_displacement hd hs W hwidth filling hmatch i) x hx start finish hstart hfinish

#print axioms periodic_window_right_profile
#print axioms majorized_window_right_line
end LRX.FiniteWindow
