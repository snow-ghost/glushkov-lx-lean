import LRX.PeriodicWindowRightProfile
import LRX.RootCyclePorts

/-! Two actual boundary routes for an invariant gap; choose the cheaper word.
Both words have the same required initial and final orientations. -/
namespace LRX.FiniteWindow
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem two_boundary_window_route (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hcycle : (p⁻¹).SameCycle 0 r)
    (hwidth : 2*b ≤ n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (start finish : Fin n) (hxy : start.val ≤ finish.val) (hy : finish.val ≤ b) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)+
        min ((start.val : ℤ)+(finish.val : ℤ)-portLoad d 0-FiniteCuts.cycleLeftLoad filling finish.val)
          (2*(b : ℤ)-(start.val : ℤ)-(finish.val : ℤ)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling start.val) := by
  have hr : r ≠ 0 := by intro h; rw [h,Fin.val_zero,hoff] at hedge; omega
  have hanchor : (r-1 : Fin n).val=b := by
    rw [Fin.val_sub_one_of_ne_zero hr]
    omega
  have hshort (i : Fin n) : |d i| < (n : ℤ) := by
    have := majorized_short hd hm i
    have := abs_nonneg (d i)
    omega
  have hrootr := PrunedLift.nonzero_same_cycle hd hshort 0 r hroot hcycle
  have hstarr := PrunedLift.root_star_same_cycle p d 0 r hstar hcycle
  obtain ⟨wl,hel,hll⟩ := majorized_window_left_line hn hd hm hroot hstar W (by omega) hwidth filling
    hmatch finish.val hy start finish (by omega)
  obtain ⟨wr,her,hlr⟩ := majorized_window_right_line hn hd hm r hr hrootr hstarr W hedge hwidth filling
    hmatch start.val (by omega) start finish (by omega) (by rw [hanchor]; exact hy)
  rw [hanchor] at hlr
  by_cases h : (start.val : ℤ)+(finish.val : ℤ)-portLoad d 0-FiniteCuts.cycleLeftLoad filling finish.val ≤
      2*(b : ℤ)-(start.val : ℤ)-(finish.val : ℤ)-portLoad d (r-1)-FiniteCuts.cycleRightLoad filling start.val
  · refine ⟨wl,hel,?_⟩
    rw [min_eq_left h]
    linarith
  · refine ⟨wr,her,?_⟩
    rw [min_eq_right (by omega)]
    linarith

#print axioms two_boundary_window_route
end LRX.FiniteWindow
