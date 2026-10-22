import LRX.CanonicalWindowBoundaryLoad
import LRX.WindowCycleSelection
import LRX.WindowRightCycleSelection

namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem canonical_window_two_boundary_rank (hn : 2 ≤ n) (p G : State n)
    (hbelow : FiniteRankOrder.Below p G) (u v : Fin n)
    (hu : G.symm u ≠ u) (hv : G.symm v ≠ v)
    (hcoveru : PrunedLift.PacketCover G (FiniteCuts.displacement G.symm) u)
    (hcoverv : PrunedLift.PacketCover G (FiniteCuts.displacement G.symm) v)
    (W : Window n b) (hoff : W.offset=u.val+1) (hedge : W.offset+b=v.val)
    (filling : State b) (hmatch : ∀ i, G.symm (embed W i)=embed W (filling i))
    (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) (start finish : Fin n)
    (hpositions : (start.val=u.val+x ∧ finish.val=u.val+y) ∨
      (start.val=u.val+y ∧ finish.val=u.val+x)) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (FiniteCuts.inversionNumber p : ℤ)+
        (∑ i, |FiniteCuts.displacement G.symm i|)-portLoad (FiniteCuts.displacement G.symm) u+
        min ((x : ℤ)+(y : ℤ)-FiniteCuts.cycleLeftLoad filling y)
          (2*(b : ℤ)-(x : ℤ)-(y : ℤ)-FiniteCuts.cycleRightLoad filling x) := by
  have hmin : min start.val finish.val=u.val+x := by rcases hpositions with h | h <;> omega
  have hmax : max start.val finish.val=u.val+y := by rcases hpositions with h | h <;> omega
  have hslo : u.val ≤ start.val := by omega
  have hflo : u.val ≤ finish.val := by omega
  have hshi : start.val ≤ u.val+b := by omega
  have hfhi : finish.val ≤ u.val+b := by omega
  have hv0 : v ≠ 0 := by intro h; rw [h,Fin.val_zero] at hedge; omega
  have hanchor : (v-1 : Fin n).val=u.val+b := by
    rw [Fin.val_sub_one_of_ne_zero hv0]
    omega
  obtain ⟨hcl,hdl,hpl,hposl⟩ := FiniteCuts.available_left_spec filling y
  obtain ⟨hcr,hdr,hpr,hposr⟩ := FiniteCuts.available_right_spec filling x
  obtain ⟨wl,hel,hll⟩ := canonical_window_left_rank_route hn p G hbelow u hu hcoveru W hoff filling hmatch
    (FiniteCuts.availableLeftCycles filling y) hcl hdl hpl y hy hposl start finish (by omega) (by omega) (by omega)
  obtain ⟨wr,her,hlr⟩ := canonical_window_right_rank_route hn p G hbelow v hv0 hv hcoverv W hedge filling hmatch
    (FiniteCuts.availableRightCycles filling x) hcr hdr hpr x (by omega) hposr start finish (by omega) (by omega) (by omega)
  rw [FiniteCuts.available_left_discount] at hll
  rw [FiniteCuts.available_right_discount,hanchor,
    ← canonical_window_boundary_load G W filling hmatch u v hoff hedge] at hlr
  have hsum : (start.val : ℤ)+(finish.val : ℤ)=2*(u.val : ℤ)+(x : ℤ)+(y : ℤ) := by
    have hh : start.val+finish.val=2*u.val+x+y := by rcases hpositions with h | h <;> omega
    exact_mod_cast hh
  by_cases hh : (x : ℤ)+(y : ℤ)-FiniteCuts.cycleLeftLoad filling y ≤
      2*(b : ℤ)-(x : ℤ)-(y : ℤ)-FiniteCuts.cycleRightLoad filling x
  · refine ⟨wl,hel,?_⟩
    rw [min_eq_left hh]
    omega
  · refine ⟨wr,her,?_⟩
    rw [min_eq_right (by omega)]
    push_cast at hlr
    omega

#print axioms canonical_window_two_boundary_rank
end LRX.FiniteWindow
