import LRX.PeriodicWindowRoute
import LRX.WindowCycleSelection

/-! The cycle-profile left load is realized by an actual full-target word in
the periodic ambient graph, with automatic selection of finite child cycles. -/
namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem periodic_window_left_profile (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (y : ℕ) (hy : y ≤ b) (finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-FiniteCuts.cycleLeftLoad filling y+(finish.val : ℤ) := by
  obtain ⟨hc,hl,hparts,hpos⟩ := FiniteCuts.available_left_spec filling y
  have h := periodic_window_left_route hn hd hshort hroot hstar W hoff filling hmatch hfinite
    (FiniteCuts.availableLeftCycles filling y) hc hl hparts y hy hpos finish hfinish
  rw [FiniteCuts.available_left_discount] at h
  exact h

theorem periodic_window_left_line (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hstar : PrunedLift.RootStar p d 0) (W : Window n b) (hoff : 0 < W.offset)
    (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (y : ℕ) (hy : y ≤ b) (start finish : Fin n) (hfinish : W.offset+y ≤ finish.val+1) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      (w.length : ℤ) ≤
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d 0-FiniteCuts.cycleLeftLoad filling y+
        (start.val : ℤ)+(finish.val : ℤ) := by
  obtain ⟨w,he,hl⟩ := periodic_window_left_profile hn hd hshort hroot hstar W hoff filling hmatch hfinite
    y hy finish hfinish
  refine ⟨spin (-(start.val : ℤ)) ++ w,?_,?_⟩
  · rw [eval_append,spin_eval,he]
    simp [RotationWords.rotation,mul_assoc]
  · simp only [List.length_append,spin_length,Int.natAbs_neg,Int.natAbs_natCast,Nat.cast_add]
    linarith

#print axioms periodic_window_left_profile
#print axioms periodic_window_left_line
end LRX.FiniteWindow
