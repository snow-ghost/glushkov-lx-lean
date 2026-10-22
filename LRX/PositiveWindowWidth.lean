import LRX.WindowReversalInversionBudget

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

theorem matching_outside (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (j : Fin n) (hj : ¬Contains W j) :
    ¬Contains W (p j) := by
  rw [← outside_factor_outside W p f j hj]
  exact fixes_window_outside W (outsideFactor W p f) (outside_factor_embed W p f hmatch) j hj

/-- Positive load immediately before an invariant window must jump over its whole width. -/
theorem positive_boundary_window_width (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i))
    (hshort : ∀ i, 2*|displacement p i| < (n : ℤ))
    (r : Fin n) (hr : r.val+1=W.offset) (hpos : 0 < portLoad (displacement p) r) :
    2*(b+1)<n := by
  rw [port_load_eq_twice_half] at hpos
  have hh : 0 < halfLoad p W.offset := by rw [← hr]; omega
  obtain ⟨i,hi⟩ := Finset.card_pos.mp hh
  obtain ⟨hleft,hright⟩ := (mem_forward p W.offset i).mp hi
  have hout : ¬Contains W i := by unfold Contains; omega
  have hpout := matching_outside W p f hmatch i hout
  unfold Contains at hpout
  have hj : W.offset+b ≤ (p i).val := by omega
  have hs := hshort i
  have hab := le_abs_self (displacement p i)
  unfold displacement at hs hab
  omega

#print axioms positive_boundary_window_width
end LRX.FiniteWindow
