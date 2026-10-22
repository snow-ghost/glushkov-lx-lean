import LRX.TwoBlockArbitraryPorts
import LRX.GapCostInversionDeficit

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem two_block_choose_identity (a : ℕ) (ha : a ≤ n) :
    (n.choose 2 : ℤ)=(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ)+(a : ℤ)*((n-a : ℕ) : ℤ) := by
  have hn := twice_choose_two_int n
  have hA := twice_choose_two_int a
  have hB := twice_choose_two_int (n-a)
  have hs : ((n-a : ℕ) : ℤ)=(n : ℤ)-(a : ℤ) := by omega
  rw [hs] at hB ⊢
  nlinarith

/-- The exact remaining numerical payment for the constructed two-block route. -/
theorem two_block_sharp_word_of_inversion_bound (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a)
    (hI : (inversionNumber p : ℤ) ≤ (a : ℤ)*((n-a : ℕ) : ℤ)-(n/2 : ℕ))
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := two_block_arbitrary_cursor_word a ha hb p hcut start finish
  have hid := two_block_choose_identity (n := n) a (by omega)
  have hbound : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by omega
  exact ⟨w,he,by exact_mod_cast hbound⟩

/-- The small-block incidence estimate suffices when the selected block has size at most floor(n/2). -/
theorem two_block_sharp_word_of_incidence_bound (a : ℕ) (ha : 2 ≤ a) (ham : a ≤ n/2)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a)
    (hI : 2*(inversionNumber p : ℤ) ≤ (n : ℤ)*((a : ℤ)-1))
    (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      w.length ≤ n.choose 2 := by
  apply two_block_sharp_word_of_inversion_bound a ha (by omega) p hcut ?_ start finish
  have hprod : 0 ≤ (a : ℤ)*((n : ℤ)-2*(a : ℤ)) :=
    mul_nonneg (by positivity) (by omega)
  have hsub : ((n-a : ℕ) : ℤ)=(n : ℤ)-(a : ℤ) := by omega
  rw [hsub]
  have hm : 2*((n/2 : ℕ) : ℤ) ≤ (n : ℤ) := by omega
  nlinarith

#print axioms two_block_sharp_word_of_inversion_bound
#print axioms two_block_sharp_word_of_incidence_bound
end LRX.FiniteCuts
