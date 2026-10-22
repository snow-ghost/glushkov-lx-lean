import LRX.BalancedSubsetArea
import LRX.ReversalWindowFamily

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n b : ℕ}

def windowPositions (W : Window n b) : Finset (Fin n) := Finset.univ.filter (Contains W)

theorem window_positions_image (W : Window n b) :
    windowPositions W = Finset.univ.image (embed W) := by
  ext i
  simp only [windowPositions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  exact contains_iff W i

theorem window_positions_card (W : Window n b) : (windowPositions W).card = b := by
  rw [window_positions_image,Finset.card_image_of_injective _ (embed_injective W)]
  simp

theorem sum_window_positions (W : Window n b) (g : Fin n → ℤ) :
    (∑ i ∈ windowPositions W, g i) = ∑ j : Fin b, g (embed W j) := by
  rw [window_positions_image]
  exact Finset.sum_image (fun _ _ _ _ h => embed_injective W h)

theorem matching_window_displacement (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i) = embed W (f i)) (i : Fin b) :
    displacement p (embed W i) = displacement f i := by
  unfold displacement
  rw [hm]
  simp [embed]

theorem matching_window_balance (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i) = embed W (f i)) :
    (∑ i ∈ windowPositions W, displacement p i) = 0 := by
  rw [sum_window_positions]
  simp_rw [matching_window_displacement W p f hm]
  exact (canonical_lift f).1

theorem matching_window_fixed_count (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i) = embed W (f i)) :
    (windowPositions W \ p.support).card = b-f.support.card := by
  classical
  have h : f.supportᶜ.card = (windowPositions W \ p.support).card := by
    refine Finset.card_bij (fun i _ => embed W i) ?_ ?_ ?_
    · intro i hi
      have hf : f i = i := by simpa using hi
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,contains_embed W i⟩,?_⟩
      simp only [Equiv.Perm.mem_support,not_not]
      rw [hm,hf]
    · intro i _ j _ he
      exact embed_injective W he
    · intro x hx
      obtain ⟨hx,hfix⟩ := Finset.mem_sdiff.mp hx
      obtain ⟨i,rfl⟩ := (contains_iff W x).mp (Finset.mem_filter.mp hx).2
      have hp : p (embed W i) = embed W i := by simpa using hfix
      have hf : f i = i := embed_injective W ((hm i).symm.trans hp)
      exact ⟨i,by simpa using hf,rfl⟩
  rw [Finset.card_compl,Fintype.card_fin] at h
  exact h.symm

/-- The fixed-point correction retained in the C9 family sum. -/
theorem matching_window_energy_fixed (W : Window n b) (p : State n) (f : State b)
    (hm : ∀ i, p (embed W i) = embed W (f i)) :
    2*(∑ i ∈ windowPositions W, |displacement p i|)+((windowPositions W \ p.support).card : ℤ) ≤ (b : ℤ)^2 := by
  rw [sum_window_positions,matching_window_fixed_count W p f hm]
  simp_rw [matching_window_displacement W p f hm]
  have h := finite_energy_fixed_square f
  have hsq : ((b-f.support.card : ℕ) : ℤ) ≤ (((b-f.support.card : ℕ) : ℤ))^2 := by
    by_cases hz : b-f.support.card = 0
    · simp [hz]
    · have hh := mul_nonneg (show (0 : ℤ) ≤ (b-f.support.card : ℕ) by positivity)
        (show (0 : ℤ) ≤ ((b-f.support.card : ℕ) : ℤ)-1 by omega)
      nlinarith
  linarith

#print axioms matching_window_fixed_count
#print axioms matching_window_energy_fixed
end LRX.FiniteWindow
