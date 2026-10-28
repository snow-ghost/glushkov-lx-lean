import LX.EvenSecondFewFixed
import LX.EvenSecondOrientation
import LX.MinimumHeightPrefix
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- A minimum-height source two below the even midpoint costs less than
four extra letters: its fixed prefix is paid by its own reserve. -/
theorem even_second_minimum_height_four_word (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+4) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*4 := by
  by_contra hunpaid
  have hh : 0 < height p a := by
    by_contra hnot
    have hz : height p a=0 := by omega
    obtain ⟨w,hw,hprice⟩ := candidate_word_bound (by omega : 2 ≤ n) p a
    rw [hz] at hprice
    norm_num at hprice
    have hn' : n=4 := by omega
    apply hunpaid
    refine ⟨w,hw,?_⟩
    rw [hn'] at *
    norm_num at *
    omega
  have hgap : anchorReserve p a+4 ≤ ((a-p a).val : ℤ) := by
    obtain ⟨w,hw,hprice⟩ := even_second_orientation_price p a hh hn
    by_contra hnot
    exact hunpaid ⟨w,hw,by omega⟩
  have hfix (i : Fin n) (hi : i.val ≤ (a-p a).val+1) : permutation p a i=i := by
    by_contra hnot
    have hne : backwardDepth (displacement p a) i ≠ height p a :=
      fun he => hnot ((depth_eq_height_iff_fixed p a i).mp he)
    have hdepth := (candidate_price_components p a).2 i
    obtain ⟨w,hw,hprice⟩ := even_second_head_before_phase_word p a i hn hi (by omega)
    exact hunpaid ⟨w,hw,by linarith⟩
  let r := (a-p a).val+1
  have hr : r < n := by
    by_contra hnot
    have hall (i : Fin n) : permutation p a i=i := hfix i (by have := i.isLt; dsimp [r] at *; omega)
    have hz : height p a=0 := by
      unfold height descendingPositions
      simp [hall]
    omega
  have hb := minimum_height_fixed_prefix_bound p a hmin r hr
    (fun i hi => hfix i (by dsimp [r] at hi; omega))
  dsimp [r] at hb
  omega

theorem even_second_height_four_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+4) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*4 := by
  obtain ⟨b,_,hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) (height p)
    ⟨0,Finset.mem_univ _⟩
  have hmin (c : Fin n) := hb c (Finset.mem_univ _)
  by_cases he : height p b=height p a
  · exact even_second_minimum_height_four_word p b hmin (by omega)
  · have hlt := hmin a
    obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
    exact ⟨w,hw,by linarith⟩


#print axioms even_second_height_four_word
end LX.AnchoredPhases
