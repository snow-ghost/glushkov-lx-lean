import LX.RankWindowQuadraticUpper

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
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

theorem complete_mapping_eighteen_word (p : State n) (hp : CompleteMapping p) (hn : 4 ≤ n) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*18 := by
  by_cases hsmall : n < 13
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn p⁻¹
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hn' : (n : ℤ) ≤ 12 := by omega
    linarith
  · let h := height p 0
    have hparity : n=2*h+1 := complete_height p hp 0
    obtain ⟨a,ha,hforward,hcorner⟩ := complete_good_anchor p hp h hparity (by omega)
    have hheight : height p a=h := by have := complete_height p hp a; omega
    obtain ⟨w,hw,hprice⟩ := odd_forward_anchor_word p a 5 (complete_majorized p hp a)
      (by omega) (by omega) ha (by omega) hcorner
    exact ⟨w,hw,by omega⟩

/-- Source selection at constant eighteen, independent of the older
constant-thirty-two reductions. -/
theorem eighteen_unpaid_minimum (hn4 : 4 ≤ n) (p : State n) (m e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*18) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      ∀ b,height p a ≤ height p b := by
  have hlower (b : Fin n) : m ≤ height p b+1 := by
    by_contra hnot
    interval_cases e
    · by_cases hb : height p b+2=m
      · obtain ⟨w,hw,hprice⟩ := even_second_height_four_word p b (by omega)
        exact hunpaid ⟨w,hw,by linarith⟩
      · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
        exact hunpaid ⟨w,hw,by linarith⟩
    · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
      exact hunpaid ⟨w,hw,by linarith⟩
  have hex : ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m := by
    interval_cases e
    · obtain ⟨a,ha⟩ := exists_global_minimum p
      have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
      rw [displacement_anchor] at hh
      exact ⟨a,ha,by have := hlower a; omega⟩
    · by_contra hnone
      have hheight (a : Fin n) (ha : GlobalMinimum p a) : height p a=m := by
        have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
        rw [displacement_anchor] at hh
        have hne : height p a+1 ≠ m := fun hh => hnone ⟨a,ha,hh⟩
        have := hlower a
        omega
      exact hunpaid (complete_mapping_eighteen_word p (odd_maximal_minima_complete p m hn hheight) hn4)
  obtain ⟨a,ha,hh⟩ := hex
  exact ⟨a,ha,hh,fun b => by have := hlower b; omega⟩

#print axioms even_second_height_four_word
#print axioms complete_mapping_eighteen_word
#print axioms eighteen_unpaid_minimum
end LX.AnchoredPhases
