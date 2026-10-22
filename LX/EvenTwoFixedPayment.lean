import LX.EvenAnchorPrice
import LX.EvenTwoStepPhases

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- If every global minimum has two fixed positions, exact two-step phase
changes supply a terminal anchor at the target price. This pays the entire
family, independently of its exchange reserve and finite event defect. -/
theorem even_all_minima_two_fixed_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hfixed : ∀ a : Fin n,GlobalMinimum p a → (fixedPositions (permutation p a)).card=2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  by_cases hsmall : n < 22
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  · have hheight (a : Fin n) (ha : GlobalMinimum p a) : height p a+1=m :=
      even_unpaid_global_height hn4 m hn ha hunpaid
    have hstep (a : Fin n) (ha : GlobalMinimum p a) :
        ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+2 := by
      have hh := hheight a ha
      apply maximal_even_two_fixed_next_phase ha (by omega) (hfixed a ha)
      intro b hb
      have hb' := hheight b hb
      omega
    obtain ⟨a,ha⟩ := exists_global_minimum p
    obtain ⟨b,k,hb,hklo,hkhi,hbr,hhead⟩ := two_step_terminal_anchor (by omega) ha hstep
    obtain ⟨c,hc,hcr,hlast⟩ := last_same_offset_anchor hb
    have hraw : p c-c= -(k : Fin n) := hcr.trans hbr
    have hheadc : p 0 ≠ p c-c := fun he => hhead (he.trans hcr)
    have hfinish := negative_offset_finish p c k (by omega) hraw
    have hcorner : 8 ≤ c.val+(-p c).val := by rcases hfinish with h | h <;> omega
    have hbound : c.val+(-p c).val ≤ n+11 := by rcases hfinish with h | h <;> omega
    have hhc := hheight c hc
    obtain ⟨w,hw,hprice⟩ := maximal_even_anchor_word hc (by omega) (by omega) hheadc hlast hcorner 11 hbound
    norm_num only [Nat.cast_ofNat] at hprice
    exact hunpaid ⟨w,hw,by linarith⟩

/-- Every still-unpaid even input has an actual globally minimal phase
with one fixed position. The two-fixed-phase obstruction is fully paid. -/
theorem even_unpaid_one_fixed_minimum (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card=1 := by
  by_contra hnone
  have htwo (a : Fin n) (ha : GlobalMinimum p a) : (fixedPositions (permutation p a)).card=2 := by
    have hh := even_unpaid_global_height hn4 m hn ha hunpaid
    have hf := majorized_anchor_fixed_positions p a (global_minimum_majorized ha)
    have hpos : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
      ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
    have hnot : (fixedPositions (permutation p a)).card ≠ 1 := fun he => hnone ⟨a,ha,hh,he⟩
    omega
  exact hunpaid (even_all_minima_two_fixed_upper_word hn4 p m hn htwo)

#print axioms even_all_minima_two_fixed_upper_word
#print axioms even_unpaid_one_fixed_minimum
end LX.AnchoredPhases
