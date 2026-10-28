import LX.CompleteMappingConjecture
import LX.OddGlobalHeight
import LX.Small4
import LX.Small6
import LX.SmallConstantPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem conjecture_small_word (hn4 : 4 ≤ n) (hn6 : n ≤ 6) (p : State n)
    (m e : ℕ) (he : e ≤ 1) (hn : n=2*m+e) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ)) := by
  have hc : n=4 ∨ n=5 ∨ n=6 := by omega
  rcases hc with rfl | rfl | rfl
  · obtain ⟨w,hw,hprice⟩ := LX.Small4.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  · obtain ⟨w,hw,hprice⟩ := LX.Small5.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩
  · obtain ⟨w,hw,hprice⟩ := LX.Small6.sharp_words p⁻¹
    exact ⟨w,by rw [hw,mul_inv_cancel],by norm_num; omega⟩

/-- Source selection at the conjectured parity constants, independent of the older
constant-thirty-two reductions. -/
theorem conjecture_unpaid_minimum (hn4 : 4 ≤ n) (p : State n) (m e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      ∀ b,height p a ≤ height p b := by
  have hlower (b : Fin n) : m ≤ height p b+1 := by
    by_contra hnot
    interval_cases e
    · by_cases hb : height p b+2=m
      · obtain ⟨w,hw,hprice⟩ := even_second_height_four_word p b (by omega)
        exact hunpaid ⟨w,hw,by norm_num; omega⟩
      · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
        exact hunpaid ⟨w,hw,by norm_num; omega⟩
    · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
      exact hunpaid ⟨w,hw,by norm_num; omega⟩
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
      obtain ⟨w,hw,hprice⟩ := complete_mapping_conjecture_word p (odd_maximal_minima_complete p m hn hheight) hn4
      exact hunpaid ⟨w,hw,by norm_num; omega⟩
  obtain ⟨a,ha,hh⟩ := hex
  exact ⟨a,ha,hh,fun b => by have := hlower b; omega⟩

#print axioms conjecture_unpaid_minimum
end LX.AnchoredPhases
