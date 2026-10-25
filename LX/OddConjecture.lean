import LX.OddAntipodeLower
import LX.OddBinaryRankObstruction
import LX.OddHeadDropContradiction
import Mathlib

namespace LX
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Every odd input is sorted at the conjectured constant 9/4. All
remaining rank-two inputs contradict the two bounds on physical drops. -/
theorem odd_sorting_word_conjecture (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  by_contra hunpaid
  obtain ⟨a,_,hnlarge,_,hh,hmin,_,hR,_,_⟩ :=
    AnchoredPhases.odd_unpaid_rank_two_geometry hn5 p m hn hunpaid
  exact AnchoredPhases.rank_two_unpaid_impossible p a (by omega) (by omega) hmin hR hunpaid

theorem odd_exists_word_conjecture (hn5 : 5 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) :
    ∃ w : List Letter,eval w=p ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9 := by
  obtain ⟨w,hw,hprice⟩ := odd_sorting_word_conjecture hn5 p⁻¹ m hn
  exact ⟨w,(inv_mul_eq_one.mp hw).symm,hprice⟩

theorem odd_diameter_conjecture_upper (hn5 : 5 ≤ n) (m : ℕ) (hn : n=2*m+1) :
    (diameter n : ℚ) ≤ (3*(n : ℚ)^2-8*n+9)/4 := by
  obtain ⟨p,_,hp⟩ := Finset.exists_mem_eq_sup
    (Finset.univ : Finset (State n)) ⟨1,Finset.mem_univ _⟩ length
  obtain ⟨w,hw,hprice⟩ := odd_exists_word_conjecture hn5 p m hn
  have hd : diameter n=length p := hp
  have hlen : length p ≤ w.length := hw ▸ length_le_word w
  have hprice' : 4*(w.length : ℚ) ≤ 3*(n : ℚ)^2-8*n+9 := by exact_mod_cast hprice
  have hlen' : (length p : ℚ) ≤ w.length := by exact_mod_cast hlen
  rw [hd]
  linarith

/-- The exact directed LX diameter for every odd n > 4. -/
theorem odd_diameter_conjecture (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    (diameter n : ℚ)=(3*(n : ℚ)^2-8*n+9)/4 := by
  apply le_antisymm
  · exact odd_diameter_conjecture_upper (by omega) m hn
  · exact Antipode.odd_diameter_conjecture_lower m hm hn

#print axioms odd_sorting_word_conjecture
#print axioms odd_exists_word_conjecture
#print axioms odd_diameter_conjecture_upper
#print axioms odd_diameter_conjecture
end LX
