import LX.OddExceptionLower
import LX.OddMiddleLower
import LX.OddOuterLower
import LX.Small5Exact
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Every phase of every balanced lift of the odd candidate meets the
sharp price; the middle, outer and exceptional cases are exhaustive. -/
theorem odd_greedy_price_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift (odd m (by omega) hn) (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-m+1 ≤ inversions d+paidRotations c g := by
  by_cases hlo : c.val ≤ 1
  · exact odd_outer_greedy_price_lower m hm hn (Or.inl hlo) hd hg
  · by_cases hmid : c.val ≤ m+1
    · exact odd_middle_greedy_price_lower m (by omega) hn (by omega) hmid hd hg
    · by_cases he : c.val=m+2
      · have hc : c=((m+2 : ℕ) : Fin n) := by
          apply Fin.ext
          have hh : (((m+2 : ℕ)) : Fin n).val=m+2 := Nat.mod_eq_of_lt (by omega)
          omega
        exact odd_exception_phase_lower m (by omega) hn hc hd hg
      · exact odd_outer_greedy_price_lower m hm hn (Or.inr (by omega)) hd hg

theorem odd_length_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m+1) :
    3*m^2-m+1 ≤ length (odd m (by omega) hn) := by
  apply (length_lower_iff_bounded_greedy_prices (by omega : 2 ≤ n) (odd m (by omega) hn) _).mpr
  intro c d g hd _ hg
  exact odd_greedy_price_lower m hm hn hd hg

/-- Sharp odd lower bound for all odd n >= 5, including the independently
checked five-position base case. -/
theorem odd_diameter_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    3*m^2-m+1 ≤ diameter n := by
  by_cases hm2 : m=2
  · subst m
    have hn5 : n=5 := by omega
    subst n
    change 11 ≤ diameter 5
    exact LX.Small5.diameter_lower
  · exact (odd_length_lower m (by omega) hn).trans (length_le_diameter (odd m (by omega) hn))

theorem odd_diameter_conjecture_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1) :
    (3*(n : ℚ)^2-8*n+9)/4 ≤ (diameter n : ℚ) := by
  have hh := odd_diameter_lower m hm hn
  have hq : ((3*m^2-m+1 : ℕ) : ℚ) ≤ (diameter n : ℚ) := by exact_mod_cast hh
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : m ≤ 3*m^2)] at hq
  push_cast at hq
  have hnq : (n : ℚ)=2*m+1 := by exact_mod_cast hn
  rw [hnq]
  nlinarith

#print axioms odd_length_lower
#print axioms odd_diameter_conjecture_lower
end LX.Antipode
