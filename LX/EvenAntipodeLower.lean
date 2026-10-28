import LX.EvenBoundaryLower
import LX.EvenMinimumLocation
import Mathlib

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- All lifts and all schedules of the even candidate meet the sharp
price. Height, phase and exceptional queue cases are discharged internally. -/
theorem even_greedy_price_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) :
    3*m^2-4*m+3 ≤ inversions d+paidRotations c g := by
  by_contra hnot
  have hu : inversions d+paidRotations c g < 3*m^2-4*m+3 := by omega
  have hlo := even_unpaid_strict_lower_strip m hm hn hd hg hu
  rcases even_strict_phase_parity m hm hn hd hlo with hc | hpar
  · subst c
    have hsource := even_exception_lift m hm hn
    have hsource' := normalize_phase hsource
    change IsLift (even : State n) (((((m+3 : ℕ) : ℤ) : Fin n)) : ℤ) (evenException m) at hsource'
    have hsourceFin : IsLift (even : State n) ((((m+3 : ℕ) : Fin n)) : ℤ) (evenException m) := by
      simpa only [Int.cast_natCast] using hsource'
    have huniq := even_strict_lift_unique m (by omega) hn (((m+3 : ℕ)) : Fin n) hd hlo
    have huniqSource := even_strict_lift_unique m (by omega) hn (((m+3 : ℕ)) : Fin n) hsourceFin
      (fun i => (even_exception_strip m hm hn i).1)
    have hde : d=evenException m := huniq.trans huniqSource.symm
    rw [hde] at hg hu
    have hh := even_exception_price_lower m hm hn hsource hg
    omega
  · have hI := even_lift_inversions_lower m hm hn hd
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions d : ℤ)+1 := by exact_mod_cast hI
    have hn' : (n : ℤ)=2*m := by omega
    have hm' : (3 : ℤ) ≤ m := by omega
    have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    rw [hm1] at hI'
    have hrot : 2*(m : ℤ)^2-3*m+4 ≤ (paidRotations c g : ℤ) := by
      rcases even_strict_minimum_location m hm hn hd hlo hpar with hhead | ⟨j,hj,hmin⟩
      · have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
        have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
        have h01 : (0 : Fin n) ≠ 1 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv1] at this; omega
        have h02 : (0 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv2] at this; omega
        have hq : -(even : State n).symm 0= -(1 : Fin n) := by
          change -(1-Equiv.swap (1 : Fin n) 2 0)= -1
          rw [Equiv.swap_apply_of_ne_of_ne h01 h02,sub_zero]
        have hqval : ((-(1 : Fin n)).val : ℤ)=(n : ℤ)-1 := by
          rw [Fin.val_neg,ite_eq_right (Ne.symm h01),hv1]
          omega
        have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd 0
        rw [hq,hqval] at ht
        simp only [targets,hhead,Fin.val_zero,Nat.cast_zero,Nat.zero_sub,mul_zero,zero_add,zero_sub] at ht
        nlinarith
      · have ht := even_ordinary_token_bound (by omega : 3 ≤ n) hd hg j (by omega)
        rw [hmin] at ht
        have hj' : (m : ℤ)+2 ≤ j := by omega
        nlinarith
    have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-4*m+3 : ℕ) : ℤ) := by
      exact_mod_cast hu
    rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hu'
    push_cast at hu'
    nlinarith

/-- The even candidate is at least the conjectured diameter distance
from the identity for every even n >= 6. -/
theorem even_length_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    3*m^2-4*m+3 ≤ length (even : State n) := by
  apply (length_lower_iff_bounded_greedy_prices (by omega : 2 ≤ n) even _).mpr
  intro c d g hd _ hg
  exact even_greedy_price_lower m hm hn hd hg

theorem even_diameter_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    3*m^2-4*m+3 ≤ diameter n :=
  (even_length_lower m hm hn).trans (length_le_diameter even)

theorem even_diameter_conjecture_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) :
    (3*(n : ℚ)^2-8*n+12)/4 ≤ (diameter n : ℚ) := by
  have hh := even_diameter_lower m hm hn
  have hq : ((3*m^2-4*m+3 : ℕ) : ℚ) ≤ (diameter n : ℚ) := by exact_mod_cast hh
  rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hq
  push_cast at hq
  have hnq : (n : ℚ)=2*m := by exact_mod_cast hn
  rw [hnq]
  nlinarith

#print axioms even_length_lower
#print axioms even_diameter_conjecture_lower
end LX.Antipode
