import LRX.ComponentShortArrowDeficit
import LRX.ExchangeReserveNonnegative

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual fixed-position count obeys the quadratic activity constraint. -/
theorem canonical_fixed_activity_square (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) :
    (((n-p.support.card : ℕ) : ℤ))^2 ≤
      4*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|))+(n%2 : ℕ) := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have hmass := ZeroGap.active_mass_cap hd hmaj
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hf : ((n-p.support.card : ℕ) : ℤ) = (n : ℤ)-(p.support.card : ℤ) := by omega
  have hhalf : 2*(p.support.card/2) ≤ p.support.card := by omega
  have hprod : 0 ≤ ((n : ℤ)-2*((p.support.card/2 : ℕ) : ℤ)-((n-p.support.card : ℕ) : ℤ))*
      ((n : ℤ)-2*((p.support.card/2 : ℕ) : ℤ)+((n-p.support.card : ℕ) : ℤ)) :=
    mul_nonneg (by omega) (by omega)
  have hQ : 4*((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))+(n%2 : ℕ) = (n : ℤ)^2 := by
    have hn : (n : ℤ) = 2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
    have hp : n%2 = 0 ∨ n%2 = 1 := by omega
    rcases hp with hp | hp <;> rw [hp] at hn ⊢ <;>
      simp only [Nat.cast_zero,Nat.cast_one,add_zero] at hn ⊢ <;> nlinarith
  nlinarith

/-- Nonnegativity of the actual activity credit A0=2 epsilon+parity-fixed. -/
theorem canonical_activity_credit_nonneg (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) :
    0 ≤ 2*(((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|))+
      (n%2 : ℕ)-((n-p.support.card : ℕ) : ℤ) := by
  let f := n-p.support.card
  let ε : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  have h := canonical_fixed_activity_square p hmaj
  change (f : ℤ)^2 ≤ 4*ε+(n%2 : ℕ) at h
  change 0 ≤ 2*ε+(n%2 : ℕ)-(f : ℤ)
  have hp0 : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have hp1 : ((n%2 : ℕ) : ℤ) ≤ 1 := by omega
  by_cases hf : f ≤ 1
  · have hf' : f = 0 ∨ f = 1 := by omega
    rcases hf' with hf' | hf' <;> rw [hf'] at h ⊢ <;>
      norm_num only [Nat.cast_zero,Nat.cast_one,zero_pow,one_pow,sub_zero] at h ⊢ <;> omega
  · have hh := mul_nonneg (show (0 : ℤ) ≤ f by positivity) (show (0 : ℤ) ≤ (f : ℤ)-2 by omega)
    nlinarith

#print axioms canonical_fixed_activity_square
#print axioms canonical_activity_credit_nonneg
end LRX.FiniteCuts
