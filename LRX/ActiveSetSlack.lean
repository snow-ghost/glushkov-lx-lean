import LRX.ExchangeReserveNonnegative

/-! The active-set energy cap supplies the parity-correct fixed-point slack
used in the connected and multiple-component routing budgets. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def fixedCount (p : State n) : ℕ := n-p.support.card

theorem fixed_count_identity (p : State n) :
    (fixedCount p : ℤ)=(n : ℤ)-(p.support.card : ℤ) := by
  unfold fixedCount
  rw [Nat.cast_sub (by simpa using Finset.card_le_univ p.support)]

theorem fixed_energy_deficit {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    (fixedCount p : ℤ)^2-(n%2 : ℕ) ≤ 4*epsilon d := by
  have hmass := ZeroGap.active_mass_cap hd hm
  have hs : (p.support.card : ℤ) ≤ n := by exact_mod_cast (show p.support.card ≤ n by simpa using Finset.card_le_univ p.support)
  have ha : 2*(p.support.card/2 : ℕ) ≤ (p.support.card : ℤ) := by omega
  have hprod := mul_nonneg (show (0 : ℤ) ≤ p.support.card-2*(p.support.card/2 : ℕ) by omega)
    (show (0 : ℤ) ≤ 2*(n : ℤ)-p.support.card-2*(p.support.card/2 : ℕ) by omega)
  have hf := fixed_count_identity p
  have hQ := floor_square_identity n
  unfold epsilon
  nlinarith

theorem fixed_slack_nonneg {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) :
    0 ≤ 2*epsilon d+(n%2 : ℕ)-(fixedCount p : ℤ) := by
  have he := epsilon_nonneg hd hm
  have hf := fixed_energy_deficit hd hm
  have hp : (0 : ℤ) ≤ (n%2 : ℕ) := by positivity
  have hp' : (n%2 : ℕ) ≤ (1 : ℤ) := by omega
  by_cases hsmall : fixedCount p ≤ 1
  · have hcases : fixedCount p=0 ∨ fixedCount p=1 := by omega
    rcases hcases with h | h <;> rw [h] at hf ⊢ <;> norm_num at hf ⊢ <;> omega
  · have hge : (2 : ℤ) ≤ fixedCount p := by omega
    nlinarith

#print axioms fixed_energy_deficit
#print axioms fixed_slack_nonneg
end LRX.FiniteGaps
