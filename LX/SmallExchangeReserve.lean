import LX.EvenUnitPayment
import LX.OddUnitPayment

namespace LX.AnchoredPhases
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- The remaining inputs have at least two units of dimension-wide reserve,
for both parities. The reserve is measured at an actual global minimum. -/
theorem unpaid_dimension_reserve_at_least_two {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    2 ≤ ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) := by
  have hpar : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hpar with he | ho
  · have hh := even_unpaid_reserve_at_least_two hn4 (n/2) he ha hunpaid
    have he' : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by exact_mod_cast he
    nlinarith
  · have hh := odd_unpaid_reserve_at_least_two hn4 (n/2) ho ha hunpaid
    have ho' : (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by exact_mod_cast ho
    nlinarith

/-- Actual LX words at the target price for every input within one exchange
of the dimension-wide capacity. No parity or exceptional-shape premise remains. -/
theorem small_dimension_reserve_upper_word {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  have hh := unpaid_dimension_reserve_at_least_two hn4 ha hunpaid
  omega

#print axioms unpaid_dimension_reserve_at_least_two
#print axioms small_dimension_reserve_upper_word
end LX.AnchoredPhases
