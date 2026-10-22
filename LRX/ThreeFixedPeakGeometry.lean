import LRX.TwoComponentReducedPeak

set_option maxHeartbeats 800000

namespace LRX.FiniteCuts

/-- The three-fixed row, whose parity and energy are forced by activity,
is incompatible with the common C9/C10 interval envelope. -/
theorem three_fixed_peak_scalar_impossible (m a v r U S2 : ℤ)
    (ha : a=2 ∨ a=3) (hv : 2 ≤ v) (hr : a+4 ≤ r)
    (hU : 1 ≤ U) (hU2 : U ≤ 2) (hm : 2*v+2+U ≤ m)
    (hcap : S2 ≤ (m-1)*(2*m+1-r))
    (henv : S2 ≤ (m-1)^2+(m+2-r)^2)
    (harea : (2*m+1-r)^2-2*S2+2*(2*m-r)*a+a^2+1 ≤ 4)
    (hdensity : 2*(m*(m+1)-2) ≤ 4*U*(2*m+1-v-a-U)+S2) : False := by
  have ha2 : 2 ≤ a := by omega
  have hm7 : 7 ≤ m := by omega
  have hr12 : r ≤ 12 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ m-1 by omega) (show 0 ≤ r-13 by omega)
    rcases ha with ha | ha <;> subst a <;> interval_cases U <;> nlinarith
  have hr6 : 6 ≤ r := by omega
  rcases ha with ha | ha <;> subst a <;> interval_cases U <;> interval_cases r <;> nlinarith

#print axioms three_fixed_peak_scalar_impossible
end LRX.FiniteCuts
