import LRX.FiniteSupportPeakBounds

namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

/-- The actual fixed-position correction to finite filling energy. -/
theorem finite_energy_fixed_square (p : State b) :
    2*(∑ i, |displacement p i|)+(((b-p.support.card : ℕ) : ℤ))^2 ≤ (b : ℤ)^2 := by
  have hq := gapCost_quadratic p
  have hf := fixed_count_le_gapCost p
  have hp := mul_nonneg
    (show (0 : ℤ) ≤ (gapCost p : ℤ)-((b-p.support.card : ℕ) : ℤ) by omega)
    (show (0 : ℤ) ≤ (gapCost p : ℤ)+((b-p.support.card : ℕ) : ℤ) by positivity)
  unfold displacement
  nlinarith

/-- Energy is bounded by the area under the permutation's actual half-load peak. -/
theorem finite_energy_peak_area (p : State b) :
    (∑ i, |displacement p i|) ≤ 2*(leftPeak p b : ℤ)*((b : ℤ)-leftPeak p b) := by
  have h := DiscreteLoad.prefix_area_bound (discreteProfile p) 0 0 (by omega) (by omega)
    (fun j hj => by
      have he : j = 0 := by omega
      subst j
      exact Nat.le_of_eq (half_load_zero p))
  simp only [Nat.cast_zero,sub_zero,mul_zero] at h
  have he := discrete_area_footrule p
  have hp : DiscreteLoad.peak (discreteProfile p) = leftPeak p b := rfl
  rw [hp] at h
  unfold displacement
  nlinarith

/-- A larger supplied peak remains valid up to half the physical width. -/
theorem finite_energy_peak_upper (p : State b) (U : ℕ)
    (hpeak : leftPeak p b ≤ U) (hwidth : 2*U ≤ b) :
    (∑ i, |displacement p i|) ≤ 2*(U : ℤ)*((b : ℤ)-U) := by
  have h := finite_energy_peak_area p
  have hp := mul_nonneg
    (show (0 : ℤ) ≤ (U : ℤ)-(leftPeak p b : ℤ) by omega)
    (show (0 : ℤ) ≤ (b : ℤ)-(U : ℤ)-(leftPeak p b : ℤ) by omega)
  nlinarith

#print axioms finite_energy_fixed_square
#print axioms finite_energy_peak_area
end LRX.FiniteCuts
