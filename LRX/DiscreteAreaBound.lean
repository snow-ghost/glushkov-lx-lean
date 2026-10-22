import LRX.DiscreteLevelWidths
import LRX.FiniteCoordinateCapacity

/-! Summing the actual superlevel widths gives a quadratic prefix-area bound. -/
namespace LRX.DiscreteLoad
open scoped BigOperators
variable {b : ℕ}

theorem triangular_width_sum (b k : ℕ) :
    (∑ h ∈ Finset.range k, ((b : ℤ)-2*(h : ℤ)-1))=(k : ℤ)*(b-k) := by
  have h := FiniteCoordinates.range_sum_twice k
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,← Finset.mul_sum]
  nlinarith

theorem prefix_area_bound (P : Profile b) (y u : ℕ) (hy : y ≤ b) (hu : u ≤ peak P)
    (hprefix : ∀ j, j ≤ y → P.height j ≤ u) :
    (area P : ℤ) ≤ (peak P : ℤ)*(b-peak P)-((peak P : ℤ)-u)*((y : ℤ)-u) := by
  have hlow : (∑ h ∈ Finset.range u, ((level P h).card : ℤ)) ≤
      ∑ h ∈ Finset.range u, ((b : ℤ)-2*(h : ℤ)-1) := by
    apply Finset.sum_le_sum
    intro h hh
    exact level_width P h (by have := Finset.mem_range.mp hh; omega)
  have hhigh : (∑ h ∈ Finset.Ico u (peak P), ((level P h).card : ℤ)) ≤
      ∑ h ∈ Finset.Ico u (peak P), ((b : ℤ)-y+u-2*(h : ℤ)-1) := by
    apply Finset.sum_le_sum
    intro h hh
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ico.mp hh
    exact level_width_after_prefix P y u h hy hprefix hlo hhi
  have harea : (area P : ℤ)=∑ h ∈ Finset.range (peak P), ((level P h).card : ℤ) := by
    exact_mod_cast area_by_levels P
  have hsplit := Finset.sum_range_add_sum_Ico (fun h => ((level P h).card : ℤ)) hu
  have hsum : (∑ h ∈ Finset.Ico u (peak P), ((b : ℤ)-y+u-2*(h : ℤ)-1))=
      (peak P : ℤ)*(b-peak P)-(u : ℤ)*(b-u)-((peak P : ℤ)-u)*((y : ℤ)-u) := by
    calc
      _ = (∑ h ∈ Finset.Ico u (peak P), ((b : ℤ)-2*(h : ℤ)-1))-
          ∑ _h ∈ Finset.Ico u (peak P), ((y : ℤ)-u) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro h _
        ring
      _ = _ := by
        rw [Finset.sum_Ico_eq_sub _ hu,triangular_width_sum,triangular_width_sum]
        simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul,Nat.cast_sub hu]
  rw [triangular_width_sum] at hlow
  rw [hsum] at hhigh
  omega

/-- The discrete area estimate suffices for the quadratic gap inequality
when the right-hand peak is a global peak. -/
theorem quadratic_of_right_peak (P : Profile b) (x y u : ℕ) (hy : y ≤ b) (hxy : x ≤ y)
    (hu : u ≤ peak P) (hprefix : ∀ j, j ≤ y → P.height j ≤ u)
    (K : ℤ) (hK : 0 ≤ K)
    (hleft : K ≤ (x : ℤ)+y-2*u)
    (hright : K ≤ 2*(b : ℤ)-x-y-2*peak P) :
    4*(area P : ℤ)+K^2 ≤ (b : ℤ)^2 := by
  have harea := prefix_area_bound P y u hy hu hprefix
  have hgap : (0 : ℤ) ≤ (peak P : ℤ)-u := by omega
  have hyu : K ≤ 2*((y : ℤ)-u) := by omega
  have hproduct := mul_le_mul_of_nonneg_left hyu hgap
  have hsum : K ≤ (b : ℤ)-u-peak P := by omega
  by_cases hside : (peak P : ℤ)-u ≤ K
  · have hnon : 0 ≤ (b : ℤ)-2*peak P := by omega
    have hsquare := mul_nonneg
      (show 0 ≤ ((b : ℤ)-2*peak P)-(K-((peak P : ℤ)-u)) by omega)
      (show 0 ≤ ((b : ℤ)-2*peak P)+(K-((peak P : ℤ)-u)) by omega)
    nlinarith [sq_nonneg ((peak P : ℤ)-u)]
  · have hprod := mul_nonneg hK (show 0 ≤ 2*((peak P : ℤ)-u)-K by omega)
    nlinarith [sq_nonneg ((b : ℤ)-2*peak P)]

#print axioms prefix_area_bound
#print axioms quadratic_of_right_peak
end LRX.DiscreteLoad
