import LRX.DiscreteAreaBound
import LRX.DiscreteProfileReflection

/-! The quadratic gap bound follows from actual discrete heights, slopes,
and the two available boundary discounts. -/
namespace LRX.DiscreteLoad
open scoped BigOperators
variable {b : ℕ}

theorem quadratic_with_right_peak (P : Profile b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b)
    (L R K : ℤ) (hK : 0 ≤ K)
    (hL : ∀ j, j ≤ y → 2*(P.height j : ℤ) ≤ L) (hR : 2*(peak P : ℤ) ≤ R)
    (hleft : K ≤ (x : ℤ)+y-L) (hright : K ≤ 2*(b : ℤ)-x-y-R) :
    4*(area P : ℤ)+K^2 ≤ (b : ℤ)^2 := by
  obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup (Finset.range (y+1)) ⟨0,by simp⟩ P.height
  have hjy : j ≤ y := by have := Finset.mem_range.mp hj; omega
  have heu : leftPeak P y=P.height j := he
  have hLu : 2*(leftPeak P y : ℤ) ≤ L := by rw [heu]; exact hL j hjy
  apply quadratic_of_right_peak P x y (leftPeak P y) hy hxy (left_peak_le P y hy)
    (fun j hj => Finset.le_sup (Finset.mem_range.mpr (by omega))) K hK <;> omega

theorem quadratic_gap (P : Profile b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b)
    (L R K : ℤ) (hK : 0 ≤ K)
    (hL : ∀ j, j ≤ y → 2*(P.height j : ℤ) ≤ L)
    (hR : ∀ j, x ≤ j → j ≤ b → 2*(P.height j : ℤ) ≤ R)
    (hleft : K ≤ (x : ℤ)+y-L) (hright : K ≤ 2*(b : ℤ)-x-y-R) :
    4*(area P : ℤ)+K^2 ≤ (b : ℤ)^2 := by
  obtain ⟨j,hj,he⟩ := peak_attained P
  by_cases hxj : x ≤ j
  · apply quadratic_with_right_peak P x y hxy hy L R K hK hL
      (by rw [← he]; exact hR j hxj hj) hleft hright
  · have hglobal : 2*(peak (reflect P) : ℤ) ≤ L := by
      rw [reflect_peak,← he]
      exact hL j (by omega)
    have hprefix : ∀ k, k ≤ b-x → 2*((reflect P).height k : ℤ) ≤ R := by
      intro k hk
      exact hR (b-k) (by omega) (by omega)
    have hx : x ≤ b := by omega
    have hleft' : K ≤ ((b-y : ℕ) : ℤ)+(b-x : ℕ)-R := by
      rw [Nat.cast_sub hy,Nat.cast_sub hx]
      omega
    have hright' : K ≤ 2*(b : ℤ)-(b-y : ℕ)-(b-x : ℕ)-L := by
      rw [Nat.cast_sub hy,Nat.cast_sub hx]
      omega
    have h := quadratic_with_right_peak (reflect P) (b-y) (b-x) (by omega) (by omega)
      R L K hK hprefix hglobal hleft' hright'
    simpa only [reflect_area] using h

#print axioms quadratic_gap
end LRX.DiscreteLoad
