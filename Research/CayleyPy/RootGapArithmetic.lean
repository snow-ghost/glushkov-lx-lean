import Mathlib

set_option linter.style.header false

/-!
Kernel-checked arithmetic for the phase34 root-gap argument.

The passage from permutations and global Lorenz bounds to the displayed
integer hypotheses is NOT formalized here. In particular, these theorems
do not assert an unconditional Cayley-graph diameter bound.
-/

namespace CayleyPy.RootGapArithmetic

theorem envelope_identity
    (n r s e eta o H Q G delta J squares F N p : ℤ)
    (hn : n = r + s)
    (hQ : 4 * Q = n ^ 2 - p)
    (hG : 4 * G = (s + eta) ^ 2 - p)
    (hdelta : delta = Q - G - H)
    (hJ : 2 * J = 2 * squares - (s - e + o))
    (hF : F = 2 * delta - r + 1 + J)
    (hN : 2 * N = n * (n - 1)) :
    2 * (F - (N + 1)) =
      2 * squares - (s + eta) ^ 2 - r + e - o - 4 * H := by
  subst n
  nlinarith only [hQ, hG, hdelta, hJ, hF, hN]

/-- A half-size bound on every gap bounds the sum of their squared sizes. -/
theorem nondominant_square_sum {ι : Type*} (T : Finset ι) (g : ι → ℤ)
    (s : ℤ) (hs : 0 ≤ s)
    (hgap : ∀ i ∈ T, 0 ≤ g i ∧ 2 * g i ≤ s)
    (hsum : ∑ i ∈ T, g i ≤ s) :
    2 * (∑ i ∈ T, (g i) ^ 2) ≤ s ^ 2 := by
  calc
    2 * (∑ i ∈ T, (g i) ^ 2) = ∑ i ∈ T, 2 * (g i) ^ 2 := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ T, s * g i := by
      apply Finset.sum_le_sum
      intro i hi
      have h := hgap i hi
      nlinarith [mul_nonneg h.1 (sub_nonneg.mpr h.2)]
    _ = s * ∑ i ∈ T, g i := by rw [Finset.mul_sum]
    _ ≤ s * s := mul_le_mul_of_nonneg_left hsum hs
    _ = s ^ 2 := by ring

/-- The exact integer reversal energy bound, including empty families. -/
theorem nondominant_reversal_energy {ι : Type*} (T : Finset ι) (g : ι → ℤ)
    (s : ℤ) (hs : 0 ≤ s)
    (hgap : ∀ i ∈ T, 0 ≤ g i ∧ 2 * g i ≤ s)
    (hsum : ∑ i ∈ T, g i ≤ s) :
    (∑ i ∈ T, (g i) ^ 2 / 2) ≤ s ^ 2 / 4 := by
  have hsquares := nondominant_square_sum T g s hs hgap hsum
  have hhalf : 2 * (∑ i ∈ T, (g i) ^ 2 / 2) ≤ ∑ i ∈ T, (g i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    omega
  omega

/-- Payment is conditional on the original activity and strict-length caps. -/
theorem nondominant_payment
    (Q G H rootDelta gapDelta completionC m N s : ℤ)
    (hH : 0 ≤ H) (hroot : rootDelta ≤ Q - G - H)
    (hgap : gapDelta ≤ s ^ 2 / 4) (hG : s ^ 2 / 4 ≤ G)
    (hC : completionC ≤ Q - m) (hN : N = 2 * Q - m) :
    completionC + rootDelta + gapDelta ≤ N := by
  omega

def allowance (r o H e s eta : ℤ) : ℤ :=
  r + o + 4 * H + e * (2 * s - e - 1) + eta * (2 * s + 1)

/-- Only the convex concentration inequality is assumed, not realizability
of an auxiliary concentration of the smaller physical gaps. -/
theorem disparity_bound
    (E squares r s e eta o H b c : ℤ)
    (heta : eta = 0 ∨ eta = 1)
    (hidentity : 2 * E =
      2 * squares - (s + eta) ^ 2 - r + e - o - 4 * H)
    (hsum : b + c = s - e)
    (hconvex : squares ≤ b ^ 2 + c ^ 2) :
    2 * E ≤ (b - c) ^ 2 - allowance r o H e s eta := by
  have hs : s = b + c + e := by omega
  subst s
  rcases heta with rfl | rfl <;>
    dsimp [allowance] <;> nlinarith only [hidentity, hconvex]

theorem paid_of_disparity (E t B : ℤ)
    (hbound : 2 * E ≤ t ^ 2 - B) (hpaid : t ^ 2 ≤ B) : E ≤ 0 := by
  omega

theorem load_aware_payment (E t B gamma u p : ℤ)
    (hbound : 2 * E ≤ t ^ 2 - B)
    (hpaid : t ^ 2 ≤ B + 2 * gamma)
    (hallowance : gamma ≤ 2 * u - p - 1) : E + 1 + p - 2 * u ≤ 0 := by
  omega

theorem necessary_failure (E t B : ℤ)
    (hbound : 2 * E ≤ t ^ 2 - B) (hfail : ¬ E ≤ 0) : B + 2 ≤ t ^ 2 := by
  omega

theorem necessary_gap_failure (E t B u p : ℤ)
    (hbound : 2 * E ≤ t ^ 2 - B)
    (hfail : ¬ E + 1 + p - 2 * u ≤ 0) : B + 4 * u - 2 * p ≤ t ^ 2 := by
  omega

end CayleyPy.RootGapArithmetic

#print axioms CayleyPy.RootGapArithmetic.envelope_identity
#print axioms CayleyPy.RootGapArithmetic.nondominant_reversal_energy
#print axioms CayleyPy.RootGapArithmetic.disparity_bound
#print axioms CayleyPy.RootGapArithmetic.load_aware_payment
