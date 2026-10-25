import Mathlib

/-! Integer coordinate identities for the corrected periodic buffer service.
No cycle coverage or global sorting cost is assumed or asserted here. -/
namespace LRX.PeriodicBuffer

def passive (M H y : ℤ) : ℤ := y + 1 + (y-H)/M

def buffer (M H y : ℤ) : ℤ := H + (M+1)*((y-H)/M)

def contract (n x : ℤ) : ℤ := x + (-x)/n

theorem quotient_eq_of_bounds {M x q : ℤ} (hM : 0 < M)
    (hlo : q*M ≤ x) (hhi : x < (q+1)*M) : x/M = q := by
  have ha := (Int.le_ediv_iff_mul_le hM).mpr hlo
  have hb := (Int.ediv_lt_iff_lt_mul hM).mpr hhi
  omega


def edgePassages (n a b : ℤ) : ℤ := |(-b)/n-(-a)/n|



end LRX.PeriodicBuffer
