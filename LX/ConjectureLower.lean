import LX.EvenAntipodeLower
import LX.OddAntipodeLower
import Mathlib

namespace LX

/-- The conjectured value is a lower bound for every n > 4. The parity
term gives constant 3 in even size and 9/4 in odd size. -/
theorem diameter_conjecture_lower (n : ℕ) [NeZero n] (hn : 5 ≤ n) :
    (3*(n : ℚ)^2-8*n+12-3*((n%2 : ℕ) : ℚ))/4 ≤ (diameter n : ℚ) := by
  have he : n%2=0 ∨ n%2=1 := by omega
  rcases he with he | he
  · rw [he,Nat.cast_zero,mul_zero,sub_zero]
    exact Antipode.even_diameter_conjecture_lower (n/2) (by omega) (by omega)
  · rw [he,Nat.cast_one,mul_one]
    have hh := Antipode.odd_diameter_conjecture_lower (n/2) (by omega) (by omega : n=2*(n/2)+1)
    convert hh using 1 <;> ring

#print axioms diameter_conjecture_lower
end LX
