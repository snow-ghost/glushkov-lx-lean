import LRX.TwoBlockReflectionCoordinates

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- Shifting the fixed-point cut once more places the two reflected blocks consecutively. -/
theorem reflection_recenter_one_two_blocks (hn : 2 ≤ n) (p : State n)
    (href : ∀ i : Fin n, p.symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n)) :
    ∀ i : Fin n, (localTarget p 0 1).symm i=((n/2-1 : ℕ) : Fin n)-i := by
  have hsum : (n-1)/2+(n/2-1)+2=n := by omega
  have hs : (((n-1)/2 : ℕ) : Fin n)+((n/2-1 : ℕ) : Fin n)+2=0 := by
    have h := congrArg (fun k : ℕ => (k : Fin n)) hsum
    simpa using h
  intro i
  rw [local_target_inverse,href]
  simp only [Int.cast_natCast,zero_sub]
  linear_combination -hs

/-- Actual recentered coordinates equal the canonical two-block displacements. -/
theorem reflection_recenter_one_canonical (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (href : ∀ i : Fin n, p.symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n)) :
    localDisplacement d 1=displacement (localTarget p 0 1).symm := by
  apply two_block_reflection_lift_canonical hn
    (recentered_lift (0 : Fin n) 1 (by simpa using hd))
    (fun i => hshort ((L n^(1 : Fin n).val) i))
  exact reflection_recenter_one_two_blocks hn p href

#print axioms reflection_recenter_one_two_blocks
#print axioms reflection_recenter_one_canonical
end LRX.FiniteCuts
