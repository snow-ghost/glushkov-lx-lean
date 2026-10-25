import LX.MatchingFixedNeighbors
import Mathlib

namespace LX.CycleGeometry
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Even displacement is preserved along every actual cycle, expressed
inside the cyclic additive group so that the seam is handled as well. -/
theorem same_cycle_even_difference (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : q.SameCycle i j) : Even (j-i) := by
  obtain ⟨k,hk⟩ := hij.exists_nat_pow_eq
  have hp : ∀ k : ℕ,Even ((q^k) i-i) := by
    intro k
    induction k with
    | zero => simpa using (even_zero : Even (0 : Fin n))
    | succ k ih =>
      have hs := (he ((q^k) i)).add ih
      simpa only [pow_succ',Equiv.Perm.mul_apply,sub_add_sub_cancel] using hs
  rw [← hk]
  exact hp k

/-- In even dimension, a cycle whose displacements are even cannot
contain two linearly neighboring physical positions. -/
theorem even_displacement_no_neighbor_cycle (hn2 : 2 ≤ n) (hn : Even n)
    (q : State n) (he : ∀ i : Fin n,Even (q i-i))
    (i j : Fin n) (hij : i.val+1=j.val) : ¬q.SameCycle i j := by
  intro hs
  have hd := same_cycle_even_difference q he i j hs
  have hj : i+1=j := LX.MatchingGeometry.eq_add_of_value_add i j 1 hij
  rw [← hj] at hd
  have hdiff : i+1-i=(1 : Fin n) := by ring
  rw [hdiff] at hd
  have hm := (Fin.even_iff_mod_of_even hn).mp hd
  norm_num [Nat.mod_eq_of_lt (by omega : 1 < n)] at hm

end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]


end LX.AnchoredPhases
