import LX.AdjacentBoundaryPrice
import LX.ShallowCutShift
import LX.ShallowRotation
import LX.WordMetric
import Mathlib

namespace LX.FiniteJoin
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

def depthDeficit (q : State n) : ℤ :=
  (∑ i, |displacement q i|)-(inversionNumber q : ℤ)

theorem shift_depth_deficit (q : State n) (t : ℕ) :
    depthDeficit (shiftConjugate q t)=depthDeficit q := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    induction t with
    | zero => simp [shiftConjugate,depthDeficit]
    | succ t ih =>
      rw [shift_conjugate_succ]
      exact (rotation_energy_minus_inversions (shiftConjugate q t)).trans ih

theorem shift_neighbor_swap (q : State n) (u : Fin n) :
    shiftConjugate (q*Equiv.swap u (u+1)) u.val=shiftConjugate q u.val*Equiv.swap 0 1 := by
  apply Equiv.ext
  intro i
  rw [shift_conjugate_apply]
  change q (Equiv.swap u (u+1) (i+u))-u=shiftConjugate q u.val (Equiv.swap 0 1 i)
  rw [shift_conjugate_apply]
  congr 1
  apply congrArg q
  have hh := Function.Injective.map_swap (f := fun j : Fin n => j+u) (add_left_injective u) 0 1 i
  simpa only [zero_add,add_zero,add_comm] using hh.symm

/-- Joining two fixed neighbors increases finite depth minus inversions by
exactly one. Moving the finite cut first handles the seam without a separate
unproved formula for exchanging the first and last positions. -/
theorem fixed_neighbor_deficit (hn : 2 ≤ n) (q : State n) (u : Fin n)
    (hu : q u=u) (hv : q (u+1)=u+1) :
    depthDeficit (q*Equiv.swap u (u+1))=depthDeficit q+1 := by
  let Q := shiftConjugate q u.val
  have hQ0 : Q 0=0 := by
    simp only [Q,shift_conjugate_apply,zero_add,hu,sub_self]
  have hQ1 : Q 1=1 := by
    change shiftConjugate q u.val 1=1
    rw [shift_conjugate_apply,add_comm (1 : Fin n) u,hv]
    abel
  have h01 : (1 : Fin n).val=(0 : Fin n).val+1 := by
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hmass := adjacent_boundary_mass_price Q 0 1 h01
    (by rw [hQ0]) (by rw [hQ1])
  have hI := adjacent_raising_inversion_price Q 0 1 h01 (by rw [hQ0,hQ1]; omega)
  have hprice : depthDeficit (Q*Equiv.swap 0 1)=depthDeficit Q+1 := by
    unfold depthDeficit
    rw [hmass,hI]
    push_cast
    ring
  calc
    _ = depthDeficit (shiftConjugate (q*Equiv.swap u (u+1)) u.val) := (shift_depth_deficit _ _).symm
    _ = depthDeficit (Q*Equiv.swap 0 1) := by rw [shift_neighbor_swap]
    _ = depthDeficit Q+1 := hprice
    _ = depthDeficit q+1 := by rw [shift_depth_deficit]

#print axioms shift_depth_deficit
#print axioms fixed_neighbor_deficit
end LX.FiniteJoin
