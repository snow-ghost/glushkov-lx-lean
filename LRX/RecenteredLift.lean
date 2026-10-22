import LRX.RotationWords

/-! Recenter a phase lift at an arbitrary port. The local target is chosen so
that paid entry and exit rotations recover the original visible permutation. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def localTarget (p : State n) (c r : Fin n) : State n :=
  (L n^r.val)⁻¹*p*(L n^(c-r).val)⁻¹

def localDisplacement (d : Fin n → ℤ) (r : Fin n) (i : Fin n) : ℤ :=
  d ((L n^r.val) i)

theorem local_target_inverse (p : State n) (c r i : Fin n) :
    (localTarget p c r).symm i=p.symm (i+r)+(c-r) := by
  change (localTarget p c r)⁻¹ i= _
  simp only [localTarget, mul_inv_rev, inv_inv, Equiv.Perm.mul_apply,
    AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
  rfl

theorem local_displacement_zero (d : Fin n → ℤ) (r : Fin n) :
    localDisplacement d r 0=d r := by
  simp [localDisplacement, AffineLift.rotation_power_apply]

theorem recentered_lift {p : State n} {d : Fin n → ℤ} (c r : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    AffineLift.IsLift (localTarget p c r) 0 (localDisplacement d r) := by
  constructor
  · unfold localDisplacement
    rw [Equiv.sum_comp (L n^r.val) d]
    exact hd.1
  · intro i
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add, add_zero, Int.cast_natCast,
      Fin.cast_val_eq_self, local_target_inverse]
    have h := AffineLift.lift_residue hd ((L n^r.val) i)
    simp only [AffineLift.rotation_power_apply, Fin.cast_val_eq_self,
      Int.cast_natCast] at h
    change i+(d ((L n^r.val) i) : Fin n)=p.symm (i+r)+(c-r)
    rw [AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
    linear_combination h

omit [NeZero n] in
theorem local_displacement_mass (d : Fin n → ℤ) (r : Fin n) :
    (∑ i : Fin n, |localDisplacement d r i|)=∑ i : Fin n, |d i| := by
  exact Equiv.sum_comp (L n^r.val) (fun i => |d i|)

def wrap (c r : Fin n) (w : List Letter) : List Letter :=
  toPort r ++ w ++ toPort (c-r)

theorem wrap_eval (p : State n) (c r : Fin n) (w : List Letter)
    (hw : eval w=localTarget p c r) : eval (wrap c r w)=p := by
  simp only [wrap, eval_append, toPort_eval, hw, localTarget]
  group

omit [NeZero n] in
theorem wrap_length (c r : Fin n) (w : List Letter) :
    (wrap c r w).length=w.length+min r.val (n-r.val)+min (c-r).val (n-(c-r).val) := by
  simp only [wrap, List.length_append, toPort_length]
  omega

omit [NeZero n] in
theorem wrap_length_le (c r : Fin n) (w : List Letter) :
    (wrap c r w).length ≤ w.length+2*(n/2) := by
  have h1 := toPort_length_le r
  have h2 := toPort_length_le (c-r)
  simp only [wrap, List.length_append]
  omega

#print axioms recentered_lift
#print axioms wrap_eval
#print axioms wrap_length
end LRX.RotationWords
