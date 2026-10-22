import LRX.ShallowRotation
import LRX.ShallowCycleNeighbor

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def Shallow (p : State n) : Prop :=
  (∑ i : Fin n, |displacement p.symm i|)=
    (LiftedModel.inversionCount (fun i : Fin n => (p.symm i : ℤ)) : ℤ)+
      (p.support.card : ℤ)-1

def shiftConjugate (p : State n) (t : ℕ) : State n := (finRotate n^t)⁻¹*p*(finRotate n^t)

theorem shallow_rotate_any (p : State n) (h : Shallow p) : Shallow (rotateConjugate p) := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k => exact shallow_rotate p h

theorem shift_conjugate_succ (p : State n) (t : ℕ) :
    shiftConjugate p (t+1)=rotateConjugate (shiftConjugate p t) := by
  simp only [shiftConjugate,rotateConjugate,pow_succ,mul_inv_rev,mul_assoc]

theorem shallow_shift (p : State n) (h : Shallow p) (t : ℕ) : Shallow (shiftConjugate p t) := by
  induction t with
  | zero => simpa [shiftConjugate] using h
  | succ t ih => rw [shift_conjugate_succ]; exact shallow_rotate_any _ ih

theorem shift_conjugate_cycle {p : State n} (hp : p.IsCycle) (t : ℕ) :
    (shiftConjugate p t).IsCycle := by
  simpa only [shiftConjugate,inv_inv] using hp.conj (g := (finRotate n^t)⁻¹)

theorem shift_conjugate_apply (p : State n) (c i : Fin n) :
    shiftConjugate p c.val i=p (i+c)-c := by
  have hP (j : Fin n) : (finRotate n^c.val) j=j+c := by
    simpa only [LRX.L,Fin.cast_val_eq_self] using AffineLift.rotation_power_apply c.val j
  have hR (j : Fin n) : (finRotate n^c.val)⁻¹ j=j-c := by
    apply (finRotate n^c.val).injective
    change (finRotate n^c.val) ((finRotate n^c.val).symm j)=(finRotate n^c.val) (j-c)
    rw [Equiv.apply_symm_apply,hP,sub_add_cancel]
  simp only [shiftConjugate,Equiv.Perm.mul_apply,hP,hR]

theorem shift_conjugate_apply_shift (p : State n) (c i : Fin n) :
    shiftConjugate p c.val (i-c)=p i-c := by
  rw [shift_conjugate_apply,sub_add_cancel]

theorem shift_support (p : State n) (c i : Fin n) :
    i-c ∈ (shiftConjugate p c.val).support ↔ i ∈ p.support := by
  simp only [Equiv.Perm.mem_support,shift_conjugate_apply_shift]
  constructor
  · intro h he
    exact h (congrArg (fun j : Fin n => j-c) he)
  · intro h he
    apply h
    have hh := congrArg (fun j : Fin n => j+c) he
    simpa only [sub_add_cancel] using hh

#print axioms shallow_shift
#print axioms shift_support
end LRX.FiniteCuts
