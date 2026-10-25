import LRX.WordMetric
import Mathlib

/-! Reflection in the edge between positions zero and one. It exchanges L/R,
fixes X, and agrees with the word symmetry already used by the lower proof. -/
namespace LRX.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def reflection : State n where
  toFun i := 1-i
  invFun i := 1-i
  left_inv i := by change (1 : Fin n)-(1-i)=i; ring
  right_inv i := by change (1 : Fin n)-(1-i)=i; ring

@[simp] theorem reflection_apply (i : Fin n) : reflection i=1-i := rfl

@[simp] theorem reflection_twice (i : Fin n) : reflection (reflection i)=i := by
  simp only [reflection_apply]
  abel

@[simp] theorem reflection_square : (reflection : State n)*reflection=1 := by
  apply Equiv.ext
  intro i
  exact reflection_twice i

def mirror (w : List Letter) : List Letter := w.map Letter.inverse



theorem mirror_letter_eval (a : Letter) :
    a.inverse.eval (n := n)=reflection*a.eval*reflection := by
  apply Equiv.ext
  intro i
  cases a with
  | l =>
    simp [Letter.inverse, Letter.eval, L, R, Equiv.Perm.mul_apply, reflection,
      finRotate_apply, finRotate_symm_apply]
  | r =>
    simp [Letter.inverse, Letter.eval, L, R, Equiv.Perm.mul_apply, reflection,
      finRotate_apply, finRotate_symm_apply]
    abel
  | x =>
    change Equiv.swap 0 1 i=reflection (Equiv.swap 0 1 (reflection i))
    have h := Function.Injective.map_swap (reflection (n := n)).injective
      (0 : Fin n) 1 (reflection i)
    change reflection (Equiv.swap 0 1 (reflection i))=
      Equiv.swap (reflection (0 : Fin n)) (reflection 1) (reflection (reflection i)) at h
    rw [reflection_twice] at h
    have hz : reflection (0 : Fin n)=1 := by simp
    have ho : reflection (1 : Fin n)=0 := by simp
    rw [hz, ho, Equiv.swap_comm 1 0] at h
    exact h.symm

theorem mirror_eval (w : List Letter) :
    eval (n := n) (mirror w)=reflection*eval w*reflection := by
  induction w with
  | nil => simp [mirror]
  | cons a w ih =>
    simp only [mirror, List.map_cons, eval_cons] at ih ⊢
    rw [mirror_letter_eval, ih]
    simp only [mul_assoc, ← mul_assoc (reflection : State n) reflection, reflection_square, one_mul]



#print axioms mirror_eval
end LRX.WordReflection
