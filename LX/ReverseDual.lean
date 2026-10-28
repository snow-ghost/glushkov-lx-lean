import LX.WordReflection
import LX.WordMetric
import Mathlib

namespace LX
open LX.Core.WordReflection
variable {n : ℕ} [NeZero n]

/-- Reflecting an inverse reverses an LX word without adding inverse
letters. This is a symmetry of the directed word metric. -/
def reverseDual (p : State n) : State n := reflection*p⁻¹*reflection

private theorem reflection_inv : (reflection : State n)⁻¹=reflection := by
  apply Equiv.ext
  intro i
  rfl

@[simp] theorem reverseDual_one : reverseDual (1 : State n)=1 := by
  simp [reverseDual]

theorem reverseDual_mul (p q : State n) : reverseDual (p*q)=reverseDual q*reverseDual p := by
  simp only [reverseDual,mul_inv_rev]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul]

@[simp] theorem reverseDual_twice (p : State n) : reverseDual (reverseDual p)=p := by
  simp only [reverseDual,mul_inv_rev,reflection_inv,inv_inv]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem reverseDual_letter (c : Letter) : reverseDual (eval (n := n) [c])=eval [c] := by
  have he : (eval (n := n) [c])⁻¹=reflection*eval [c]*reflection := by
    simpa only [eval,List.map_cons,List.map_nil,LX.Core.eval_cons,LX.Core.eval_nil,mul_one,
      LX.Core.Letter.eval_inverse] using mirror_letter_eval (n := n) c.toCore
  rw [reverseDual,he]
  simp only [mul_assoc,← mul_assoc (reflection : State n) reflection,reflection_square,one_mul,mul_one]

theorem eval_reverse_dual (w : List Letter) : eval (n := n) w.reverse=reverseDual (eval w) := by
  induction w with
  | nil => simp
  | cons c w ih =>
    rw [List.reverse_cons,eval_append,ih]
    have he : eval (n := n) (c::w)=eval [c]*eval w := by
      simpa only [List.singleton_append] using eval_append (n := n) [c] w
    rw [he,reverseDual_mul,reverseDual_letter]

theorem reverse_dual_sorting_word (p : State n) (w : List Letter)
    (hw : reverseDual p*eval w=1) : p*eval w.reverse=1 := by
  have he := congrArg reverseDual hw
  rw [reverseDual_mul,reverseDual_twice,reverseDual_one,← eval_reverse_dual] at he
  exact mul_eq_one_comm.mp he

#print axioms eval_reverse_dual
#print axioms reverse_dual_sorting_word
end LX
