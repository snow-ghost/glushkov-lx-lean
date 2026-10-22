import LRX.ExactServiceRoute
import LRX.ReflectedClosedService

/-! Reflection of full integer execution, with a label-dependent offset
which fixes the canonical integer positions at every initial port. -/
namespace LRX.WordReflection
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open LiftedModel
variable {n : ℕ} [NeZero n]

def reflectConfiguration (s : Configuration n) : Configuration n where
  physical := ⟨reflection*s.physical.tokens*reflection, -s.physical.cursor⟩
  position i := (i : ℤ)+(reflection i : ℤ)-s.position (reflection i)
  cursor := -s.cursor

theorem reflect_step (a : Letter) (s : Configuration n) :
    reflectConfiguration (step a s)=step a.inverse (reflectConfiguration s) := by
  cases a with
  | l => simp [reflectConfiguration, step, PhysicalModel.step, Letter.inverse, increment, sub_eq_add_neg, add_comm]
  | r => simp [reflectConfiguration, step, PhysicalModel.step, Letter.inverse, increment, sub_eq_add_neg, add_comm]
  | x =>
    have hswap : Equiv.swap s.physical.cursor (s.physical.cursor+1)*reflection=
        reflection*Equiv.swap (-s.physical.cursor) (-s.physical.cursor+1) := by
      apply Equiv.ext
      intro i
      have h := Function.Injective.map_swap (reflection (n := n)).injective
        (-s.physical.cursor) (-s.physical.cursor+1) i
      have h0 : reflection (-s.physical.cursor)=s.physical.cursor+1 := by simp; ring
      have h1 : reflection (-s.physical.cursor+1)=s.physical.cursor := by simp
      rw [h0,h1] at h
      simpa only [Equiv.Perm.mul_apply, Equiv.swap_comm (s.physical.cursor+1) s.physical.cursor] using h.symm
    have ht : reflection*(s.physical.tokens*Equiv.swap s.physical.cursor (s.physical.cursor+1))*reflection=
        (reflection*s.physical.tokens*reflection)*Equiv.swap (-s.physical.cursor) (-s.physical.cursor+1) := by
      simp only [mul_assoc, hswap]
    have he (i j : Fin n) : reflection i=j ↔ i=reflection j := by
      constructor
      · intro h; rw [← h, reflection_twice]
      · intro h; rw [h, reflection_twice]
    simp only [reflectConfiguration, step, PhysicalModel.step, Letter.inverse, increment, add_zero]
    congr 1
    · exact congrArg (fun q => PhysicalModel.Configuration.mk q (-s.physical.cursor)) ht
    · funext i
      have h0 : reflection (-s.physical.cursor)=s.physical.cursor+1 := by simp; ring
      have h1 : reflection (-s.physical.cursor+1)=s.physical.cursor := by simp
      simp only [Equiv.Perm.mul_apply, h0, h1, he]
      ring

theorem reflect_run (w : List Letter) (s : Configuration n) :
    reflectConfiguration (run w s)=run (mirror w) (reflectConfiguration s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    simp only [run, mirror, List.map_cons] at *
    rw [ih, reflect_step]

theorem reflect_at_port (r : Fin n) (z : ℤ) :
    reflectConfiguration (atPort r z)=atPort (-r) (-z) := by
  simp [reflectConfiguration, atPort]

#print axioms reflect_run
#print axioms reflect_at_port
end LRX.WordReflection
