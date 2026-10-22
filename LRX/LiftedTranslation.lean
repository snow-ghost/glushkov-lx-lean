import LRX.LiftedRename
import LRX.RotationWords

/-! Spatial translation commutes with literal execution, retaining the integer
positions and cursor. The finite and integer shifts are kept separate. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def translate (r : Fin n) (z : ℤ) (s : Configuration n) : Configuration n where
  physical := ⟨s.physical.tokens * (Equiv.addRight r).symm, s.physical.cursor+r⟩
  position i := s.position i+z
  cursor := s.cursor+z

theorem translate_step (r : Fin n) (z : ℤ) (a : Letter) (s : Configuration n) :
    translate r z (step a s)=step a (translate r z s) := by
  cases a with
  | l => simp [translate, step, PhysicalModel.step, increment, add_assoc, add_comm]
  | r => simp [translate, step, PhysicalModel.step, increment, sub_eq_add_neg, add_assoc, add_comm]
  | x =>
    have ht : (s.physical.tokens * Equiv.swap s.physical.cursor (s.physical.cursor+1)) *
        (Equiv.addRight r).symm =
        (s.physical.tokens * (Equiv.addRight r).symm) *
          Equiv.swap (s.physical.cursor+r) (s.physical.cursor+r+1) := by
      apply Equiv.ext
      intro i
      simp only [Equiv.Perm.mul_apply]
      congr 1
      have h := Function.Injective.map_swap (f := fun j : Fin n => j-r)
        (sub_left_injective) (s.physical.cursor+r) (s.physical.cursor+r+1) i
      have he : (s.physical.cursor+r+1)-r=s.physical.cursor+1 := by abel
      simp only [he, add_sub_cancel_right] at h
      simpa [sub_eq_add_neg, add_comm] using h.symm
    simp only [translate, step, PhysicalModel.step, increment, add_zero]
    congr 1
    · exact congrArg (fun q => PhysicalModel.Configuration.mk q (s.physical.cursor+r)) ht
    · funext i
      simp [Equiv.Perm.mul_apply, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      ring

theorem translate_run (r : Fin n) (z : ℤ) (w : List Letter) (s : Configuration n) :
    translate r z (run w s)=run w (translate r z s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => rw [run, ih, translate_step, run]

#print axioms translate_run
end LRX.LiftedModel
