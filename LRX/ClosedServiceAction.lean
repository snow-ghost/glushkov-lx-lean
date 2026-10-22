import LRX.ServiceAction
import LRX.ExactClosedService

/-! Complete state action of a closed service: the physical token permutation
is multiplied by its target, and the integer cursor is restored. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem physical_cursor_run (w : List Letter) (s : Configuration n) :
    (run w s).physical.cursor=s.physical.cursor+((w.map increment).sum : ℤ) := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih =>
    rw [run, ih]
    cases a <;> simp [step, PhysicalModel.step, increment, add_assoc, sub_eq_add_neg]

end LRX.LiftedModel
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem closed_service_cursor (service : ClosedService n) (s : LiftedModel.Configuration n) :
    (LiftedModel.run service.word s).cursor=s.cursor ∧
    (LiftedModel.run service.word s).physical.cursor=s.physical.cursor := by
  simp [LiftedModel.cursor_run, LiftedModel.physical_cursor_run, service.closed]

theorem closed_service_tokens (service : ClosedService n) (s : LiftedModel.Configuration n)
    (hport : s.physical.cursor=service.port) :
    (LiftedModel.run service.word s).physical.tokens=s.physical.tokens*service.target := by
  have hv := PhysicalModel.visible_run service.word s.physical
  rw [← LiftedModel.run_physical] at hv
  change (LiftedModel.run service.word s).physical.tokens*
    rotation (LiftedModel.run service.word s).physical.cursor=
    s.physical.tokens*rotation s.physical.cursor*eval service.word at hv
  rw [(closed_service_cursor service s).2, hport, service.correct] at hv
  apply mul_right_cancel (b := rotation service.port)
  calc
    _ = _ := hv
    _ = _ := by group

#print axioms closed_service_tokens
end LRX.RotationWords
