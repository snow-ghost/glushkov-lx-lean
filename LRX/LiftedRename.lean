import LRX.LiftedModel
import Mathlib

/-! Periodic renaming of lifted tokens commutes with physical execution. The
integer offset is retained, so this symmetry records winding as well as labels. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def rename (q : State n) (offset : Fin n → ℤ) (s : Configuration n) : Configuration n where
  physical := ⟨q.symm*s.physical.tokens, s.physical.cursor⟩
  position i := s.position (q i)+offset i
  cursor := s.cursor

theorem rename_step (q : State n) (offset : Fin n → ℤ) (a : Letter) (s : Configuration n) :
    rename q offset (step a s)=step a (rename q offset s) := by
  have he (i j : Fin n) : i=q.symm j ↔ q i=j := by
    constructor
    · intro h; rw [h, q.apply_symm_apply]
    · intro h; rw [← h, q.symm_apply_apply]
  cases a <;>
    simp [rename, step, increment, PhysicalModel.step, mul_assoc, Equiv.Perm.mul_apply,
      he, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]

theorem rename_run (q : State n) (offset : Fin n → ℤ) (w : List Letter) (s : Configuration n) :
    rename q offset (run w s)=run w (rename q offset s) := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => rw [run, ih, rename_step, run]

omit [NeZero n] in
theorem rename_involutive (q : State n) (offset : Fin n → ℤ)
    (hq : Function.Involutive q) (hoffset : ∀ i, offset (q i)+offset i=0) :
    Function.Involutive (rename q offset) := by
  have hqi : q.symm=q := by
    apply Equiv.ext
    intro i
    apply q.injective
    rw [q.apply_symm_apply]
    exact (hq i).symm
  have hqq : q*q=1 := by
    apply Equiv.ext
    intro i
    exact hq i
  intro s
  have hp : (fun i => s.position (q (q i))+offset (q i)+offset i)=s.position := by
    funext i
    rw [hq, add_assoc, hoffset, add_zero]
  simp only [rename, hqi, ← mul_assoc, hqq, one_mul, hp]

/-- Two X events implementing the same involutive lifted renaming can both be
removed, while preserving the entire configuration and every integer position. -/
theorem delete_renamed_pair (q : State n) (offset : Fin n → ℤ)
    (hq : Function.Involutive q) (hoffset : ∀ i, offset (q i)+offset i=0)
    (middle : List Letter) (s : Configuration n)
    (hfirst : step .x s=rename q offset s)
    (hsecond : step .x (run middle (step .x s))=rename q offset (run middle (step .x s))) :
    run ([.x]++middle++[.x]) s=run middle s := by
  simp only [run_append, run]
  rw [hsecond, hfirst, ← rename_run]
  exact rename_involutive q offset hq hoffset (run middle s)

#print axioms rename_step
#print axioms delete_renamed_pair
end LRX.LiftedModel
