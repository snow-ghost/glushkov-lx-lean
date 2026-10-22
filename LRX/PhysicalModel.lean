import LRX.ZeroLift

/-! Physical positions, a paid cursor, and literal L/R/X words.
Every physical operation is proved to induce the same visible generator.
A realized balanced lift ends at the original target in its exact orientation. -/
namespace LRX.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open AffineLift

structure Configuration (n : ℕ) where
  tokens : State n
  cursor : Fin n

variable {n : ℕ} [NeZero n]

def visible (s : Configuration n) : State n := s.tokens * L n ^ s.cursor.val

theorem visible_apply (s : Configuration n) (i : Fin n) :
    visible s i = s.tokens (i + s.cursor) := by
  simp only [visible, Equiv.Perm.mul_apply, rotation_power_apply, Fin.cast_val_eq_self]

def step (a : Letter) (s : Configuration n) : Configuration n :=
  match a with
  | .l => ⟨s.tokens, s.cursor + 1⟩
  | .r => ⟨s.tokens, s.cursor - 1⟩
  | .x => ⟨s.tokens * Equiv.swap s.cursor (s.cursor + 1), s.cursor⟩

theorem visible_step (a : Letter) (s : Configuration n) :
    visible (step a s) = visible s * a.eval (n := n) := by
  apply Equiv.ext
  intro i
  cases a with
  | l =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, L, finRotate_apply]
    congr 1
    abel
  | r =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, R, L]
    change s.tokens (i + (s.cursor - 1)) = s.tokens ((finRotate n).symm i + s.cursor)
    rw [finRotate_symm_apply]
    congr 1
    abel
  | x =>
    simp only [step, visible_apply, Letter.eval, Equiv.Perm.mul_apply, X]
    congr 1
    have h := Function.Injective.map_swap (f := fun j : Fin n => j + s.cursor)
      (add_left_injective s.cursor) (0 : Fin n) 1 i
    simpa only [zero_add, add_zero, add_comm] using h.symm

def run : List Letter → Configuration n → Configuration n
  | [], s => s
  | a :: w, s => run w (step a s)

theorem visible_run (w : List Letter) (s : Configuration n) :
    visible (run w s) = visible s * eval w := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => rw [run, ih, visible_step, eval_cons, mul_assoc]

def initial : Configuration n := ⟨1, 0⟩

@[simp] theorem visible_initial : visible (initial (n := n)) = 1 := by
  simp [visible, initial]

/-- Positions are physical: `tokens.symm i` is the position of token `i`. -/
def Realizes (s : Configuration n) (d : Fin n → ℤ) : Prop :=
  ∀ i : Fin n, s.tokens.symm i = i + (d i : Fin n)

theorem visible_of_realizes {p : State n} {s : Configuration n} {d : Fin n → ℤ}
    (hd : IsLift p (s.cursor : ℤ) d) (hs : Realizes s d) : visible s = p := by
  apply Equiv.ext
  intro i
  rw [visible_apply]
  have he := lift_residue hd (p i)
  have hcast : ((s.cursor : ℤ) : Fin n) = s.cursor := by simp
  rw [hcast, Equiv.symm_apply_apply] at he
  have hpos : s.tokens.symm (p i) = i + s.cursor := (hs (p i)).trans he
  have h := congrArg s.tokens hpos
  simpa only [Equiv.apply_symm_apply] using h.symm

/-- No extra free rotation is needed or allowed: the final cursor is part of
`IsLift`, and the executed physical word evaluates to the exact target. -/
theorem eval_of_realizes (w : List Letter) {p : State n} {d : Fin n → ℤ}
    (hd : IsLift p ((run w (initial (n := n))).cursor : ℤ) d)
    (hs : Realizes (run w (initial (n := n))) d) : eval w = p := by
  have h := visible_of_realizes hd hs
  simpa only [visible_run, visible_initial, one_mul] using h

#print axioms visible_step
#print axioms eval_of_realizes
end LRX.PhysicalModel
