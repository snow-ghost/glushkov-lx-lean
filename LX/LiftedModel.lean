import LX.AffineCrossings
import LX.PhysicalModel
import Mathlib

/-! Literal LX.Core execution with an integer cursor and integer positions of every
named token. The position log records winding, including exchanges at the seam.
Its residues are proved to agree with the finite physical permutation. -/
namespace LX.Core.LiftedModel
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

structure Configuration (n : ℕ) where
  physical : PhysicalModel.Configuration n
  position : Fin n → ℤ
  cursor : ℤ

variable {n : ℕ} [NeZero n]

def Aligned (s : Configuration n) : Prop :=
  (s.cursor : Fin n) = s.physical.cursor ∧
  ∀ i, (s.position i : Fin n) = s.physical.tokens.symm i

def increment (a : Letter) : ℤ := match a with
  | .l => 1
  | .r => -1
  | .x => 0

def step (a : Letter) (s : Configuration n) : Configuration n where
  physical := PhysicalModel.step a s.physical
  cursor := s.cursor + increment a
  position i := match a with
    | .l | .r => s.position i
    | .x => s.position i + (if i = s.physical.tokens s.physical.cursor then 1 else 0) -
        (if i = s.physical.tokens (s.physical.cursor + 1) then 1 else 0)

theorem neighboring_positions_distinct (hn : 2 ≤ n) (c : Fin n) : c ≠ c + 1 := by
  have h1 : (1 : Fin n) ≠ 0 := by
    intro h
    have := Fin.one_eq_zero_iff.mp h
    omega
  intro h
  have h' : c + 0 = c + 1 := by simpa using h
  exact h1 (add_left_cancel h').symm

theorem step_aligned (hn : 2 ≤ n) (a : Letter) {s : Configuration n}
    (hs : Aligned s) : Aligned (step a s) := by
  constructor
  · cases a <;> simpa [step, increment, PhysicalModel.step, Int.cast_add, sub_eq_add_neg] using hs.1
  · intro i
    cases a with
    | l => exact hs.2 i
    | r => exact hs.2 i
    | x =>
      let q := s.physical.tokens
      let c := s.physical.cursor
      have hne : q c ≠ q (c+1) := fun h => neighboring_positions_distinct hn c (q.injective h)
      change ((s.position i + (if i = q c then 1 else 0) -
        (if i = q (c+1) then 1 else 0) : ℤ) : Fin n) =
          Equiv.swap c (c+1) (q.symm i)
      by_cases hi : i = q c
      · subst i
        simp only [ite_eq_right hne, sub_zero, Int.cast_add]
        rw [hs.2, Equiv.symm_apply_apply, Equiv.swap_apply_left]
        simp
      · by_cases hj : i = q (c+1)
        · subst i
          simp only [ite_eq_right hi, add_zero, Int.cast_sub]
          rw [hs.2, Equiv.symm_apply_apply, Equiv.swap_apply_right]
          norm_num
        · simp only [ite_eq_right hi, ite_eq_right hj, add_zero, sub_zero]
          rw [hs.2]
          have h0 : q.symm i ≠ c := by intro h; exact hi (by simpa using congrArg q h)
          have h1 : q.symm i ≠ c+1 := by intro h; exact hj (by simpa using congrArg q h)
          exact (Equiv.swap_apply_of_ne_of_ne h0 h1).symm

theorem position_sum_step (a : Letter) (s : Configuration n) :
    ∑ i, (step a s).position i = ∑ i, s.position i := by
  cases a <;> simp [step, Finset.sum_add_distrib, Finset.sum_sub_distrib]

def run : List Letter → Configuration n → Configuration n
  | [], s => s
  | a :: w, s => run w (step a s)

theorem run_append (u v : List Letter) (s : Configuration n) :
    run (u ++ v) s = run v (run u s) := by
  induction u generalizing s with
  | nil => rfl
  | cons a u ih => exact ih (step a s)

theorem run_physical (w : List Letter) (s : Configuration n) :
    (run w s).physical = PhysicalModel.run w s.physical := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact ih (step a s)

theorem run_aligned (hn : 2 ≤ n) (w : List Letter) {s : Configuration n}
    (hs : Aligned s) : Aligned (run w s) := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih => exact ih (step_aligned hn a hs)

theorem position_sum_run (w : List Letter) (s : Configuration n) :
    ∑ i, (run w s).position i = ∑ i, s.position i := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => exact (ih (step a s)).trans (position_sum_step a s)

theorem cursor_run (w : List Letter) (s : Configuration n) :
    (run w s).cursor = s.cursor + (w.map increment).sum := by
  induction w generalizing s with
  | nil => simp [run]
  | cons a w ih => simp [run, ih, step, add_assoc]

def initial : Configuration n := ⟨PhysicalModel.initial, fun i => (i : ℤ), 0⟩

theorem initial_aligned : Aligned (initial (n := n)) := by
  constructor
  · rfl
  · intro i
    simp [initial, PhysicalModel.initial]
    rfl

/-- Every literal word has a balanced exact displacement vector, even if tokens wind. -/
theorem displacement_balanced (w : List Letter) :
    ∑ i, ((run w (initial (n := n))).position i - (i : ℤ)) = 0 := by
  rw [Finset.sum_sub_distrib, position_sum_run]
  simp [initial]


theorem cast_eq_iff_modEq (a b : ℤ) :
    (a : Fin n) = (b : Fin n) ↔ Int.ModEq (n : ℤ) a b := by
  constructor
  · intro h
    have hh := congrArg Fin.val h
    simp only [Fin.val_intCast] at hh
    have hi := congrArg (fun k : ℕ => (k : ℤ)) hh
    have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hn0),
      Int.toNat_of_nonneg (Int.emod_nonneg b hn0)] at hi
    exact hi
  · exact AffineLift.cast_eq_of_modEq


#print axioms step_aligned
#print axioms displacement_balanced
end LX.Core.LiftedModel
