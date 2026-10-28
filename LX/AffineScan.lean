import LX.LiftedModel
import LX.WordMetric
import Mathlib

/-! Local invariants for the forward scan used to construct LX words.
This module proves progress and energy descent, not the quadratic price. -/
namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def labels (d : Fin n → ℤ) (i : Fin n) : Fin n := i + (d i : Fin n)

def rotate (d : Fin n → ℤ) (i : Fin n) : ℤ := d (finRotate n i)

def exchange (d : Fin n → ℤ) (i : Fin n) : ℤ :=
  d (Equiv.swap 0 1 i) + (if i = 0 then 1 else 0) - (if i = 1 then 1 else 0)

theorem rotate_labels (d : Fin n → ℤ) (i : Fin n) :
    labels (rotate d) i = labels d (finRotate n i) - 1 := by
  simp only [labels, rotate, finRotate_apply]
  abel

theorem rotate_injective (d : Fin n → ℤ) (hi : Function.Injective (labels d)) :
    Function.Injective (labels (rotate d)) := by
  intro i j hij
  simp only [rotate_labels, sub_left_inj] at hij
  exact (finRotate n).injective (hi hij)

theorem exchange_labels (hn : 2 ≤ n) (d : Fin n → ℤ) (i : Fin n) :
    labels (exchange d) i = labels d (Equiv.swap 0 1 i) := by
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have hh := Fin.one_eq_zero_iff.mp h.symm
    omega
  by_cases hi : i = 0
  · subst i
    simp [labels, exchange, h01, add_comm]
  · by_cases hj : i = 1
    · subst i
      simp [labels, exchange, Ne.symm h01]
    · simp [labels, exchange, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]

theorem exchange_injective (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (exchange d)) := by
  intro i j hij
  simp only [exchange_labels hn] at hij
  exact (Equiv.swap (0 : Fin n) 1).injective (hi hij)

omit [NeZero n] in
theorem rotate_sum (d : Fin n → ℤ) : ∑ i, rotate d i = ∑ i, d i :=
  Equiv.sum_comp (finRotate n) d


theorem exchange_sum (d : Fin n → ℤ) : ∑ i, exchange d i = ∑ i, d i := by
  simp [exchange, Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp]

theorem exchange_energy (hn : 2 ≤ n) (d : Fin n → ℤ) :
    (LX.Core.AffineLift.energy (exchange d) : ℤ) - LX.Core.AffineLift.energy d =
      2 * (d 1 - d 0 + 1) := by
  have h01 : (0 : Fin n) ≠ 1 := by
    intro h
    have h' := Fin.one_eq_zero_iff.mp h.symm
    omega
  have point (i : Fin n) : (exchange d i)^2 = (d (Equiv.swap 0 1 i))^2 +
      (if i = 0 then 2*d 1+1 else 0) + (if i = 1 then -2*d 0+1 else 0) := by
    by_cases hi : i = 0
    · subst i
      simp only [exchange, Equiv.swap_apply_left, h01, ite_true, ite_false, sub_zero, add_zero]
      ring
    · by_cases hj : i = 1
      · subst i
        simp only [exchange, Equiv.swap_apply_right, Ne.symm h01, ite_true, ite_false,
          add_zero]
        ring
      · simp [exchange, Equiv.swap_apply_of_ne_of_ne hi hj, hi, hj]
  rw [LX.Core.AffineLift.energy_cast, LX.Core.AffineLift.energy_cast]
  simp_rw [point]
  simp only [Finset.sum_add_distrib]
  rw [Equiv.sum_comp (Equiv.swap (0 : Fin n) 1) (fun i => d i ^ 2)]
  simp
  ring

theorem exchange_energy_lt (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hdesc : d 1 + 1 < d 0) :
    LX.Core.AffineLift.energy (exchange d) < LX.Core.AffineLift.energy d := by
  have h := exchange_energy hn d
  have hh : (LX.Core.AffineLift.energy (exchange d) : ℤ) < LX.Core.AffineLift.energy d := by
    omega
  exact_mod_cast hh

theorem constant_of_neighbor_le (d : Fin n → ℤ)
    (h : ∀ i, d i ≤ d (finRotate n i)) : ∀ i, d i = d 0 := by
  cases n with
  | zero => exact False.elim (NeZero.ne 0 rfl)
  | succ k =>
    have hm : Monotone d := Fin.monotone_iff_le_succ.mpr (by
      intro i
      have he : finRotate (k + 1) i.castSucc = i.succ := by
        apply Fin.ext
        rw [coe_finRotate_of_ne_last (ne_of_lt (Fin.castSucc_lt_last i))]
        rfl
      simpa only [he] using h i.castSucc)
    have hl : d (Fin.last k) ≤ d 0 := by simpa only [finRotate_last] using h (Fin.last k)
    intro i
    exact le_antisymm ((hm (Fin.le_last i)).trans hl) (hm (Fin.zero_le i))

theorem zero_of_neighbor_le (d : Fin n → ℤ) (hb : ∑ i, d i = 0)
    (h : ∀ i, d i ≤ d (finRotate n i)) : ∀ i, d i = 0 := by
  have hc := constant_of_neighbor_le d h
  have hs : (n : ℤ) * d 0 = 0 := by simpa only [hc, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using hb
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hz := (mul_eq_zero.mp hs).resolve_left hn
  intro i
  exact (hc i).trans hz

/-- An unsorted balanced affine permutation has a legal exchange during a forward lap. -/
theorem exists_descent (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i, d i = 0) (hi : Function.Injective (labels d))
    (hz : ¬ ∀ i, d i = 0) : ∃ i, d (finRotate n i) + 1 < d i := by
  by_contra hno
  push Not at hno
  apply hz
  apply zero_of_neighbor_le d hb
  intro i
  have hne : d i ≠ d (finRotate n i) + 1 := by
    intro he
    have hh : labels d i = labels d (finRotate n i) := by
      simp only [labels, he, Int.cast_add, Int.cast_one, finRotate_apply]
      abel
    have hc := hi hh
    exact LX.Core.LiftedModel.neighboring_positions_distinct hn i (by
      simpa only [finRotate_apply] using hc)
  have hh := hno i
  omega

def step : Letter → (Fin n → ℤ) → (Fin n → ℤ)
  | .l => rotate
  | .x => exchange

def run : List Letter → (Fin n → ℤ) → (Fin n → ℤ)
  | [], d => d
  | a :: w, d => run w (step a d)

theorem run_append (u v : List Letter) (d : Fin n → ℤ) :
    run (u ++ v) d = run v (run u d) := by
  induction u generalizing d with
  | nil => rfl
  | cons a u ih => exact ih (step a d)

theorem run_sum (w : List Letter) (d : Fin n → ℤ) : ∑ i, run w d i = ∑ i, d i := by
  induction w generalizing d with
  | nil => rfl
  | cons a w ih =>
    rw [run, ih]
    cases a with
    | l => exact rotate_sum d
    | x => exact exchange_sum d

theorem run_injective (hn : 2 ≤ n) (w : List Letter) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) : Function.Injective (labels (run w d)) := by
  induction w generalizing d with
  | nil => exact hi
  | cons a w ih =>
    apply ih
    cases a with
    | l => exact rotate_injective d hi
    | x => exact exchange_injective hn d hi

theorem step_labels (hn : 2 ≤ n) (a : Letter) (d : Fin n → ℤ) (i : Fin n) :
    labels (step a d) i = labels d (eval (n := n) [a] i) -
      (if a = .l then 1 else 0) := by
  cases a with
  | l => simpa [step, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval, LX.Core.L] using rotate_labels d i
  | x => simpa [step, eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval, LX.Core.X] using exchange_labels hn d i

theorem run_labels (hn : 2 ≤ n) (w : List Letter) (d : Fin n → ℤ) (i : Fin n) :
    labels (run w d) i = labels d (eval w i) - (w.count .l : Fin n) := by
  induction w generalizing d with
  | nil => simp [run, eval, LX.Core.eval]
  | cons a w ih =>
    rw [run, ih, step_labels hn]
    cases a <;> simp [eval, Letter.toCore, LX.Core.eval,
      LX.Core.Letter.eval, Equiv.Perm.mul_apply] <;> abel

/-- A zero affine board gives an actual sorting word, including its final paid rotation. -/
theorem sorting_word_of_zero (hn : 2 ≤ n) (p : State n) (c : Fin n)
    (d : Fin n → ℤ) (hd : ∀ i, labels d i = p i + c)
    (w : List Letter) (hw : ∀ i, run w d i = 0) :
    p * eval (w ++ List.replicate (c - (w.count .l : Fin n)).val .l) = 1 := by
  let k : Fin n := c - (w.count .l : Fin n)
  apply Equiv.ext
  intro i
  have hz := run_labels hn w d (i + k)
  have hleft : labels (run w d) (i + k) = i + k := by simp [labels, hw]
  rw [hleft, hd] at hz
  have hh : i + k = p (eval w (i + k)) + k := by
    simpa only [← add_sub_assoc, k] using hz
  have hc : p (eval w (i + k)) = i := (add_right_cancel hh).symm
  change (p * eval (n := n) (w ++ List.replicate k.val Letter.l)) i = i
  rw [eval_append]
  simpa [eval, Letter.toCore, LX.Core.eval, LX.Core.Letter.eval,
    Equiv.Perm.mul_apply, LX.Core.AffineLift.rotation_power_apply] using hc

theorem run_left_apply (k : ℕ) (d : Fin n → ℤ) (i : Fin n) :
    run (List.replicate k .l) d i = d (((LX.Core.L n)^k) i) := by
  induction k generalizing d with
  | zero => simp [run]
  | succ k ih =>
    simp only [List.replicate_succ, run, step]
    rw [ih]
    simp only [rotate, LX.Core.L, pow_succ', Equiv.Perm.mul_apply]

theorem run_left_energy (k : ℕ) (d : Fin n → ℤ) :
    LX.Core.AffineLift.energy (run (List.replicate k .l) d) = LX.Core.AffineLift.energy d := by
  simp only [LX.Core.AffineLift.energy, run_left_apply]
  exact Equiv.sum_comp ((LX.Core.L n)^k) (fun i => (d i).natAbs ^ 2)


#print axioms exchange_energy_lt
#print axioms exists_descent
#print axioms sorting_word_of_zero
end LX.AffineScan
