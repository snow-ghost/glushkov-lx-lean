import LX.Graph
import Mathlib

/-!
A balanced phase lift of an actual permutation, with subset majorization.
We minimize the nonnegative integer sum of squared displacements over all
balanced lifts and phases. Phase shifts yield majorization directly, without
assuming an affine inversion formula or a pre-existing bounded lift.
-/
namespace LX.Core.AffineLift
open scoped BigOperators

/-- `p` maps visible positions to labels, so token `i` ends at `p.symm i`.
The integer phase is the final physical cursor, taken modulo `n`. -/
def IsLift {n : ℕ} (p : State n) (c : ℤ) (d : Fin n → ℤ) : Prop :=
  (∑ i, d i) = 0 ∧ ∀ i : Fin n,
    Int.ModEq (n : ℤ) ((i : ℤ) + d i) ((p.symm i : ℤ) + c)

def energy {n : ℕ} (d : Fin n → ℤ) : ℕ := ∑ i, (d i).natAbs ^ 2

theorem energy_cast {n : ℕ} (d : Fin n → ℤ) :
    (energy d : ℤ) = ∑ i, d i ^ 2 := by
  simp [energy, sq_abs]

theorem canonical_lift {n : ℕ} (p : State n) :
    IsLift p 0 (fun i => (p.symm i : ℤ) - (i : ℤ)) := by
  constructor
  · rw [Finset.sum_sub_distrib]
    have h := Equiv.sum_comp p.symm (fun i : Fin n => (i : ℤ))
    rw [h]
    simp
  · intro i
    simp [Int.ModEq]

/-- Existence uses well-ordering of natural energy, even though the space of
phases and integer lift vectors is infinite. -/
theorem exists_minimal {n : ℕ} (p : State n) :
    ∃ c d, IsLift p c d ∧ ∀ c' d', IsLift p c' d' → energy d ≤ energy d' := by
  classical
  let P : ℕ → Prop := fun k => ∃ c d, IsLift p c d ∧ energy d = k
  have hex : ∃ k, P k := ⟨_, 0, _, canonical_lift p, rfl⟩
  obtain ⟨c, d, hd, he⟩ := Nat.find_spec hex
  refine ⟨c, d, hd, ?_⟩
  intro c' d' hd'
  rw [he]
  exact Nat.find_min' hex ⟨c', d', hd', rfl⟩

/-- Shift the final cursor by `|s|`, and subtract one turn at selected tokens. -/
def phaseShift {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n)) (i : Fin n) : ℤ :=
  d i + s.card - if i ∈ s then (n : ℤ) else 0

theorem shift_balanced {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) : ∑ i, phaseShift d s i = 0 := by
  simp [phaseShift, Finset.sum_sub_distrib, Finset.sum_add_distrib, hd,
    Finset.sum_ite_mem, mul_comm]

theorem shift_lift {n : ℕ} {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (s : Finset (Fin n)) :
    IsLift p (c + s.card) (phaseShift d s) := by
  refine ⟨shift_balanced d s hd.1, ?_⟩
  intro i
  have h := (hd.2 i).add_right (s.card : ℤ)
  simp only [phaseShift]
  by_cases hi : i ∈ s
  · simp only [ite_eq_left hi]
    rw [← add_sub_assoc, Int.sub_modulus_modEq_iff]
    simpa only [add_assoc] using h
  · simp only [ite_eq_right hi, sub_zero]
    simpa only [add_assoc] using h

/-- The exact change in quadratic energy for every subset, not just sorted prefixes. -/
theorem shift_energy {n : ℕ} (d : Fin n → ℤ) (s : Finset (Fin n))
    (hd : ∑ i, d i = 0) :
    (energy (phaseShift d s) : ℤ) - energy d =
      (n : ℤ) * ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
  rw [energy_cast, energy_cast]
  have point (i : Fin n) : phaseShift d s i ^ 2 =
      d i ^ 2 + 2 * (s.card : ℤ) * d i + (s.card : ℤ) ^ 2 +
      if i ∈ s then (n : ℤ)^2 - 2*n*s.card - 2*n*d i else 0 := by
    unfold phaseShift
    split_ifs <;> ring
  simp_rw [point]
  simp [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_ite_mem, hd]
  ring

/-- Subset form of the Lorenz/majorization condition used in the upper proof. -/
def Majorized {n : ℕ} (d : Fin n → ℤ) : Prop :=
  ∀ s : Finset (Fin n), 2 * ∑ i ∈ s, d i ≤ (s.card : ℤ) * (n - s.card)

theorem minimal_majorized {n : ℕ} (hn : 0 < n) {p : State n} {c : ℤ}
    {d : Fin n → ℤ} (hd : IsLift p c d)
    (hmin : ∀ c' d', IsLift p c' d' → energy d ≤ energy d') : Majorized d := by
  intro s
  have h := hmin _ _ (shift_lift hd s)
  have he : (energy d : ℤ) ≤ energy (phaseShift d s) := by exact_mod_cast h
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hprod : 0 ≤ (n : ℤ) *
      ((s.card : ℤ) * (n - s.card) - 2 * ∑ i ∈ s, d i) := by
    rw [← shift_energy d s hd.1]
    omega
  have hnonneg := nonneg_of_mul_nonneg_right hprod hn'
  omega


/-- Singleton and complementary-subset bounds force every arrow to be strictly
shorter than half a circle. The integer statement also keeps the parity slack. -/
theorem short_coordinates {n : ℕ} {d : Fin n → ℤ}
    (hd : ∑ i, d i = 0) (hm : Majorized d) (i : Fin n) :
    2 * d i ≤ (n : ℤ) - 1 ∧ -((n : ℤ) - 1) ≤ 2 * d i := by
  have hpos := hm {i}
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hpos
  have hsum := Finset.sum_erase_add Finset.univ d (Finset.mem_univ i)
  rw [hd] at hsum
  have hneg := hm (Finset.univ.erase i)
  have hn : 1 ≤ n := by have := i.isLt; omega
  simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one] at hneg
  constructor
  · exact hpos
  · have hsum' : ∑ j ∈ Finset.univ.erase i, d j = -d i := by omega
    rw [hsum'] at hneg
    nlinarith

theorem range_bound {n : ℕ} {d : Fin n → ℤ}
    (hd : ∑ i, d i = 0) (hm : Majorized d) (i j : Fin n) :
    d i - d j ≤ (n : ℤ) - 1 := by
  obtain ⟨hi, _⟩ := short_coordinates hd hm i
  obtain ⟨_, hj⟩ := short_coordinates hd hm j
  omega

end LX.Core.AffineLift
