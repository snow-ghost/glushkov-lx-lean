import Mathlib

/-!
# Finite cut-deficit service

An abstract cut-profile formalization of
`literature/root_phase34_finite_reversal_route.md`, Sections 1--2.
The permutation-to-load correspondence is not assumed to be formalized.
All profile and available-load hypotheses are explicit below. This file
does not assert the LRX diameter theorem.
-/

namespace FiniteGapService

open Finset

/-- Maximum number of crossings in one direction at a finite cut. -/
def capacity (b e : ℕ) : ℕ := min e (b - e)

/-- Sum over all cuts, including the two zero-capacity boundary cuts. -/
def capacitySum (b : ℕ) : ℕ := ∑ e ∈ range (b + 1), capacity b e

lemma capacity_shift (b e : ℕ) (he : e ≤ b) :
    capacity (b + 2) (e + 1) = capacity b e + 1 := by
  unfold capacity
  omega

lemma capacitySum_step (b : ℕ) :
    capacitySum (b + 2) = capacitySum b + (b + 1) := by
  unfold capacitySum
  rw [sum_range_succ]
  simp only [capacity, Nat.sub_self, _root_.min_zero, add_zero]
  rw [sum_range_succ']
  simp only [Nat.sub_zero, _root_.zero_min, add_zero]
  have hsum :
      (∑ e ∈ range (b + 1), min (e + 1) (b + 2 - (e + 1))) =
        ∑ e ∈ range (b + 1), (min e (b - e) + 1) := by
    apply sum_congr rfl
    intro e he
    exact capacity_shift b e (by simpa using (Nat.le_of_lt_succ (mem_range.mp he)))
  rw [hsum, sum_add_distrib]
  simp

/-- Exact maximal footrule, including both parities and b = 0, 1. -/
theorem twice_capacitySum (b : ℕ) :
    2 * capacitySum b = b * b / 2 := by
  induction b using Nat.twoStepInduction with
  | zero => simp [capacitySum, capacity]
  | one => simp [capacitySum, capacity, sum_range_succ]
  | more b hb _ =>
    rw [capacitySum_step]
    have hsquare : (b + 2) * (b + 2) = b * b + 4 * b + 4 := by ring
    rw [hsquare]
    omega

/-- Abstract finite half-loads and the two available total loads.

The endpoint cuts 0 and b are included. The pointwise upper bound and
nonnegativity force their half-loads to vanish. The `left_available`
and `right_available` hypotheses are precisely the incident-port
coverage facts used in the mathematical proof. They do not require
the maxima of different cycles to occur at the same cut.
-/
structure CutProfile (b : ℕ) where
  halfLoad : ℕ → ℤ
  nonneg : ∀ e, e ≤ b → 0 ≤ halfLoad e
  upper : ∀ e, e ≤ b → halfLoad e ≤ (capacity b e : ℤ)
  leftLoad : ℕ → ℤ
  rightLoad : ℕ → ℤ
  left_available : ∀ e y, e ≤ y → y ≤ b → 2 * halfLoad e ≤ leftLoad y
  right_available : ∀ x e, x ≤ e → e ≤ b → 2 * halfLoad e ≤ rightLoad x

/-- Total finite footrule represented by the cut profile. -/
def CutProfile.footrule {b : ℕ} (P : CutProfile b) : ℤ :=
  2 * ∑ e ∈ range (b + 1), P.halfLoad e

/-- The smaller of the left- and right-boundary scalar charges.
This is not a claim about a standalone LRX word without an outer root.
-/
def CutProfile.charge {b : ℕ} (P : CutProfile b) (x y : ℕ) : ℤ :=
  min ((x : ℤ) + y - P.leftLoad y)
    (2 * (b : ℤ) - x - y - P.rightLoad x)

lemma capacitySum_cast (b : ℕ) :
    2 * (∑ e ∈ range (b + 1), (capacity b e : ℤ)) = (b * b / 2 : ℕ) := by
  have h := twice_capacitySum b
  unfold capacitySum at h
  exact_mod_cast h

/-- A single cut's deficit is bounded by the total footrule deficit. -/
theorem local_deficit_bound {b : ℕ} (P : CutProfile b) (e : ℕ) (he : e ≤ b) :
    P.footrule + 2 * ((capacity b e : ℤ) - P.halfLoad e) ≤
      (b * b / 2 : ℕ) := by
  have hd : (capacity b e : ℤ) - P.halfLoad e ≤
      ∑ j ∈ range (b + 1), ((capacity b j : ℤ) - P.halfLoad j) := by
    apply single_le_sum (s := range (b + 1))
      (f := fun j : ℕ => (capacity b j : ℤ) - P.halfLoad j) (a := e)
    · intro j hj
      have hj' := mem_range.mp hj
      exact sub_nonneg.mpr (P.upper j (by omega))
    · exact mem_range.mpr (by omega)
  have hQ := capacitySum_cast b
  rw [sum_sub_distrib] at hd
  unfold CutProfile.footrule
  linarith

/-- The left boundary pays every ordered pair whose sum is at most b. -/
theorem left_service_bound {b : ℕ} (P : CutProfile b) (x y : ℕ)
    (hxy : x ≤ y) (hy : y ≤ b) (hsum : x + y ≤ b) :
    P.footrule + ((x : ℤ) + y - P.leftLoad y) ≤
      (b * b / 2 : ℕ) + (b % 2 : ℕ) := by
  let e := min y (b / 2)
  have hey : e ≤ y := by dsimp [e]; omega
  have heb : e ≤ b := hey.trans hy
  have hgeom : (x : ℤ) + y ≤ (b % 2 : ℕ) + 2 * (capacity b e : ℤ) := by
    dsimp [e, capacity]
    omega
  have hload := P.left_available e y hey hy
  have hdef := local_deficit_bound P e heb
  linarith

/-- The reflected argument, at cut b-min(b-x,b/2), pays the right half.
No symmetry or reflection property of the supplied functions is assumed:
the right available-load hypothesis is used directly.
-/
theorem right_service_bound {b : ℕ} (P : CutProfile b) (x y : ℕ)
    (hxy : x ≤ y) (hy : y ≤ b) (hsum : b ≤ x + y) :
    P.footrule + (2 * (b : ℤ) - x - y - P.rightLoad x) ≤
      (b * b / 2 : ℕ) + (b % 2 : ℕ) := by
  let e := b - min (b - x) (b / 2)
  have hxe : x ≤ e := by dsimp [e]; omega
  have heb : e ≤ b := by dsimp [e]; omega
  have hgeom : 2 * (b : ℤ) - x - y ≤
      (b % 2 : ℕ) + 2 * (capacity b e : ℤ) := by
    dsimp [e, capacity]
    omega
  have hload := P.right_available x e hxe heb
  have hdef := local_deficit_bound P e heb
  linarith

/-- General finite cut-deficit service theorem, for every b and every
ordered cursor pair 0 <= x <= y <= b, with both parities included. -/
theorem finite_gap_service {b : ℕ} (P : CutProfile b) (x y : ℕ)
    (hxy : x ≤ y) (hy : y ≤ b) :
    P.footrule + P.charge x y ≤
      (b * b / 2 : ℕ) + (b % 2 : ℕ) := by
  by_cases hsum : x + y ≤ b
  · have h := left_service_bound P x y hxy hy hsum
    have hm := min_le_left ((x : ℤ) + y - P.leftLoad y)
      (2 * (b : ℤ) - x - y - P.rightLoad x)
    unfold CutProfile.charge
    linarith
  · have h := right_service_bound P x y hxy hy (by omega)
    have hm := min_le_right ((x : ℤ) + y - P.leftLoad y)
      (2 * (b : ℤ) - x - y - P.rightLoad x)
    unfold CutProfile.charge
    linarith

/-- The same universal bound for arbitrary cursor order, after sorting
the two coordinates as in the scalar line-service functional. -/
theorem finite_gap_service_unordered {b : ℕ} (P : CutProfile b) (x y : ℕ)
    (hx : x ≤ b) (hy : y ≤ b) :
    P.footrule + P.charge (min x y) (max x y) ≤
      (b * b / 2 : ℕ) + (b % 2 : ℕ) := by
  apply finite_gap_service
  · omega
  · omega

/-- Adding an explicit inversion-count upper bound yields the joint
functional estimate. No permutation or inversion count is postulated. -/
theorem finite_gap_service_with_inversions {b : ℕ} (P : CutProfile b)
    (I : ℤ) (hI : I ≤ (b * (b - 1) / 2 : ℕ)) (x y : ℕ)
    (hxy : x ≤ y) (hy : y ≤ b) :
    I + P.footrule + P.charge x y ≤
      (b * (b - 1) / 2 : ℕ) + (b * b / 2 : ℕ) + (b % 2 : ℕ) := by
  have h := finite_gap_service P x y hxy hy
  linarith

end FiniteGapService

#print axioms FiniteGapService.twice_capacitySum
#print axioms FiniteGapService.finite_gap_service
#print axioms FiniteGapService.finite_gap_service_unordered
#print axioms FiniteGapService.finite_gap_service_with_inversions
