import LRX.FiniteDescentRank

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- The unique lift of p(i) in [i,i+n). -/
def clockwiseRepresentative (p : State n) (i : Fin n) : ℤ :=
  (p i : ℤ) + if (p i).val < i.val then (n : ℤ) else 0

theorem clockwise_representative_bounds (p : State n) (i : Fin n) :
    (i : ℤ) ≤ clockwiseRepresentative p i ∧ clockwiseRepresentative p i < (i : ℤ)+n := by
  have hi := i.isLt
  have hp := (p i).isLt
  unfold clockwiseRepresentative
  split_ifs <;> omega

theorem clockwise_representative_modEq (p : State n) (i : Fin n) :
    Int.ModEq (n : ℤ) (clockwiseRepresentative p i) (p i : ℤ) := by
  unfold clockwiseRepresentative
  split_ifs <;> simp [Int.ModEq]

theorem clockwise_representative_unique (p : State n) (g : Fin n → ℤ)
    (hb : ∀ i : Fin n, (i : ℤ) ≤ g i ∧ g i < (i : ℤ)+n)
    (hm : ∀ i : Fin n, Int.ModEq (n : ℤ) (g i) (p i : ℤ)) :
    g = clockwiseRepresentative p := by
  funext i
  have h := ((hm i).trans (clockwise_representative_modEq p i).symm).sub_right (i : ℤ)
  have hg := hb i
  have hc := clockwise_representative_bounds p i
  unfold Int.ModEq at h
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

theorem clockwise_representative_mass (p : State n) :
    (∑ i : Fin n, (clockwiseRepresentative p i-(i : ℤ))) =
      (n : ℤ)*((descendingPositions p).card : ℤ) := by
  have hp : (∑ i : Fin n, displacement p i)=0 := (canonical_lift p).1
  have hpoint (i : Fin n) : clockwiseRepresentative p i-(i : ℤ) =
      displacement p i+(if (p i).val < i.val then (n : ℤ) else 0) := by
    unfold clockwiseRepresentative displacement
    ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hp, zero_add]
  rw [← Finset.sum_filter]
  simp [descendingPositions, mul_comm]

/-- Balance of a strip-shifted lift determines the number of positions moving left. -/
theorem shifted_balanced_descending_count [NeZero n] (p : State n)
    (d : Fin n → ℤ) (h : ℤ) (hbalance : ∑ i, d i=0)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hmod : ∀ i : Fin n, Int.ModEq (n : ℤ) ((i : ℤ)+d i+h) (p i : ℤ)) :
    ((descendingPositions p).card : ℤ)=h := by
  let g : Fin n → ℤ := fun i => (i : ℤ)+d i+h
  have heq : g=clockwiseRepresentative p := clockwise_representative_unique p g
    (fun i => by dsimp [g]; have := hband i; omega) hmod
  have hm := clockwise_representative_mass p
  rw [← heq] at hm
  have hsum : (∑ i : Fin n, (g i-(i : ℤ)))=(n : ℤ)*h := by
    simp only [g, show ∀ i : Fin n, (i : ℤ)+d i+h-(i : ℤ)=d i+h by intro i; ring,
      Finset.sum_add_distrib, hbalance, zero_add, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hsum] at hm
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact (mul_left_cancel₀ hn hm).symm

#print axioms shifted_balanced_descending_count
end LRX.FiniteCuts
