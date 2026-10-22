import LRX.StrictBandInversionCapacity

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Equality in the strip capacity forces both intermediate rank inequalities to be equalities. -/
theorem shifted_capacity_equality {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)-(q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h := by
  dsimp only
  let q := shiftedLiftPermutation p c h
  have hf := shifted_lift_inversion_formula hd h hband
  have hc := shifted_balanced_descending_count q d h hd.1 hband
    (shifted_lift_permutation_modEq hd h)
  have hr := finite_depth_rank q
  have hm := displacement_mass_eq_twice_leftDepth q
  have hs : ((descendingPositions q).card : ℤ)+(q.cycleFactorsFinset.card : ℤ) ≤
      (q.support.card : ℤ) := by exact_mod_cast descending_count_add_cycles_le_support q
  change (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
    h*((n : ℤ)-h)+(inversionNumber q : ℤ)-2*leftDepth q at hf
  rw [heq] at hf
  have hdef : 2*leftDepth q-(inversionNumber q : ℤ)=h := by nlinarith
  change (q.support.card : ℤ)-(q.cycleFactorsFinset.card : ℤ)=h ∧
    (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h
  rw [hc] at hs
  constructor <;> omega

/-- A fixed endpoint residue is exactly a negative extreme coordinate. -/
theorem shifted_fixed_iff_negative_extreme {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (i : Fin n) :
    shiftedLiftPermutation p c h i=i ↔ d i= -h := by
  let q := shiftedLiftPermutation p c h
  have heq : (fun j : Fin n => (j : ℤ)+d j+h)=clockwiseRepresentative q :=
    clockwise_representative_unique q _
      (fun j => by have := hband j; omega) (shifted_lift_permutation_modEq hd h)
  constructor
  · intro hfix
    have hi := congrFun heq i
    change q i=i at hfix
    simp only [clockwiseRepresentative, hfix, lt_self_iff_false, ite_false, add_zero] at hi
    omega
  · intro hi
    have hm := shifted_lift_permutation_modEq hd h i
    have hz : (i : ℤ)+d i+h=(i : ℤ) := by omega
    rw [hz] at hm
    have hc := (LiftedModel.cast_eq_iff_modEq _ _).mpr hm
    simpa only [Int.cast_natCast, Fin.cast_val_eq_self] using hc.symm

theorem shifted_support_add_extreme_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) :
    (shiftedLiftPermutation p c h).support.card+
      (Finset.univ.filter (fun i => d i= -h)).card=n := by
  classical
  have heq : Finset.univ.filter (fun i => d i= -h)=
      Finset.univ \ (shiftedLiftPermutation p c h).support := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
      Equiv.Perm.mem_support, not_not]
    exact (shifted_fixed_iff_negative_extreme hd h hband i).symm
  rw [heq, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, Fintype.card_fin]
  have hs := (shiftedLiftPermutation p c h).support.card_le_univ
  simp only [Fintype.card_fin] at hs
  omega

/-- The extreme-coordinate bound forces exactly h pairs' worth of moved vertices. -/
theorem shifted_capacity_equality_support {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) (h : ℤ)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1))
    (hext : ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) ≤ (n : ℤ)-2*h) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h := by
  dsimp only
  let q := shiftedLiftPermutation p c h
  have hr := shifted_capacity_equality hd h hband heq
  change (q.support.card : ℤ)-(q.cycleFactorsFinset.card : ℤ)=h ∧
    (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h at hr
  have hf : (q.support.card : ℤ)+((Finset.univ.filter (fun i => d i= -h)).card : ℤ)=n := by
    exact_mod_cast shifted_support_add_extreme_count hd h hband
  have hc : 2*(q.cycleFactorsFinset.card : ℤ) ≤ (q.support.card : ℤ) := by
    exact_mod_cast twice_cycle_count_le_support q
  change (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
    (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h
  omega

#print axioms shifted_capacity_equality
#print axioms shifted_fixed_iff_negative_extreme
#print axioms shifted_capacity_equality_support
end LRX.FiniteCuts
