import LRX.FiniteCycleLoads

/-! Aggregate discounts are sums of peaks of the actual disjoint cycles.
Each positive summand is attained by a closed service (FiniteCycleAvailability).
The scalar estimate here does not yet assemble those services into a route. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

noncomputable def cycleLeftLoad (p : State b) (y : ℕ) : ℤ :=
  ∑ q ∈ p.cycleFactorsFinset, 2*(leftPeak q y : ℤ)

noncomputable def cycleRightLoad (p : State b) (x : ℕ) : ℤ :=
  ∑ q ∈ p.cycleFactorsFinset, 2*(rightPeak q x : ℤ)

theorem cycle_left_available (p : State b) (e y : ℕ) (hey : e ≤ y) :
    2*(halfLoad p e : ℤ) ≤ cycleLeftLoad p y := by
  classical
  rw [half_load_cycle_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have h : halfLoad q e ≤ leftPeak q y :=
    Finset.le_sup (Finset.mem_range.mpr (by omega))
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by norm_num)

theorem cycle_right_available (p : State b) (x e : ℕ) (hxe : x ≤ e) (heb : e ≤ b) :
    2*(halfLoad p e : ℤ) ≤ cycleRightLoad p x := by
  classical
  rw [half_load_cycle_sum, Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  have h : halfLoad q e ≤ rightPeak q x :=
    Finset.le_sup (Finset.mem_Icc.mpr ⟨hxe,heb⟩)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast h) (by norm_num)

noncomputable def cycleProfile (p : State b) : FiniteGapService.CutProfile b where
  halfLoad e := (halfLoad p e : ℤ)
  nonneg e _ := by positivity
  upper e he := by exact_mod_cast half_load_capacity p e he
  leftLoad := cycleLeftLoad p
  rightLoad := cycleRightLoad p
  left_available e y hey _ := cycle_left_available p e y hey
  right_available x e hxe heb := cycle_right_available p x e hxe heb

theorem cycle_profile_footrule (p : State b) :
    (cycleProfile p).footrule=∑ i : Fin b, |(p i : ℤ)-(i : ℤ)| := (footrule p).symm

theorem finite_cycle_charge_bound (p : State b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) :
    (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)+
      min ((x : ℤ)+y-cycleLeftLoad p y)
        (2*(b : ℤ)-x-y-cycleRightLoad p x) ≤
      (b*b/2 : ℕ)+(b%2 : ℕ) := by
  have h := FiniteGapService.finite_gap_service (cycleProfile p) x y hxy hy
  rw [cycle_profile_footrule] at h
  exact h

#print axioms cycle_left_available
#print axioms cycle_right_available
#print axioms finite_cycle_charge_bound
end LRX.FiniteCuts
