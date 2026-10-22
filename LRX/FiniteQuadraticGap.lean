import LRX.DiscreteQuadraticGap
import LRX.FiniteCycleProfile

/-! Quadratic service bounds for the actual cuts and cycle discounts of a
finite permutation. The nonnegative maximum bounds every boundary charge. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

noncomputable def cycleCharge (p : State b) (x y : ℕ) : ℤ :=
  min ((x : ℤ)+y-cycleLeftLoad p y) (2*(b : ℤ)-x-y-cycleRightLoad p x)

theorem discrete_area_footrule (p : State b) :
    2*(DiscreteLoad.area (discreteProfile p) : ℤ)=∑ i : Fin b, |(p i : ℤ)-(i : ℤ)| := by
  rw [footrule]
  simp only [DiscreteLoad.area,discreteProfile,Nat.cast_sum]

theorem finite_energy_square_cap (p : State b) :
    2*(∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|) ≤ (b : ℤ)^2 := by
  have h := DiscreteLoad.prefix_area_bound (discreteProfile p) 0 0 (by omega) (by omega)
    (fun j hj => by
      have he : j=0 := by omega
      subst j
      exact Nat.le_of_eq (half_load_zero p))
  simp only [Nat.cast_zero,sub_zero,mul_zero] at h
  have he := discrete_area_footrule p
  nlinarith [sq_nonneg ((b : ℤ)-2*DiscreteLoad.peak (discreteProfile p))]

theorem cycle_charge_quadratic (p : State b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b)
    (K : ℤ) (hK : 0 ≤ K) (hcharge : K ≤ cycleCharge p x y) :
    2*(∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)+K^2 ≤ (b : ℤ)^2 := by
  have h := DiscreteLoad.quadratic_gap (discreteProfile p) x y hxy hy
    (cycleLeftLoad p y) (cycleRightLoad p x) K hK
    (fun j hj => cycle_left_available p j y hj)
    (fun j hj hj' => cycle_right_available p x j hj hj')
    (le_trans hcharge (min_le_left _ _)) (le_trans hcharge (min_le_right _ _))
  have he := discrete_area_footrule p
  nlinarith

theorem nonnegative_charge_quadratic (p : State b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) :
    2*(∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)+((cycleCharge p x y).toNat : ℤ)^2 ≤ (b : ℤ)^2 := by
  by_cases hc : 0 ≤ cycleCharge p x y
  · rw [Int.toNat_of_nonneg hc]
    exact cycle_charge_quadratic p x y hxy hy _ hc le_rfl
  · have hz : (cycleCharge p x y).toNat=0 := Int.toNat_eq_zero.mpr (by omega)
    simpa only [hz,Nat.cast_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using finite_energy_square_cap p

noncomputable def gapCost (p : State b) : ℕ :=
  (Finset.univ.filter (fun xy : Fin (b+1) × Fin (b+1) => xy.1.val ≤ xy.2.val)).sup
    (fun xy => (cycleCharge p xy.1.val xy.2.val).toNat)

theorem charge_le_gapCost (p : State b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) :
    cycleCharge p x y ≤ (gapCost p : ℤ) := by
  classical
  have hm : ((⟨x,by omega⟩,⟨y,by omega⟩) : Fin (b+1) × Fin (b+1)) ∈
      Finset.univ.filter (fun xy : Fin (b+1) × Fin (b+1) => xy.1.val ≤ xy.2.val) := by simp [hxy]
  have hs := Finset.le_sup (f := fun xy : Fin (b+1) × Fin (b+1) =>
    (cycleCharge p xy.1.val xy.2.val).toNat) hm
  change (cycleCharge p x y).toNat ≤ gapCost p at hs
  exact le_trans (Int.self_le_toNat (cycleCharge p x y)) (by exact_mod_cast hs)

theorem gapCost_quadratic (p : State b) :
    2*(∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)+(gapCost p : ℤ)^2 ≤ (b : ℤ)^2 := by
  classical
  let pairs := Finset.univ.filter (fun xy : Fin (b+1) × Fin (b+1) => xy.1.val ≤ xy.2.val)
  have hn : pairs.Nonempty := ⟨(0,0),by simp [pairs]⟩
  obtain ⟨xy,hxy,he⟩ := Finset.exists_mem_eq_sup pairs hn
    (fun xy => (cycleCharge p xy.1.val xy.2.val).toNat)
  have horder : xy.1.val ≤ xy.2.val := (Finset.mem_filter.mp hxy).2
  have hbound : xy.2.val ≤ b := by have := xy.2.isLt; omega
  have hcost : gapCost p=(cycleCharge p xy.1.val xy.2.val).toNat := he
  rw [hcost]
  exact nonnegative_charge_quadratic p xy.1.val xy.2.val horder hbound

theorem gapCost_le_size (p : State b) : gapCost p ≤ b := by
  have h := gapCost_quadratic p
  have hmass : 0 ≤ ∑ i : Fin b, |(p i : ℤ)-(i : ℤ)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hK : (0 : ℤ) ≤ gapCost p := by positivity
  have hb : (0 : ℤ) ≤ b := by positivity
  have hbound : (gapCost p : ℤ) ≤ b := by nlinarith
  exact_mod_cast hbound

#print axioms cycle_charge_quadratic
#print axioms gapCost_quadratic
end LRX.FiniteCuts
