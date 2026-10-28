import LX.FiniteCoordinateCapacity
import LX.AnchoredPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- Distinct cyclic displacements, also called a complete mapping of the cycle. -/
def CompleteMapping (p : State n) : Prop := Function.Injective (fun i => p i-i)

theorem clockwise_difference_value (q : State n) (i : Fin n) :
    clockwiseRepresentative q i-(i : ℤ)=((q i-i : Fin n) : ℤ) := by
  have hb := clockwise_representative_bounds q i
  have hc := LX.Core.AffineLift.cast_eq_of_modEq (clockwise_representative_modEq q i)
  have hm : ((clockwiseRepresentative q i-(i : ℤ) : ℤ) : Fin n)=q i-i := by
    simp only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hc]
  have hh := congrArg (fun x : Fin n => (x : ℤ)) hm
  simp only [Fin.val_intCast] at hh
  rw [Int.emod_eq_of_lt (by omega) (by omega),Int.toNat_of_nonneg (by omega)] at hh
  exact hh

theorem complete_shift_injective (p : State n) (hp : CompleteMapping p) (a : Fin n) :
    Function.Injective (fun i => permutation p a i-i) := by
  intro i j hij
  apply hp
  change p i+(a-p a)-i=p j+(a-p a)-j at hij
  linear_combination hij

theorem complete_displacement_injective (p : State n) (hp : CompleteMapping p) (a : Fin n) :
    Function.Injective (displacement p a) := by
  intro i j hij
  apply complete_shift_injective p hp a
  apply Fin.ext
  have he (k : Fin n) : displacement p a k=
      ((permutation p a k-k : Fin n) : ℤ)-height p a := by
    unfold displacement
    rw [clockwise_difference_value]
  rw [he,he] at hij
  have hc : ((permutation p a i-i : Fin n) : ℤ)=((permutation p a j-j : Fin n) : ℤ) := by omega
  exact_mod_cast hc

/-- Every anchor of a complete mapping has the same half-size height. -/
theorem complete_height (p : State n) (hp : CompleteMapping p) (a : Fin n) :
    n=2*height p a+1 := by
  let f : State n := Equiv.ofBijective (fun i => permutation p a i-i)
    ⟨complete_shift_injective p hp a,Finite.surjective_of_injective (complete_shift_injective p hp a)⟩
  have hsum := Equiv.sum_comp f (fun i : Fin n => (i : ℤ))
  have hm := clockwise_representative_mass (permutation p a)
  simp_rw [clockwise_difference_value] at hm
  change (∑ i : Fin n, (f i : ℤ))=(n : ℤ)*height p a at hm
  rw [hsum] at hm
  have htri : 2*(∑ i : Fin n, (i : ℤ))=(n : ℤ)*((n : ℤ)-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact LX.Core.FiniteCoordinates.range_sum_twice n
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hh : (n : ℤ)=2*(height p a : ℤ)+1 := by nlinarith
  exact_mod_cast hh

/-- The distinct centered integer coordinates satisfy the full subset
majorization inequality, for every anchor, not just for a selected phase. -/
theorem complete_majorized (p : State n) (hp : CompleteMapping p) (a : Fin n) :
    LX.Core.AffineLift.Majorized (displacement p a) := by
  intro S
  have hinj : Set.InjOn (displacement p a) S := (complete_displacement_injective p hp a).injOn
  have hn := complete_height p hp a
  have hupper (i : Fin n) : displacement p a i ≤ height p a := by
    have hh := (displacement_band p a i).2
    omega
  have hhigh := Finset.sum_le_sum_range (s := S.image (displacement p a)) (c := (height p a : ℤ)) (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact hupper i)
  rw [Finset.card_image_iff.mpr hinj,Finset.sum_image hinj] at hhigh
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hhigh
  have htri := LX.Core.FiniteCoordinates.range_sum_twice S.card
  have hna : (n : ℤ)=2*(height p a : ℤ)+1 := by exact_mod_cast hn
  nlinarith

/-- Complete mappings have equally many strictly positive and negative
ordinary displacements. -/
theorem complete_positive_count (p : State n) (hp : CompleteMapping p) (h : ℕ)
    (hn : n=2*h+1) :
    (Finset.univ.filter (fun i : Fin n => i.val < (p i).val)).card=h := by
  obtain ⟨a,ha⟩ := (Finite.surjective_of_injective hp) 0
  have hfix : p a=a := sub_eq_zero.mp ha
  have hq : permutation p a=p := by
    ext i
    simp [permutation,hfix]
  have hheight := complete_height p hp a
  have hh : height p a=(descendingPositions p).card := by rw [height,hq]
  rw [hh] at hheight
  have hneg : (descendingPositions p).card=h := by omega
  have hzero : Finset.univ.filter (fun i : Fin n => p i=i)={a} := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    constructor
    · intro hi
      apply hp
      simp only [hi,hfix,sub_self]
    · rintro rfl
      exact hfix
  have hpoint (i : Fin n) :
      (if i.val < (p i).val then (1 : ℕ) else 0)+
      (if (p i).val < i.val then 1 else 0)+(if p i=i then 1 else 0)=1 := by
    have he : p i=i ↔ (p i).val=i.val := Fin.ext_iff
    simp only [he]
    split_ifs <;> omega
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin n))) rfl (fun i _ => hpoint i)
  simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one,hzero,Finset.card_singleton] at hsum
  change (Finset.univ.filter (fun i : Fin n => i.val < (p i).val)).card+
    (descendingPositions p).card+1=n at hsum
  omega


#print axioms complete_height
#print axioms complete_majorized
end LX.AnchoredPhases
