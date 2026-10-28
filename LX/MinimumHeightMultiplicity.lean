import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
private theorem rank_bonus_sum (f : ℕ) (hf : 0 < f) (hfn : f ≤ n) :
    2*(∑ t : Fin n,if 0 < t.val ∧ t.val < f then (f : ℤ)-t.val-1 else 0)=
      ((f : ℤ)-1)*(f-2) := by
  let B := fun k : ℕ => if 0 < k ∧ k < f then (f : ℤ)-k-1 else 0
  have hsum : (∑ t : Fin n,B t.val)=∑ k ∈ Finset.range f,B k := by
    rw [Fin.sum_univ_eq_sum_range]
    symm
    apply Finset.sum_subset (Finset.range_mono hfn)
    intro k _ hk
    have hk' : ¬k < f := by simpa only [Finset.mem_range] using hk
    simp [B,hk']
  change 2*(∑ t : Fin n,B t.val)=_
  rw [hsum]
  have hp : (∑ k ∈ Finset.range f,B k)=
      (f : ℤ)*((f : ℤ)-1)-(∑ k ∈ Finset.range f,(k : ℤ))-((f : ℤ)-1) := by
    calc
      _ = ∑ k ∈ Finset.range f,
          ((((f : ℤ)-1)-(k : ℤ))-(if k=0 then (f : ℤ)-1 else 0)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        dsimp only [B]
        by_cases hz : k=0
        · subst k; simp
        · rw [ite_eq_left ⟨by omega,hk'⟩,ite_eq_right hz]; ring
      _ = _ := by simp [Finset.sum_sub_distrib,hf]; ring
  rw [hp]
  have ht := LX.Core.FiniteCoordinates.range_sum_twice f
  nlinarith

/-- A large fixed fiber forces quadratically many additional minimum-height
offsets. Its whole rank-surplus contribution is retained in the count. -/
theorem even_minimum_anchor_count_with_fixed (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+2) :
    (n : ℤ)+(((fixedPositions (permutation p a)).card : ℤ)-1)*
        (((fixedPositions (permutation p a)).card : ℤ)-2) ≤
      2*((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ) := by
  classical
  let f := (fixedPositions (permutation p a)).card
  have hf : 0 < f := Finset.card_pos.mpr
    ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
  have hfn : f ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hbelow (t : ℕ) (ht : 0 < t) : f ≤ belowCount p a t := by
    apply Finset.card_le_card
    intro i hi
    have hz := (offset_zero_iff_source_fixed p a i).mpr ((mem_fixedPositions _ _).mp hi)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hz,Fin.val_zero]
    exact ht
  have hp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)+
      (∑ t : Fin n,if 0 < t.val ∧ t.val < f then (f : ℤ)-t.val-1 else 0) ≤
        ∑ t : Fin n,rankSurplus p a t.val := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
    by_cases ht : 0 < t.val ∧ t.val < f
    · have hb := hbelow t.val ht.1
      have hne : rankSurplus p a t.val ≠ 0 := by unfold rankSurplus; omega
      rw [ite_eq_right hne,ite_eq_left ht]
      unfold rankSurplus
      omega
    · rw [ite_eq_right ht,add_zero]
      split_ifs <;> omega
  have hcomp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
      (n : ℤ)-(Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card := by
    have he (t : Fin n) : (if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
        1-(if rankSurplus p a t.val=0 then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  rw [hcomp] at hp
  have hb := rank_bonus_sum f hf hfn
  have hs := rank_surplus_sum p a
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  change (n : ℤ)+((f : ℤ)-1)*(f-2) ≤ _
  nlinarith

def rawOffsets (p : State n) : Finset (Fin n) :=
  Finset.univ.image (fun i => p i-i)


theorem zero_surplus_count_le_raw_offsets (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card ≤
      (rawOffsets p).card := by
  classical
  let Z := Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)
  have hsub : Z.image (fun t => p a-a+t) ⊆ rawOffsets p := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨b,hb,_⟩ := zero_surplus_anchor p a hmin t (Finset.mem_filter.mp ht).2
    apply Finset.mem_image.mpr
    refine ⟨b,Finset.mem_univ _,?_⟩
    unfold cyclicOffset at hb
    linear_combination hb
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (add_right_injective (p a-a))] at hc
  exact hc

theorem even_raw_offset_count_with_fixed (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+2) :
    (n : ℤ)+(((fixedPositions (permutation p a)).card : ℤ)-1)*
        (((fixedPositions (permutation p a)).card : ℤ)-2) ≤
      2*((rawOffsets p).card : ℤ) := by
  have hc := even_minimum_anchor_count_with_fixed p a hmin hn
  have hle := zero_surplus_count_le_raw_offsets p a hmin
  omega

#print axioms even_minimum_anchor_count_with_fixed
#print axioms zero_surplus_count_le_raw_offsets
#print axioms even_raw_offset_count_with_fixed
end LX.AnchoredPhases
