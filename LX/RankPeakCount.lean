import LX.NextOccupiedPhase
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem below_count_mono (p : State n) (a : Fin n) {r t : ℕ} (hrt : r ≤ t) :
    belowCount p a r ≤ belowCount p a t := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hrt⟩

omit [NeZero n] in
theorem below_count_succ (p : State n) (a : Fin n) (t : ℕ) :
    belowCount p a (t+1)=belowCount p a t+
      (Finset.univ.filter fun i => (cyclicOffset p a i).val=t).card := by
  classical
  have he : Finset.univ.filter (fun i => (cyclicOffset p a i).val < t+1)=
      (Finset.univ.filter fun i => (cyclicOffset p a i).val < t) ∪
        (Finset.univ.filter fun i => (cyclicOffset p a i).val=t) := by
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
    omega
  have hd : Disjoint (Finset.univ.filter fun i => (cyclicOffset p a i).val < t)
      (Finset.univ.filter fun i => (cyclicOffset p a i).val=t) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hlt := (Finset.mem_filter.mp hi).2
    have heq := (Finset.mem_filter.mp hj).2
    omega
  unfold belowCount
  rw [he,Finset.card_union_of_disjoint hd]

theorem offset_fiber_count (p : State n) (a b : Fin n) :
    (Finset.univ.filter fun i => (cyclicOffset p a i).val=(cyclicOffset p a b).val).card=
      (fixedPositions (permutation p b)).card := by
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,mem_fixedPositions]
  rw [← offset_zero_iff_source_fixed,cyclic_offset_reanchor p a b i,sub_eq_zero,Fin.ext_iff]

/-- A maximal rank surplus bounds every actual height and fixed fiber. -/
theorem rank_peak_anchor_bounds (p : State n) (a : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R) :
    (∀ b,height p a ≤ height p b ∧ height p b ≤ height p a+R) ∧
      (∀ b,(fixedPositions (permutation p b)).card ≤ R+1) := by
  constructor
  · intro b
    have hr := hR (cyclicOffset p a b)
    have hh := reanchor_height p a b
    unfold rankSurplus at hr
    exact ⟨hmin b,by omega⟩
  · intro b
    let t := (cyclicOffset p a b).val
    have ht : t < n := (cyclicOffset p a b).isLt
    have hs := below_count_succ p a t
    rw [offset_fiber_count] at hs
    have hr := minimum_height_ranks p a hmin t (Nat.le_of_lt ht)
    by_cases htn : t+1 < n
    · have hb := hR ⟨t+1,htn⟩
      change (belowCount p a (t+1) : ℤ)-(t+1 : ℕ) ≤ R at hb
      omega
    · have hc : belowCount p a (t+1) ≤ n :=
        (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
      omega

omit [NeZero n] in
private theorem interval_rank_bonus_sum (r R : ℕ) (hbound : r+R ≤ n) :
    2*(∑ t : Fin n,if r ≤ t.val ∧ t.val < r+R then (R : ℤ)+r-t.val-1 else 0)=
      (R : ℤ)*(R-1) := by
  let B := fun k : ℕ => if r ≤ k ∧ k < r+R then (R : ℤ)+r-k-1 else 0
  have hsum : (∑ t : Fin n,B t.val)=∑ k ∈ Finset.range (r+R),B k := by
    rw [Fin.sum_univ_eq_sum_range]
    symm
    apply Finset.sum_subset (Finset.range_mono hbound)
    intro k _ hk
    have hk' : ¬k < r+R := by simpa only [Finset.mem_range] using hk
    simp [B,hk']
  change 2*(∑ t : Fin n,B t.val)=_
  rw [hsum,Finset.sum_range_add]
  have hz : (∑ k ∈ Finset.range r,B k)=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' := Finset.mem_range.mp hk
    simp [B,show ¬r ≤ k by omega]
  have he : (∑ k ∈ Finset.range R,B (r+k))=
      (R : ℤ)*((R : ℤ)-1)-∑ k ∈ Finset.range R,(k : ℤ) := by
    calc
      _ = ∑ k ∈ Finset.range R,((R : ℤ)-1-(k : ℤ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' := Finset.mem_range.mp hk
        simp only [B,ite_eq_left (show r ≤ r+k ∧ r+k < r+R by omega),Nat.cast_add]
        ring
      _ = _ := by simp [Finset.sum_sub_distrib]; ring
  rw [hz,zero_add,he]
  have ht := LRX.FiniteCoordinates.range_sum_twice R
  nlinarith


def minimumHeightOffsets (p : State n) (h : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter fun i => height p i=h).image (fun i => p i-i)

theorem zero_surplus_count_eq_minimum_offsets (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) :
    (Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card=
      (minimumHeightOffsets p (height p a)).card := by
  classical
  let Z := Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)
  have he : Z.image (fun t => p a-a+t)=minimumHeightOffsets p (height p a) := by
    ext x
    constructor
    · intro hx
      obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨b,hb,hh⟩ := zero_surplus_anchor p a hmin t (Finset.mem_filter.mp ht).2
      apply Finset.mem_image.mpr
      refine ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩,?_⟩
      unfold cyclicOffset at hb
      linear_combination hb
    · intro hx
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hx
      have hh := (Finset.mem_filter.mp hb).2
      apply Finset.mem_image.mpr
      refine ⟨cyclicOffset p a b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,?_⟩
      · have hr := reanchor_height p a b
        unfold rankSurplus
        omega
      · unfold cyclicOffset
        ring
  have hc := congrArg Finset.card he
  rw [Finset.card_image_of_injective _ (add_right_injective (p a-a))] at hc
  exact hc

#print axioms rank_peak_anchor_bounds
#print axioms zero_surplus_count_eq_minimum_offsets

/-- The second rank excess pays the peak, with the exact total-rank correction. -/
theorem minimum_count_minus_high_count (p : State n) (a r : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b)
    (hRpos : 0 < R) (hpeak : rankSurplus p a r.val=R) :
    ((R : ℤ)-1)*(R-2) ≤
      2*((Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card : ℤ)-
        2*((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ)+
        (n : ℤ)*((n : ℤ)-3-2*height p a) := by
  have hcard : belowCount p a r.val ≤ n :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hbound : r.val+(R-1) ≤ n := by unfold rankSurplus at hpeak; omega
  have hp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)+
      (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0)+
      (∑ t : Fin n,if r.val ≤ t.val ∧ t.val < r.val+(R-1) then
        ((R-1 : ℕ) : ℤ)+r.val-t.val-1 else 0) ≤
        ∑ t : Fin n,rankSurplus p a t.val := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
    by_cases ht : r.val ≤ t.val ∧ t.val < r.val+(R-1)
    · have hmono := below_count_mono p a ht.1
      have hpos : 2 ≤ rankSurplus p a t.val := by unfold rankSurplus at *; omega
      rw [ite_eq_right (by omega : rankSurplus p a t.val ≠ 0),ite_eq_left hpos,ite_eq_left ht]
      unfold rankSurplus at *
      omega
    · rw [ite_eq_right ht,add_zero]
      split_ifs <;> omega
  have hcomp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
      (n : ℤ)-(Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card := by
    have he (t : Fin n) : (if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
        1-(if rankSurplus p a t.val=0 then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  have hhigh : (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ) := by simp
  rw [hcomp,hhigh] at hp
  have hb := interval_rank_bonus_sum r.val (R-1) hbound
  have hs := rank_surplus_sum p a
  rw [Nat.cast_sub hRpos,Nat.cast_one] at hb hp
  nlinarith


/-- A surplus-one threshold is occupied, or the immediately following
threshold is a minimum-height anchor. This includes the cyclic seam. -/
theorem rank_one_occupied_or_next_minimum (p : State n) (a t : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hone : rankSurplus p a t.val=1) :
    (∃ b : Fin n,cyclicOffset p a b=t ∧ height p b=height p a+1) ∨
      (∃ b : Fin n,cyclicOffset p a b=t+1 ∧ height p b=height p a) := by
  classical
  by_cases hex : ∃ b : Fin n,cyclicOffset p a b=t
  · obtain ⟨b,hb⟩ := hex
    have hh := reanchor_height p a b
    rw [hb] at hh
    unfold rankSurplus at hone
    exact Or.inl ⟨b,hb,by omega⟩
  · have hf : (Finset.univ.filter fun i => (cyclicOffset p a i).val=t.val).card=0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.filter_eq_empty_iff.mpr
      intro i _ he
      exact hex ⟨i,Fin.ext he⟩
    have hs := below_count_succ p a t.val
    rw [hf,add_zero] at hs
    by_cases ht : t.val+1 < n
    · let u : Fin n := ((t.val+1 : ℕ) : Fin n)
      have hu : u=t+1 := by simp only [u,Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one]
      have huv : u.val=t.val+1 := Nat.mod_eq_of_lt ht
      have hz : rankSurplus p a u.val=0 := by
        rw [huv]
        unfold rankSurplus at hone ⊢
        omega
      obtain ⟨b,hb,hh⟩ := zero_surplus_anchor p a hmin u hz
      exact Or.inr ⟨b,hb.trans hu,hh⟩
    · have htn : t.val+1=n := by have := t.isLt; omega
      have hz : t+1=0 := by
        have he : ((t.val+1 : ℕ) : Fin n)=0 := by rw [htn,Fin.natCast_self]
        simpa only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_one] using he
      exact Or.inr ⟨a,by simp [cyclicOffset,hz],rfl⟩

#print axioms rank_one_occupied_or_next_minimum
end LX.AnchoredPhases
