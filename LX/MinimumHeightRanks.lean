import LX.HeightReduction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Residues relative to the selected anchor, before balancing. -/
def cyclicOffset (p : State n) (a i : Fin n) : Fin n := p i-i-(p a-a)

def belowCount (p : State n) (a : Fin n) (t : ℕ) : ℕ :=
  (Finset.univ.filter fun i => (cyclicOffset p a i).val < t).card

theorem cyclic_subtraction_value (u v : Fin n) :
    ((u-v : Fin n) : ℤ)=(u : ℤ)-(v : ℤ)+if u.val < v.val then (n : ℤ) else 0 := by
  have hu := u.isLt
  have hv := v.isLt
  change (((u-v).val : ℕ) : ℤ)=_
  rw [Fin.val_sub]
  by_cases h : u.val < v.val
  · rw [Nat.mod_eq_of_lt (by omega : n-v.val+u.val < n),ite_eq_left h]
    omega
  · have he : n-v.val+u.val=n+(u.val-v.val) := by omega
    rw [he,Nat.add_mod_left,Nat.mod_eq_of_lt (by omega : u.val-v.val < n),ite_eq_right h]
    omega

theorem cyclic_offset_reanchor (p : State n) (a b i : Fin n) :
    cyclicOffset p b i=cyclicOffset p a i-cyclicOffset p a b := by
  unfold cyclicOffset
  abel

theorem cyclic_offset_mass (p : State n) (a : Fin n) :
    (∑ i : Fin n, (cyclicOffset p a i : ℤ))=(n : ℤ)*height p a :=
  offset_difference_mass p a

/-- Exact change of height, including every repeated cyclic displacement. -/
theorem reanchor_height (p : State n) (a b : Fin n) :
    (height p b : ℤ)=(height p a : ℤ)-(cyclicOffset p a b : ℤ)+
      belowCount p a (cyclicOffset p a b).val := by
  have hm := cyclic_offset_mass p b
  simp_rw [cyclic_offset_reanchor p a b,cyclic_subtraction_value] at hm
  have hcount : (∑ i : Fin n, if (cyclicOffset p a i).val < (cyclicOffset p a b).val
      then (n : ℤ) else 0)=(n : ℤ)*belowCount p a (cyclicOffset p a b).val := by
    rw [← Finset.sum_filter]
    simp [belowCount,mul_comm]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,cyclic_offset_mass,hcount] at hm
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
  apply mul_left_cancel₀ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  rw [mul_add,mul_sub]
  exact hm.symm

/-- Minimality is exactly a family of cumulative rank inequalities at occupied residues. -/
theorem minimum_height_iff_occupied_ranks (p : State n) (a : Fin n) :
    (∀ b, height p a ≤ height p b) ↔
      ∀ b, (cyclicOffset p a b).val ≤ belowCount p a (cyclicOffset p a b).val := by
  constructor
  · intro hmin b
    have hh := reanchor_height p a b
    have h := hmin b
    omega
  · intro hr b
    have hh := reanchor_height p a b
    have h := hr b
    omega

/-- The same rank inequality holds at every integer threshold, including gaps
in the multiset of offsets. No majorization hypothesis is used. -/
theorem minimum_height_ranks (p : State n) (a : Fin n)
    (hmin : ∀ b, height p a ≤ height p b) (t : ℕ) (ht : t ≤ n) :
    t ≤ belowCount p a t := by
  have hr := (minimum_height_iff_occupied_ranks p a).mp hmin
  by_cases hex : ∃ i : Fin n, t ≤ (cyclicOffset p a i).val
  · let S := Finset.univ.filter fun i => t ≤ (cyclicOffset p a i).val
    obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image S (fun i => (cyclicOffset p a i).val) (by
      obtain ⟨i,hi⟩ := hex
      exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
    have hbt := (Finset.mem_filter.mp hb).2
    have he : belowCount p a t=belowCount p a (cyclicOffset p a b).val := by
      unfold belowCount
      congr 1
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      constructor
      · intro hi
        omega
      · intro hi
        by_contra hnot
        have him : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
        have hh := hbmin i him
        omega
    rw [he]
    exact hbt.trans (hr b)
  · have hall (i : Fin n) : (cyclicOffset p a i).val < t := by
      by_contra hnot
      exact hex ⟨i,by omega⟩
    simpa [belowCount,hall] using ht

/-- Nonnegative surplus above the minimal cumulative rank requirement. -/
def rankSurplus (p : State n) (a : Fin n) (t : ℕ) : ℤ :=
  (belowCount p a t : ℤ)-(t : ℤ)

theorem rank_surplus_nonnegative (p : State n) (a : Fin n)
    (hmin : ∀ b, height p a ≤ height p b) (t : ℕ) (ht : t ≤ n) :
    0 ≤ rankSurplus p a t := by
  have hh := minimum_height_ranks p a hmin t ht
  unfold rankSurplus
  omega

theorem above_threshold_card (r : Fin n) :
    (∑ t : Fin n, if r.val < t.val then (1 : ℤ) else 0)=(n : ℤ)-1-(r : ℤ) := by
  have he : Finset.univ.filter (fun t : Fin n => r.val < t.val)=Finset.Ioi r := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Ioi,Fin.lt_def]
  have hc : (Finset.univ.filter (fun t : Fin n => r.val < t.val)).card=n-1-r.val := by
    rw [he,Fin.card_Ioi]
  have hsum : (∑ t : Fin n, if r.val < t.val then (1 : ℤ) else 0)=
      ((Finset.univ.filter (fun t : Fin n => r.val < t.val)).card : ℤ) := by simp
  rw [hsum,hc]
  have hh := r.isLt
  omega

theorem below_count_sum (p : State n) (a : Fin n) :
    (∑ t : Fin n, (belowCount p a t.val : ℤ))=(n : ℤ)*((n : ℤ)-1-height p a) := by
  simp only [belowCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  simp_rw [above_threshold_card]
  rw [Finset.sum_sub_distrib,cyclic_offset_mass]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

/-- Exact total rank surplus. In the remaining height cases it is at most 2n. -/
theorem rank_surplus_sum (p : State n) (a : Fin n) :
    2*(∑ t : Fin n, rankSurplus p a t.val)=
      (n : ℤ)*((n : ℤ)-1-2*height p a) := by
  simp only [rankSurplus,Finset.sum_sub_distrib]
  rw [below_count_sum]
  have htri : 2*(∑ t : Fin n, (t : ℤ))=(n : ℤ)*((n : ℤ)-1) := by
    rw [Fin.sum_univ_eq_sum_range]
    exact LRX.FiniteCoordinates.range_sum_twice n
  nlinarith

/-- A zero-surplus threshold is itself occupied and determines another anchor
with the same minimum height. -/
theorem zero_surplus_anchor (p : State n) (a : Fin n)
    (hmin : ∀ b, height p a ≤ height p b) (t : Fin n)
    (hz : rankSurplus p a t.val=0) :
    ∃ b : Fin n, cyclicOffset p a b=t ∧ height p b=height p a := by
  have hc : belowCount p a t.val=t.val := by unfold rankSurplus at hz; omega
  have hex : ∃ b : Fin n, (cyclicOffset p a b).val=t.val := by
    by_contra hnone
    have hn (b : Fin n) : (cyclicOffset p a b).val≠t.val := fun he => hnone ⟨b,he⟩
    have he : belowCount p a (t.val+1)=belowCount p a t.val := by
      unfold belowCount
      congr 1
      ext b
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hh := hn b
      omega
    have hr := minimum_height_ranks p a hmin (t.val+1) (by have := t.isLt; omega)
    rw [he,hc] at hr
    omega
  obtain ⟨b,hb⟩ := hex
  have he : cyclicOffset p a b=t := Fin.ext hb
  refine ⟨b,he,?_⟩
  have hh := reanchor_height p a b
  rw [he,hc] at hh
  omega

/-- At even maximal remaining height, at least half of the residue thresholds
supply minimum-height anchors. This is an actual phase-choice resource. -/
theorem even_minimum_anchor_count (p : State n) (a : Fin n)
    (hmin : ∀ b, height p a ≤ height p b) (hn : n=2*height p a+2) :
    height p a+1 ≤ (Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card := by
  have hp : (∑ t : Fin n, if rankSurplus p a t.val=0 then (0 : ℤ) else 1) ≤
      ∑ t : Fin n, rankSurplus p a t.val := by
    apply Finset.sum_le_sum
    intro t _
    have hh := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
    split_ifs <;> omega
  have hsum := rank_surplus_sum p a
  have hna : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have hcomp : (∑ t : Fin n, if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
      (n : ℤ)-(Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card := by
    have he (t : Fin n) : (if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
        1-(if rankSurplus p a t.val=0 then 1 else 0) := by split_ifs <;> norm_num
    simp_rw [he]
    simp [Finset.sum_sub_distrib]
  rw [hcomp] at hp
  nlinarith

#print axioms reanchor_height
#print axioms minimum_height_ranks
#print axioms rank_surplus_sum
#print axioms zero_surplus_anchor
#print axioms even_minimum_anchor_count
end LX.AnchoredPhases
