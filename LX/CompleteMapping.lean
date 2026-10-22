import LX.OddAnchorPrice
import LRX.FiniteCoordinateCapacity

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- Distinct cyclic displacements, also called a complete mapping of the cycle. -/
def CompleteMapping (p : State n) : Prop := Function.Injective (fun i => p i-i)

theorem clockwise_difference_value (q : State n) (i : Fin n) :
    clockwiseRepresentative q i-(i : ℤ)=((q i-i : Fin n) : ℤ) := by
  have hb := clockwise_representative_bounds q i
  have hc := LRX.AffineLift.cast_eq_of_modEq (clockwise_representative_modEq q i)
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
    exact LRX.FiniteCoordinates.range_sum_twice n
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hh : (n : ℤ)=2*(height p a : ℤ)+1 := by nlinarith
  exact_mod_cast hh

/-- The distinct centered integer coordinates satisfy the full subset
majorization inequality, for every anchor, not just for a selected phase. -/
theorem complete_majorized (p : State n) (hp : CompleteMapping p) (a : Fin n) :
    LRX.AffineLift.Majorized (displacement p a) := by
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
  have htri := LRX.FiniteCoordinates.range_sum_twice S.card
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

/-- A complete mapping has an anchor with almost half-circle forward span;
only five exceptional displacement values/positions need be discarded. -/
theorem complete_good_anchor (p : State n) (hp : CompleteMapping p) (h : ℕ)
    (hn : n=2*h+1) (hh : 6 ≤ h) :
    ∃ a : Fin n, 0 < a.val ∧ a.val+h ≤ (p a).val+5 ∧
      5 ≤ a.val+(n-(p a).val) := by
  let P := Finset.univ.filter (fun i : Fin n => i.val < (p i).val)
  let δ := fun i : Fin n => (p i).val-i.val
  have hcard : P.card=h := complete_positive_count p hp h hn
  have hinj : Set.InjOn δ P := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply hp
    have hcast := congrArg (fun k : ℕ => (k : Fin n)) he
    simpa only [δ,Nat.cast_sub (Nat.le_of_lt hi'),Nat.cast_sub (Nat.le_of_lt hj'),
      Fin.cast_val_eq_self] using hcast
  by_contra hnone
  push Not at hnone
  let S : Finset ℕ := (Finset.Icc 1 (h-6) ∪ Finset.Icc (n-4) (n-1)) ∪ {δ 0}
  have hsub : P.image δ ⊆ S := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hpa := (Finset.mem_filter.mp ha).2
    have hpn := (p a).isLt
    by_cases ha0 : a=0
    · subst a
      simp [S]
    · have hap : 0 < a.val := Fin.pos_iff_ne_zero.mpr ha0
      by_cases hlo : δ a ≤ h-6
      · have hδpos : 0 < δ a := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inl ⟨hδpos,hlo⟩)
      · have hforward : a.val+h ≤ (p a).val+5 := by dsimp [δ] at hlo; omega
        have hnot := hnone a hap hforward
        have hδhi : n-4 ≤ δ a ∧ δ a ≤ n-1 := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inr hδhi)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,hcard] at hc
  have hcu := Finset.card_union_le (Finset.Icc 1 (h-6) ∪ Finset.Icc (n-4) (n-1)) {δ 0}
  have hcu' := Finset.card_union_le (Finset.Icc 1 (h-6)) (Finset.Icc (n-4) (n-1))
  change S.card ≤ _ at hcu
  simp only [Nat.card_Icc,Finset.card_singleton] at hcu hcu'
  omega

/-- The requested quadratic and linear terms hold uniformly for the complete
mapping family. The constant also pays all dimensions below the crowding range. -/
theorem complete_mapping_upper_word (p : State n) (hp : CompleteMapping p) (hn : 4 ≤ n) :
    ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases hsmall : n < 13
  · obtain ⟨w,hw,hprice⟩ := exists_quadratic_coarse_word (by omega : 2 ≤ n) p⁻¹
    refine ⟨w,?_,?_⟩
    · rw [hw,mul_inv_cancel]
    · nlinarith
  · let h := height p 0
    have hparity : n=2*h+1 := complete_height p hp 0
    obtain ⟨a,ha,hforward,hcorner⟩ := complete_good_anchor p hp h hparity (by omega)
    have hheight : height p a=h := by have := complete_height p hp a; omega
    obtain ⟨w,hw,hprice⟩ := odd_forward_anchor_word p a 5 (complete_majorized p hp a)
      (by omega) (by omega) ha (by omega) hcorner
    exact ⟨w,hw,by norm_num at hprice ⊢; omega⟩

#print axioms complete_height
#print axioms complete_majorized
#print axioms complete_good_anchor
#print axioms complete_mapping_upper_word
end LX.AnchoredPhases
