import Mathlib

namespace LX
open scoped BigOperators
variable {n : ℕ}

def sameColorPairs (χ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n,∑ j : Fin n,if i < j ∧ χ i=χ j then 1 else 0

def colorCount (χ : Fin n → Bool) (b : Bool) : ℕ :=
  (Finset.univ.filter fun i => χ i=b).card

theorem color_count_sum (χ : Fin n → Bool) : colorCount χ true+colorCount χ false=n := by
  have hp (i : Fin n) : (if χ i=true then 1 else 0)+(if χ i=false then 1 else 0)=(1 : ℕ) := by
    cases χ i <;> simp
  have hs := congrArg (fun f : Fin n → ℕ => ∑ i,f i) (funext hp)
  convert hs using 1 <;>
    simp only [Finset.sum_add_distrib,Finset.sum_boole,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,mul_one,colorCount] <;> rfl

theorem same_color_pair_count (χ : Fin n → Bool) :
    2*sameColorPairs χ+n=(colorCount χ true)^2+(colorCount χ false)^2 := by
  have hrow (i : Fin n) : (∑ j : Fin n,if χ i=χ j then 1 else 0)=
      if χ i=true then colorCount χ true else colorCount χ false := by
    have hset : (Finset.univ.filter fun j : Fin n => χ i=χ j)=
        (Finset.univ.filter fun j : Fin n => χ j=χ i) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact eq_comm
    rw [Finset.sum_boole,hset]
    change colorCount χ (χ i)=_
    cases hc : χ i <;> simp only [Bool.false_eq_true,ite_false,ite_true]
  have hall : (∑ i : Fin n,∑ j : Fin n,if χ i=χ j then 1 else 0)=
      (colorCount χ true)^2+(colorCount χ false)^2 := by
    simp_rw [hrow]
    rw [Finset.sum_ite]
    have hnot : (Finset.univ.filter fun i : Fin n => ¬χ i=true)=
        (Finset.univ.filter fun i : Fin n => χ i=false) := by ext i; cases χ i <;> simp
    simp only [Finset.sum_const,hnot,smul_eq_mul]
    change colorCount χ true*colorCount χ true+colorCount χ false*colorCount χ false=_
    ring
  have hp (i j : Fin n) : (if χ i=χ j then 1 else 0)=
      (if i < j ∧ χ i=χ j then 1 else 0)+
      (if j < i ∧ χ j=χ i then 1 else 0)+(if i=j then 1 else 0 : ℕ) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_lt h]
    · subst j; simp
    · simp [h,not_lt_of_ge (le_of_lt h),ne_of_gt h,eq_comm]
  have hflip : (∑ i : Fin n,∑ j : Fin n,if j < i ∧ χ j=χ i then 1 else 0)=sameColorPairs χ :=
    Finset.sum_comm
  have hsum := congrArg (fun f : Fin n → Fin n → ℕ => ∑ i,∑ j,f i j)
    (funext fun i => funext (hp i))
  simp only [Finset.sum_add_distrib] at hsum
  rw [hall,hflip] at hsum
  have hdiag : (∑ i : Fin n,∑ j : Fin n,if i=j then 1 else 0)=n := by simp
  rw [hdiag] at hsum
  change _=sameColorPairs χ+sameColorPairs χ+n at hsum
  omega

theorem even_same_color_pairs_lower (χ : Fin n → Bool) (m : ℕ) (hn : n=2*m) :
    m*(m-1) ≤ sameColorPairs χ := by
  by_cases hm : m=0
  · subst m; simp
  have hs := color_count_sum χ
  have hp := same_color_pair_count χ
  have hs' : (colorCount χ true : ℤ)+(colorCount χ false : ℤ)=2*m := by omega
  have hp' : 2*(sameColorPairs χ : ℤ)+(n : ℤ)=
      (colorCount χ true : ℤ)^2+(colorCount χ false : ℤ)^2 := by exact_mod_cast hp
  have hn' : (n : ℤ)=2*m := by omega
  have hm' : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  zify
  rw [hm']
  nlinarith [sq_nonneg ((colorCount χ true : ℤ)-m)]

theorem odd_same_color_pairs_lower (χ : Fin n → Bool) (m : ℕ) (hn : n=2*m+1) :
    m^2 ≤ sameColorPairs χ := by
  have hs := color_count_sum χ
  have hp := same_color_pair_count χ
  have hs' : (colorCount χ true : ℤ)+(colorCount χ false : ℤ)=2*m+1 := by omega
  have hp' : 2*(sameColorPairs χ : ℤ)+(n : ℤ)=
      (colorCount χ true : ℤ)^2+(colorCount χ false : ℤ)^2 := by exact_mod_cast hp
  have hn' : (n : ℤ)=2*m+1 := by omega
  have hsq := sq_nonneg ((colorCount χ true : ℤ)-(colorCount χ false : ℤ))
  have he : (m : ℤ)^2 ≤ (sameColorPairs χ : ℤ) := by nlinarith
  exact_mod_cast he

#print axioms even_same_color_pairs_lower
#print axioms odd_same_color_pairs_lower
end LX
