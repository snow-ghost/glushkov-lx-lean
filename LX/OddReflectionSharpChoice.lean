import LX.ReflectionNeighbor
import LX.ReflectionPhases
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The two exceptional families are retained explicitly; all other adjacent
perturbations have a cheap phase containing the deleted crossing. -/
theorem odd_reflection_sharp_crossing_choice (p : State n) (r i : Fin n)
    (hp : ∀ j,p j=r-j) (m : ℕ) (hn : n=2*m+1) (hm : 3 ≤ m) :
    (∃ a : Fin n,0 < a.val ∧ a.val+m ≤ (p a).val+2 ∧
      3 ≤ a.val+(n-(p a).val) ∧ 2 ≤ (cyclicOffset p a i).val) ∨
      (r.val=m ∧ i.val=m+1) ∨ (r.val=m+1 ∧ i.val=1) := by
  have hv1 : (1 : Fin n).val=1 := by norm_num [Nat.mod_eq_of_lt (by omega : 1<n)]
  have hdouble : (m : Fin n)+(m : Fin n)+1=0 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Fin.natCast_self] at he
    linear_combination -he
  by_cases hrhi : m+2 ≤ r.val
  · let a : Fin n := ⟨1,by omega⟩
    have hav : a.val=1 := rfl
    have hbval : (a+1).val=2 := by rw [Fin.val_add_one_of_lt' (by omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=1 ∨ j.val=2) :
        0 < j.val ∧ j.val+m ≤ (p j).val+2 ∧ 3 ≤ j.val+(n-(p j).val) := by
      have hjr : j ≤ r := by change j.val ≤ r.val; omega
      rw [hp,Fin.coe_sub_iff_le.mpr hjr]
      have := r.isLt
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact Or.inl ⟨b,hg.1,hg.2.1,hg.2.2,hcross⟩
  by_cases hrlo : r.val < m
  · let a : Fin n := ⟨max 2 (r.val+1),by omega⟩
    have hav : a.val=max 2 (r.val+1) := rfl
    have hbval : (a+1).val=max 2 (r.val+1)+1 := by
      rw [Fin.val_add_one_of_lt' (by omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=max 2 (r.val+1) ∨ j.val=max 2 (r.val+1)+1) :
        0 < j.val ∧ j.val+m ≤ (p j).val+2 ∧ 3 ≤ j.val+(n-(p j).val) := by
      have hjr : r < j := by change r.val < j.val; omega
      rw [hp,Fin.coe_sub_iff_lt.mpr hjr]
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact Or.inl ⟨b,hg.1,hg.2.1,hg.2.2,hcross⟩
  have hgood1 : 0 < (1 : Fin n).val ∧ (1 : Fin n).val+m ≤ (p 1).val+2 ∧
      3 ≤ (1 : Fin n).val+(n-(p 1).val) := by
    have hle : (1 : Fin n) ≤ r := by change (1 : Fin n).val ≤ r.val; omega
    rw [hp,Fin.coe_sub_iff_le.mpr hle,hv1]
    omega
  by_cases hcross1 : 2 ≤ (cyclicOffset p 1 i).val
  · exact Or.inl ⟨1,hgood1.1,hgood1.2.1,hgood1.2.2,hcross1⟩
  have hc := reflection_complete_odd p r hp m hn
  by_cases hr : r.val=m
  · let b : Fin n := ⟨m+1,by omega⟩
    have hbval : b.val=m+1 := rfl
    have hb : b=(m : Fin n)+1 := by
      apply Fin.ext
      change m+1=(m%n+1%n)%n
      rw [Nat.mod_eq_of_lt (by omega : m<n),Nat.mod_eq_of_lt (by omega : 1<n),Nat.mod_eq_of_lt (by omega)]
    have hgood : 0 < b.val ∧ b.val+m ≤ (p b).val+2 ∧ 3 ≤ b.val+(n-(p b).val) := by
      have hlt : r < b := by change r.val < b.val; omega
      rw [hp,Fin.coe_sub_iff_lt.mpr hlt]
      omega
    by_cases hcross : 2 ≤ (cyclicOffset p b i).val
    · exact Or.inl ⟨b,hgood.1,hgood.2.1,hgood.2.2,hcross⟩
    have he : cyclicOffset p 1 i=cyclicOffset p b i+1 := by
      unfold cyclicOffset
      simp only [hp,hb]
      linear_combination -hdouble
    have hv := congrArg Fin.val he
    rw [Fin.val_add_one_of_lt' (by omega : (cyclicOffset p b i).val+1<n)] at hv
    have hz : cyclicOffset p b i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have hi : i=b := hc (sub_eq_zero.mp hz)
    exact Or.inr (Or.inl ⟨hr,by rw [hi,hbval]⟩)
  · have hr' : r.val=m+1 := by omega
    let b : Fin n := ⟨m+2,by omega⟩
    have hbval : b.val=m+2 := rfl
    have hb : b=(m : Fin n)+2 := by
      apply Fin.ext
      change m+2=(m%n+2%n)%n
      rw [Nat.mod_eq_of_lt (by omega : m<n),Nat.mod_eq_of_lt (by omega : 2<n),Nat.mod_eq_of_lt (by omega)]
    have hgood : 0 < b.val ∧ b.val+m ≤ (p b).val+2 ∧ 3 ≤ b.val+(n-(p b).val) := by
      have hlt : r < b := by change r.val < b.val; omega
      rw [hp,Fin.coe_sub_iff_lt.mpr hlt]
      omega
    by_cases hcross : 2 ≤ (cyclicOffset p b i).val
    · exact Or.inl ⟨b,hgood.1,hgood.2.1,hgood.2.2,hcross⟩
    have he : cyclicOffset p b i=cyclicOffset p 1 i+1 := by
      unfold cyclicOffset
      simp only [hp,hb]
      linear_combination hdouble
    have hv := congrArg Fin.val he
    rw [Fin.val_add_one_of_lt' (by omega : (cyclicOffset p 1 i).val+1<n)] at hv
    have hz : cyclicOffset p 1 i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    have hi : i=(1 : Fin n) := hc (sub_eq_zero.mp hz)
    exact Or.inr (Or.inr ⟨hr',by rw [hi,hv1]⟩)

#print axioms odd_reflection_sharp_crossing_choice
end LX.AnchoredPhases
