import LX.ReflectionPhases
import LX.AdjacentDeletion

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Two consecutive anchors cannot both miss the chosen neighboring pair.
The two excluded residues are 0 and 1, while an anchor step adds 2. -/
theorem reflection_two_anchor_choice (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a i : Fin n) :
    ∃ b : Fin n,(b=a ∨ b=a+1) ∧ 2 ≤ (cyclicOffset p b i).val := by
  by_cases ha : 2 ≤ (cyclicOffset p a i).val
  · exact ⟨a,Or.inl rfl,ha⟩
  · refine ⟨a+1,Or.inr rfl,?_⟩
    have he : cyclicOffset p (a+1) i=cyclicOffset p a i+2 := by
      unfold cyclicOffset
      simp only [hp]
      ring
    have hv : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)]
    rw [he,Fin.val_add,hv,Nat.mod_eq_of_lt (by omega)]
    omega

theorem reflection_neighbor_descent (hn : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (a i : Fin n) (hi : 2 ≤ (cyclicOffset p a i).val) :
    displacement p a (i+1)+1 < displacement p a i := by
  have he : cyclicOffset p a (i+1)=cyclicOffset p a i-2 := by
    unfold cyclicOffset
    simp only [hp]
    ring
  have hv : (2 : Fin n).val=2 := by norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)]
  have hle : (2 : Fin n) ≤ cyclicOffset p a i := by change (2 : Fin n).val ≤ _; omega
  have heval : (cyclicOffset p a (i+1)).val=(cyclicOffset p a i).val-2 := by
    rw [he,Fin.coe_sub_iff_le.mpr hle,hv]
  rw [displacement_offset,displacement_offset]
  omega

/-- Even reflections have two cheap consecutive late anchors; one of them
also contains the required crossing. The last reflection parameter is handled
without charging an unnecessary full final turn. -/
theorem even_reflection_neighbor_anchor (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m) (hm : 10 ≤ m) (i : Fin n) :
    ∃ a : Fin n,m < a.val ∧ a.val+(-p a).val ≤ n+5 ∧
      2 ≤ (cyclicOffset p a i).val := by
  have hneg (j : Fin n) : -p j=j-r := by rw [hp]; abel
  by_cases hr : r.val=n-1
  · let a : Fin n := ⟨m+1,by omega⟩
    have hav : a.val=m+1 := rfl
    have hbval : (a+1).val=m+2 := by
      rw [Fin.val_add_one_of_lt' (by omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=m+1 ∨ j.val=m+2) :
        m < j.val ∧ j.val+(-p j).val ≤ n+5 := by
      have hjr : j < r := by change j.val < r.val; omega
      rw [hneg,Fin.coe_sub_iff_lt.mpr hjr]
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg : m < b.val ∧ b.val+(-p b).val ≤ n+5 := by
      rcases hb with rfl | rfl
      · exact hgood a (Or.inl hav)
      · exact hgood (a+1) (Or.inr hbval)
    exact ⟨b,hg.1,hg.2,hcross⟩
  · let a : Fin n := ⟨max (m+1) r.val,by have := r.isLt; omega⟩
    have hav : a.val=max (m+1) r.val := rfl
    have hbval : (a+1).val=max (m+1) r.val+1 := by
      rw [Fin.val_add_one_of_lt' (by have := r.isLt; omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=max (m+1) r.val ∨ j.val=max (m+1) r.val+1) :
        m < j.val ∧ j.val+(-p j).val ≤ n+5 := by
      have hjr : r ≤ j := by change r.val ≤ j.val; omega
      rw [hneg,Fin.coe_sub_iff_le.mpr hjr]
      have := r.isLt
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg : m < b.val ∧ b.val+(-p b).val ≤ n+5 := by
      rcases hb with rfl | rfl
      · exact hgood a (Or.inl hav)
      · exact hgood (a+1) (Or.inr hbval)
    exact ⟨b,hg.1,hg.2,hcross⟩

/-- Odd reflections have two cheap consecutive forward anchors. A fixed
allowance of ten covers both choices and the forbidden-corner condition. -/
theorem odd_reflection_neighbor_anchor (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (m : ℕ) (hn : n=2*m+1) (hm : 10 ≤ m) (i : Fin n) :
    ∃ a : Fin n,0 < a.val ∧ a.val+m ≤ (p a).val+10 ∧
      5 ≤ a.val+(n-(p a).val) ∧ 2 ≤ (cyclicOffset p a i).val := by
  by_cases hr : m ≤ r.val
  · let a : Fin n := ⟨3,by omega⟩
    have hav : a.val=3 := rfl
    have hbval : (a+1).val=4 := by rw [Fin.val_add_one_of_lt' (by omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=3 ∨ j.val=4) :
        0 < j.val ∧ j.val+m ≤ (p j).val+10 ∧ 5 ≤ j.val+(n-(p j).val) := by
      have hjr : j ≤ r := by change j.val ≤ r.val; omega
      rw [hp,Fin.coe_sub_iff_le.mpr hjr]
      have := r.isLt
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact ⟨b,hg.1,hg.2.1,hg.2.2,hcross⟩
  · let a : Fin n := ⟨r.val+3,by omega⟩
    have hav : a.val=r.val+3 := rfl
    have hbval : (a+1).val=r.val+4 := by rw [Fin.val_add_one_of_lt' (by omega : a.val+1<n),hav]
    have hgood (j : Fin n) (hj : j.val=r.val+3 ∨ j.val=r.val+4) :
        0 < j.val ∧ j.val+m ≤ (p j).val+10 ∧ 5 ≤ j.val+(n-(p j).val) := by
      have hjr : r < j := by change r.val < j.val; omega
      rw [hp,Fin.coe_sub_iff_lt.mpr hjr]
      omega
    obtain ⟨b,hb,hcross⟩ := reflection_two_anchor_choice (by omega) p r hp a i
    have hg := hgood b (by rcases hb with rfl | rfl; exact Or.inl hav; exact Or.inr hbval)
    exact ⟨b,hg.1,hg.2.1,hg.2.2,hcross⟩

/-- Every neighboring-position perturbation of a circular reflection has
an actual short LX word. The construction deletes a proved crossing event,
including when the perturbed pair crosses the seam. -/
theorem reflection_neighbor_upper_word (hn4 : 4 ≤ n) (p : State n) (r : Fin n)
    (hp : ∀ i,p i=r-i) (i : Fin n) :
    ∃ w : List Letter,(p*Equiv.swap i (i+1))*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_cases hsmall : n < 22
  · obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 (p*Equiv.swap i (i+1))⁻¹
    refine ⟨w,?_,?_⟩
    · rw [hw,mul_inv_cancel]
    · have hs : (n : ℤ)<22 := by omega
      nlinarith
  · by_cases heven : n=2*(n/2)
    · obtain ⟨a,ha,hfinish,hcross⟩ := even_reflection_neighbor_anchor p r hp (n/2) heven (by omega) i
      obtain ⟨w,hw,hzero,hprice⟩ := reflection_anchor_zero_word_even p r hp (n/2) heven
        (by omega) a ha 5 hfinish
      obtain ⟨v,hv,hlen,_⟩ := LX.LiftedScan.delete_adjacent_descent (by omega) p
        (displacement p a) w hw hzero i (reflection_neighbor_descent hn4 p r hp a i hcross)
      exact ⟨v,hv,by norm_num at hprice; omega⟩
    · have hodd : n=2*(n/2)+1 := by omega
      obtain ⟨a,ha,hforward,hcorner,hcross⟩ := odd_reflection_neighbor_anchor p r hp (n/2) hodd (by omega) i
      have hheight : height p a=n/2 := by
        have hh := complete_height p (reflection_complete_odd p r hp (n/2) hodd) a
        omega
      obtain ⟨w,hw,hzero,hprice⟩ := odd_forward_anchor_zero_word p a 10
        (global_minimum_majorized (reflection_global_minimum p r hp a))
        (by omega) (by omega) ha (by omega) hcorner
      obtain ⟨v,hv,hlen,_⟩ := LX.LiftedScan.delete_adjacent_descent (by omega) p
        (displacement p a) w hw hzero i (reflection_neighbor_descent hn4 p r hp a i hcross)
      exact ⟨v,hv,by norm_num at hprice; omega⟩

#print axioms reflection_two_anchor_choice
#print axioms reflection_neighbor_descent
#print axioms even_reflection_neighbor_anchor
#print axioms odd_reflection_neighbor_anchor
#print axioms reflection_neighbor_upper_word
end LX.AnchoredPhases
