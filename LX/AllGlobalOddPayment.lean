import LX.AllGlobalOddGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Away from the head offset and the two terminal regions, a global
phase of an unpaid odd input must have the larger height. -/
theorem odd_unpaid_middle_phase_high {p : State n} {a b : Fin n}
    (ha : GlobalMinimum p a) (hb : GlobalMinimum p b)
    (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1) (hm : 3 ≤ m)
    (hR : inversions (displacement p a)+R=m*m)
    (hlo : m-R-30 < (p b-b).val) (hhi : (p b-b).val ≤ n-11)
    (hhead : p 0 ≠ p b-b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    height p b=m := by
  have hcases := odd_unpaid_global_height_cases hn4 m hn hb hunpaid
  by_contra hnot
  have hlow : height p b+1=m := by omega
  obtain ⟨c,hc,hraw,hlast⟩ := last_same_offset_anchor hb
  have hcHeight : height p c=height p b := by
    have h := reanchor_height p b c
    have hz : cyclicOffset p b c=0 := by unfold cyclicOffset; rw [hraw,sub_self]
    rw [hz] at h
    norm_num [belowCount] at h
    omega
  have hcR : anchorReserve p c+1=R := by
    have hI : inversions (displacement p c)=inversions (displacement p a) :=
      Nat.le_antisymm (global_minimum_exchanges hc a) (global_minimum_exchanges ha c)
    unfold anchorReserve
    rw [hI]
    have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
    have hch : (height p c : ℤ)+1=m := by omega
    have hR' : (inversions (displacement p a) : ℤ)+(R : ℤ)=(m : ℤ)*(m : ℤ) := by exact_mod_cast hR
    nlinarith
  have hne : p c-c ≠ 0 := by
    intro he
    rw [← hraw,he,Fin.val_zero] at hlo
    omega
  have hgap : (c-p c).val=n-(p b-b).val := by
    rw [show c-p c= -(p c-c) by ring]
    rw [Fin.val_neg,ite_eq_right hne,hraw]
  have hfinish : 11 ≤ c.val+(-p c).val := by
    have hle : (c-p c).val ≤ c.val+(-p c).val := by
      rw [sub_eq_add_neg,Fin.val_add]
      exact Nat.mod_le _ _
    rw [hgap] at hle
    have := (p b-b).isLt
    omega
  have hbound := odd_unpaid_lower_raw_bound hc (by omega) (by omega)
    (fun he => hhead (he.trans hraw)) hlast hfinish hunpaid
  rw [hraw] at hbound
  omega

/-- In the all-global family, the central interval has no holes except
near the head offset. Every remaining residue is realized by a backward
arrow of maximal height. -/
theorem odd_all_global_middle_backward {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1)
    (hm : 31 ≤ m) (hall : ∀ b : Fin n,GlobalMinimum p b)
    (hR : inversions (displacement p a)+R=m*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32)
    (k : ℕ) (hklo : m-R-30+3 ≤ k) (hkhi : k ≤ n-13)
    (hfar : k ∉ Finset.Icc ((p 0).val-3) ((p 0).val+3)) :
    ∃ i : Fin n,i ∈ descendingPositions p ∧ (p i-i).val=k := by
  have hkn : k < n := by omega
  have hkv : (k : Fin n).val=k := by simp [Nat.mod_eq_of_lt hkn]
  have hfar' : ¬((p 0).val-3 ≤ k ∧ k ≤ (p 0).val+3) := by simpa only [Finset.mem_Icc] using hfar
  obtain ⟨b,hnear,hmin⟩ := odd_all_global_predecessor hn4 p m hn hall hunpaid (k : Fin n)
  have hble : p b-b ≤ (k : Fin n) := by
    by_contra hnot
    have hlt : (k : Fin n) < p b-b := lt_of_not_ge hnot
    rw [Fin.coe_sub_iff_lt.mpr hlt,hkv] at hnear
    have := (p b-b).isLt
    omega
  have hnear' : k-(p b-b).val ≤ 2 := by rwa [Fin.coe_sub_iff_le.mpr hble,hkv] at hnear
  have hbval : (p b-b).val ≤ k := by simpa only [Fin.le_def,hkv] using hble
  have hbhead : p 0 ≠ p b-b := by
    intro he
    have hv := congrArg Fin.val he
    omega
  have hbh : height p b=m := odd_unpaid_middle_phase_high ha (hall b) hn4 m R hn (by omega)
    hR (by omega) (by omega) hbhead hunpaid
  have he : (p b-b).val=k := by
    by_contra hnot
    obtain ⟨c,t,ht,ht3,htn,hoff,hsize⟩ := odd_all_global_next_gap hn4 p m hn hall hunpaid b
    have hbf := odd_unpaid_all_global_fixed_cases hn4 p m hn hall hunpaid b
    have hcf := odd_unpaid_all_global_fixed_cases hn4 p m hn hall hunpaid c
    have ht2 : t ≤ 2 := by omega
    have htv : (t : Fin n).val=t := by simp [Nat.mod_eq_of_lt htn]
    have hgap : ((k : Fin n)-(p b-b)).val=k-(p b-b).val := by rw [Fin.coe_sub_iff_le.mpr hble,hkv]
    have hgt : k-(p b-b).val < t := by
      by_contra hnot'
      have htle : (t : Fin n) ≤ (k : Fin n)-(p b-b) := by
        change (t : Fin n).val ≤ _
        rw [htv,hgap]
        omega
      have heq : (k : Fin n)-(p c-c)=(k : Fin n)-(p b-b)-(t : Fin n) := by rw [hoff]; ring
      have hh := hmin c
      rw [heq,Fin.coe_sub_iff_le.mpr htle,htv] at hh
      omega
    have htEq : t=2 := by omega
    have hbEq : (p b-b).val+1=k := by omega
    have hcval : (p c-c).val=k+1 := by
      rw [hoff,Fin.val_add,htv,Nat.mod_eq_of_lt (by omega)]
      omega
    have hchead : p 0 ≠ p c-c := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    have hch : height p c=m := odd_unpaid_middle_phase_high ha (hall c) hn4 m R hn (by omega)
      hR (by omega) (by omega) hchead hunpaid
    omega
  refine ⟨b,?_,he⟩
  rw [mem_descendingPositions]
  by_contra hnot
  have hforward : b.val < (p b).val := by
    by_contra hnot'
    have hbfix : p b=b := Fin.ext (by omega)
    rw [hbfix,sub_self,Fin.val_zero] at he
    omega
  have hb0 : 0 < b.val := by
    by_contra hnot'
    have hz : b=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    exact hbhead (by simp [hz])
  have hne : p b ≠ 0 := by intro heq; rw [heq,Fin.val_zero] at hforward; omega
  have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hne]
  have hspan : (p b).val-b.val=k := by
    rwa [Fin.coe_sub_iff_le.mpr (show b ≤ p b from Nat.le_of_lt hforward)] at he
  have hfinish : 5 ≤ b.val+(-p b).val := by rw [hneg]; have := (p b).isLt; omega
  have hbound := odd_unpaid_higher_forward_span (hall b) hn4 (by omega) hb0 hforward hfinish hunpaid
  have hbR : anchorReserve p b=R := by
    have hI : inversions (displacement p b)=inversions (displacement p a) :=
      Nat.le_antisymm (global_minimum_exchanges (hall b) a) (global_minimum_exchanges ha b)
    unfold anchorReserve
    rw [hbh,hI]
    have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
    have hR' : (inversions (displacement p a) : ℤ)+(R : ℤ)=(m : ℤ)*(m : ℤ) := by exact_mod_cast hR
    nlinarith
  rw [hbh,hbR] at hbound
  omega

#print axioms odd_unpaid_middle_phase_high
#print axioms odd_all_global_middle_backward

/-- The entire odd all-global-anchor family is paid. The proof counts a
central interval of distinct backward arrows and contradicts the actual
ordinary descending-position bound; no phase-count conjecture is used. -/
theorem odd_all_anchors_global_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1) (hall : ∀ a : Fin n,GlobalMinimum p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  classical
  by_contra hunpaid
  let R := m*m-inversions (displacement p 0)
  have hI : inversions (displacement p 0) ≤ m*m := by
    have hc := (candidate_price_components p 0).1
    have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
    have hi : (inversions (displacement p 0) : ℤ) ≤ (m : ℤ)*(m : ℤ) := by
      nlinarith [sq_nonneg ((height p 0 : ℤ)-(m : ℤ))]
    exact_mod_cast hi
  have hR : inversions (displacement p 0)+R=m*m := by dsimp [R]; omega
  have hlo := odd_unpaid_reserve_at_least_two hn4 m hn (hall 0) hunpaid
  have hhi := odd_unpaid_reserve_upper hn4 m hn (hall 0) hunpaid
  have hR' : (inversions (displacement p 0) : ℤ)+(R : ℤ)=(m : ℤ)*(m : ℤ) := by exact_mod_cast hR
  have hm : 31 ≤ m := by nlinarith
  let S := m-R-30
  let A := Finset.Icc (S+3) (n-13)
  let D := Finset.Icc ((p 0).val-3) ((p 0).val+3)
  let C := A \ D
  have hsub : C ⊆ (descendingPositions p).image (fun i => (p i-i).val) := by
    intro k hk
    have hkA := (Finset.mem_sdiff.mp hk).1
    have hkD := (Finset.mem_sdiff.mp hk).2
    have hkb := Finset.mem_Icc.mp hkA
    obtain ⟨i,hi,hraw⟩ := odd_all_global_middle_backward (hall 0) hn4 m R hn hm hall hR hunpaid k
      hkb.1 hkb.2 hkD
    exact Finset.mem_image.mpr ⟨i,hi,hraw⟩
  have hsmall : C.card ≤ m+1 :=
    ((Finset.card_le_card hsub).trans Finset.card_image_le).trans
      (odd_all_global_descending_bound hn4 p m hn hall hunpaid)
  have hD : D.card ≤ 7 := by dsimp [D]; rw [Nat.card_Icc]; omega
  have hA : A.card=(n-13)+1-(S+3) := by dsimp [A]; rw [Nat.card_Icc]
  have hcover : A.card ≤ C.card+D.card := Finset.card_le_card_sdiff_add_card
  dsimp [S] at hA
  omega

/-- After paying the all-global family, every unpaid odd input has an
actual lower global minimum with at most two fixed positions. -/
theorem odd_unpaid_lower_small_fixed (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card ≤ 2 := by
  rcases odd_unpaid_small_fixed_or_all_global hn4 p m hn hunpaid with h | h
  · exact h
  · exact False.elim (hunpaid (odd_all_anchors_global_upper_word hn4 p m hn h))

/-- In particular, the lower three-fixed global alternative is paid
uniformly, independently of the dimension-wide reserve. -/
theorem odd_all_lower_minima_three_fixed_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hthree : ∀ a : Fin n,GlobalMinimum p a → height p a+1=m →
      (fixedPositions (permutation p a)).card=3) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  obtain ⟨a,ha,hh,hf⟩ := odd_unpaid_lower_small_fixed hn4 p m hn hunpaid
  have he := hthree a ha hh
  omega

#print axioms odd_all_anchors_global_upper_word
#print axioms odd_unpaid_lower_small_fixed
#print axioms odd_all_lower_minima_three_fixed_upper_word
end LX.AnchoredPhases
