import LX.OddForwardPhaseCount

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- An eligible lower global phase of an unpaid odd input must have a
long backward displacement. This conclusion comes from an actual word. -/
theorem odd_unpaid_lower_raw_bound {p : State n} {b : Fin n}
    (hb : GlobalMinimum p b) (hn : n=2*height p b+3) (hh : 2 ≤ height p b)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hfinish : 11 ≤ b.val+(-p b).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    0 < (p b-b).val ∧
      ((p b-b).val : ℤ)+height p b+anchorReserve p b+33 ≤ n := by
  have hc := next_depth_count (is_lift p b) (global_minimum_majorized hb)
    (height p b) (by omega) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i)
  have hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val := by omega
  obtain ⟨w,hw,hprice⟩ := odd_lower_anchor_reserve_price p b hh hn hhead hlast hcount
  have hnot : ¬4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := fun hp => hunpaid ⟨w,hw,hp⟩
  have hlarge : (n : ℤ)+height p b+anchorReserve p b+33 ≤
      (b.val : ℤ)+((-p b).val : ℤ) := by omega
  have hr := anchor_reserve_nonneg p b
  have hne : p b ≠ 0 := by
    intro he
    rw [he,neg_zero,Fin.val_zero,Nat.cast_zero,add_zero] at hlarge
    have := b.isLt
    omega
  have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hne]
  rw [hneg,Nat.cast_sub (Nat.le_of_lt (p b).isLt)] at hlarge
  have hback : p b < b := by change (p b).val < b.val; omega
  rw [Fin.coe_sub_iff_lt.mpr hback]
  have hbi := b.isLt
  have hpi := (p b).isLt
  constructor <;> omega

noncomputable def lowerMinimumOffsets (p : State n) (m : ℕ) : Finset (Fin n) := by
  classical
  exact (Finset.univ.filter fun i => GlobalMinimum p i ∧ height p i+1=m).image (fun i => p i-i)

/-- Distinct lower global offsets of an unpaid odd input fit in one short
positive interval, eleven terminal residues, and the original head offset. -/
theorem odd_unpaid_lower_offset_count {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1)
    (hR : inversions (displacement p a)+R=m*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (lowerMinimumOffsets p m).card ≤ (m-R-30)+12 := by
  classical
  have hupper := odd_unpaid_reserve_upper hn4 m hn ha hunpaid
  have hR' : (inversions (displacement p a) : ℤ)+(R : ℤ)=(m : ℤ)*(m : ℤ) := by exact_mod_cast hR
  have hm : 3 ≤ m := by nlinarith
  let A := (Finset.Icc 1 (m-R-30)).image (fun j : ℕ => (j : Fin n))
  let B := (Finset.range 11).image (fun j : ℕ => -(j : Fin n))
  let U := (A ∪ B) ∪ {p 0}
  have hsub : lowerMinimumOffsets p m ⊆ U := by
    intro t ht
    obtain ⟨b,hb,ht⟩ := Finset.mem_image.mp ht
    have hb' := (Finset.mem_filter.mp hb).2
    obtain ⟨c,hc,hraw,hlast⟩ := last_same_offset_anchor hb'.1
    have hcHeight : height p c=height p b := by
      have hheight := reanchor_height p b c
      have hz : cyclicOffset p b c=0 := by unfold cyclicOffset; rw [hraw,sub_self]
      rw [hz] at hheight
      norm_num [belowCount] at hheight
      omega
    have hct : p c-c=t := hraw.trans ht
    have hcR : anchorReserve p c+1=R := by
      have hI : inversions (displacement p c)=inversions (displacement p a) :=
        Nat.le_antisymm (global_minimum_exchanges hc a) (global_minimum_exchanges ha c)
      unfold anchorReserve
      rw [hI]
      have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
      have hch : (height p c : ℤ)+1=m := by omega
      nlinarith
    by_cases hhead : p 0=p c-c
    · have ht0 : t=p 0 := hct.symm.trans hhead.symm
      simp [U,ht0]
    · by_cases hfinish : 11 ≤ c.val+(-p c).val
      · have hbound := odd_unpaid_lower_raw_bound hc (by omega) (by omega) hhead hlast hfinish hunpaid
        have hval : (p c-c).val ≤ m-R-30 := by omega
        have hmA : t ∈ A := by
          apply Finset.mem_image.mpr
          exact ⟨(p c-c).val,Finset.mem_Icc.mpr ⟨hbound.1,hval⟩,by simpa using hct⟩
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hmA)
      · have hgap : (c-p c).val < 11 := by
          have he : c-p c=c+(-p c) := sub_eq_add_neg _ _
          rw [he,Fin.val_add]
          exact lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
        have hmB : t ∈ B := by
          apply Finset.mem_image.mpr
          refine ⟨(c-p c).val,Finset.mem_range.mpr hgap,?_⟩
          simp only [Fin.cast_val_eq_self]
          rw [← hct]
          ring
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hmB)
  have hc := Finset.card_le_card hsub
  have hA : A.card ≤ m-R-30 := by
    have hc := Finset.card_image_le (s := Finset.Icc 1 (m-R-30)) (f := fun j : ℕ => (j : Fin n))
    simpa [A,Nat.card_Icc] using hc
  have hB : B.card ≤ 11 := by
    exact (Finset.card_image_le).trans (by rw [Finset.card_range])
  have hU := Finset.card_union_le (A ∪ B) {p 0}
  have hAB := Finset.card_union_le A B
  change U.card ≤ _ at hU
  simp only [Finset.card_singleton] at hU
  omega

/-- Enough lower minimum phases force a paid original input, without
requiring an unproved lower bound on the total number of minimum phases. -/
theorem odd_many_lower_minima_upper_word {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn4 : 4 ≤ n) (m R : ℕ) (hn : n=2*m+1)
    (hR : inversions (displacement p a)+R=m*m)
    (hcount : (m-R-30)+12 < (lowerMinimumOffsets p m).card) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  by_contra hunpaid
  have hc := odd_unpaid_lower_offset_count ha hn4 m R hn hR hunpaid
  omega

#print axioms odd_unpaid_lower_raw_bound
#print axioms odd_unpaid_lower_offset_count
#print axioms odd_many_lower_minima_upper_word
end LX.AnchoredPhases
