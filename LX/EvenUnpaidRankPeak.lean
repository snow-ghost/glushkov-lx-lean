import LX.BoundedHeightGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Minimum-height offsets outside a bounded terminal region must be
represented by backward arrows, even when the other heights vary. -/
theorem unpaid_lower_height_offset_low_arrow_count (p : State n) (h H F : ℕ)
    (hall : ∀ a,h ≤ height p a ∧ height p a ≤ h+H)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 2 ≤ h) (hn : n=2*h+2 ∨ n=2*h+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (minimumHeightOffsets p h).card ≤
      ((descendingPositions p).filter fun i => height p i=h).card+H+2*F+2 := by
  classical
  let K := H+2*F+1
  let B := (Finset.range K).image (fun k : ℕ => -(k : Fin n))
  let U := B ∪ {p 0}
  let V := ((descendingPositions p).filter fun i => height p i=h).image (fun i => p i-i)
  have hsub : minimumHeightOffsets p h ⊆ V ∪ U := by
    intro t ht
    by_cases hbad : t ∈ U
    · exact Finset.mem_union_right _ hbad
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp ht
    have hbh := (Finset.mem_filter.mp hb).2
    obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    have hcHeight : height p c=h := hch.trans hbh
    by_cases hback : (p c).val < c.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr
        ⟨(mem_descendingPositions _ _).mpr hback,hcHeight⟩,hct⟩
    have hgap : K ≤ (c-p c).val := by
      by_contra hnot
      apply hbad
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(c-p c).val,Finset.mem_range.mpr (by omega),?_⟩
      simp only [Fin.cast_val_eq_self]
      rw [← hct]
      ring
    have hhead : p 0 ≠ p c-c := by
      intro he
      apply hbad
      have ht0 : t=p 0 := hct.symm.trans he.symm
      simp [U,ht0]
    have hforward : c.val < (p c).val := by
      by_contra hnot
      have he : p c=c := Fin.ext (by omega)
      rw [he,sub_self,Fin.val_zero] at hgap
      dsimp [K] at hgap
      omega
    have hfinish : K ≤ c.val+(-p c).val := by
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hc := bounded_height_next_depth p h H F hall hF c (by omega)
    have hword : ∃ w : List Letter,p*eval w=1 ∧
        4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+
          4*((c.val : ℤ)+((-p c).val : ℤ)-(n : ℤ)+1-anchorReserve p c) := by
      rcases hn with hn | hn
      · obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p c (by omega) (by omega)
          hhead hlast (hc.trans hfinish)
        exact ⟨w,hw,hprice.le⟩
      · obtain ⟨w,hw,hprice⟩ := odd_lower_anchor_reserve_price p c (by omega) (by omega)
          hhead hlast (hc.trans hfinish)
        refine ⟨w,hw,?_⟩
        have : (0 : ℤ) ≤ height p c := by positivity
        linarith
    obtain ⟨w,hw,hprice⟩ := hword
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    rw [hneg,Nat.cast_sub (Nat.le_of_lt (p c).isLt)] at hprice
    have hr := anchor_reserve_nonneg p c
    exact False.elim (hunpaid ⟨w,hw,by omega⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V U)
  have hV : V.card ≤ ((descendingPositions p).filter fun i => height p i=h).card := Finset.card_image_le
  have hB : B.card ≤ K := (Finset.card_image_le).trans (by rw [Finset.card_range])
  have hU : U.card ≤ K+1 := by
    have hc := Finset.card_union_le B {p 0}
    simp only [Finset.card_singleton] at hc
    change U.card ≤ _ at hc
    omega
  dsimp [K] at *
  omega

theorem even_unpaid_minimum_offset_low_arrow_count (p : State n) (h H F : ℕ)
    (hall : ∀ a,h ≤ height p a ∧ height p a ≤ h+H)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (minimumHeightOffsets p h).card ≤
      ((descendingPositions p).filter fun i => height p i=h).card+H+2*F+2 :=
  unpaid_lower_height_offset_low_arrow_count p h H F hall hF hh (Or.inl hn) hunpaid

theorem even_unpaid_minimum_offset_count (p : State n) (h H F : ℕ)
    (hall : ∀ a,h ≤ height p a ∧ height p a ≤ h+H)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (minimumHeightOffsets p h).card ≤ (descendingPositions p).card+H+2*F+2 := by
  have hc := even_unpaid_minimum_offset_low_arrow_count p h H F hall hF hh hn hunpaid
  have hf := Finset.card_filter_le (s := descendingPositions p) (fun i => height p i=h)
  omega

/-- Every rank peak of an unpaid even input is at most eleven. This closes
the unbounded height-range issue for the original permutation. -/
theorem even_unpaid_rank_peak_le_eleven (p : State n) (a r : Fin n) (R : ℕ)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+2)
    (hh : 2 ≤ height p a) (hpeak : rankSurplus p a r.val=R)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) : R ≤ 11 := by
  have hb := rank_peak_anchor_bounds p a R hmin hR
  have hlo := even_minimum_anchor_count_with_peak p a r R hmin hn hpeak
  rw [zero_surplus_count_eq_minimum_offsets p a hmin] at hlo
  have hc := even_unpaid_minimum_offset_count p (height p a) R (R+1) hb.1 hb.2 hh hn hunpaid
  have hd := bounded_height_descending_count p (height p a) R (R+1) hb.1 hb.2
  have hci : ((minimumHeightOffsets p (height p a)).card : ℤ) ≤
      (height p a : ℤ)+5*(R : ℤ)+4 := by omega
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  by_contra hnot
  have hp := mul_nonneg (show 0 ≤ (R : ℤ)-12 by omega) (show 0 ≤ (R : ℤ)+1 by positivity)
  nlinarith

/-- Uniform actual geometry for every still-unpaid even input. The constants
are independent of n and of the exchange reserve. -/
theorem even_unpaid_bounded_rank_geometry (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (∀ t : Fin n,0 ≤ rankSurplus p a t.val ∧ rankSurplus p a t.val ≤ 11) ∧
      (∀ b,height p a ≤ height p b ∧ height p b ≤ height p a+11) ∧
      (∀ b,(fixedPositions (permutation p b)).card ≤ 12) ∧
      (∀ b,depthCount (displacement p b) (height p b-1) ≤ 36) ∧
      (descendingPositions p).card ≤ m+21 ∧
      (∀ r : Fin n,∃ b : Fin n,(r-(p b-b)).val < 23) ∧
      (minimumHeightOffsets p (height p a)).card ≤ m+58 ∧
      (Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card ≤ 58 := by
  classical
  have hn22 : 22 ≤ n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  obtain ⟨a,ha⟩ := exists_global_minimum p
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  have hmin := even_unpaid_global_minimum_height p m hn hn4 hunpaid a ha
  obtain ⟨r,_,hr⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun t => rankSurplus p a t.val) ⟨0,Finset.mem_univ _⟩
  have hr0 := rank_surplus_nonnegative p a hmin r.val (Nat.le_of_lt r.isLt)
  let R := (rankSurplus p a r.val).toNat
  have hpeak : rankSurplus p a r.val=R := by dsimp [R]; rw [Int.toNat_of_nonneg hr0]
  have hR (t : Fin n) : rankSurplus p a t.val ≤ R := by
    rw [← hpeak]
    exact hr t (Finset.mem_univ _)
  have hR11 := even_unpaid_rank_peak_le_eleven p a r R hmin (by omega) (by omega) hpeak hR hunpaid
  have hbound (t : Fin n) : rankSurplus p a t.val ≤ 11 := by have := hR t; omega
  have hb := rank_peak_anchor_bounds p a 11 hmin (by simpa using hbound)
  have hdepth (b : Fin n) : depthCount (displacement p b) (height p b-1) ≤ 36 := by
    have ht := bounded_height_next_depth p (height p a) 11 12 hb.1 hb.2 b
      (by have := hmin b; omega)
    exact ht
  have hdesc : (descendingPositions p).card ≤ m+21 := by
    have ht := bounded_height_descending_count p (height p a) 11 12 hb.1 hb.2
    omega
  have hcount : (minimumHeightOffsets p (height p a)).card ≤ m+58 := by
    have ht := even_unpaid_minimum_offset_count p (height p a) 11 12 hb.1 hb.2 (by omega) (by omega) hunpaid
    omega
  have hhigh : (Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card ≤ 58 := by
    have hp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)+
        (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0) ≤
          ∑ t : Fin n,rankSurplus p a t.val := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t _
      have ht := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
      split_ifs <;> omega
    have hcomp : (∑ t : Fin n,if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
        (n : ℤ)-(Finset.univ.filter (fun t : Fin n => rankSurplus p a t.val=0)).card := by
      have he (t : Fin n) : (if rankSurplus p a t.val=0 then (0 : ℤ) else 1)=
          1-(if rankSurplus p a t.val=0 then 1 else 0) := by split_ifs <;> norm_num
      simp_rw [he]
      simp [Finset.sum_sub_distrib]
    rw [hcomp,zero_surplus_count_eq_minimum_offsets p a hmin] at hp
    have hhighSum : (∑ t : Fin n,if 2 ≤ rankSurplus p a t.val then (1 : ℤ) else 0)=
        ((Finset.univ.filter (fun t : Fin n => 2 ≤ rankSurplus p a t.val)).card : ℤ) := by simp
    rw [hhighSum] at hp
    have hs := rank_surplus_sum p a
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by omega
    have hs' : (∑ t : Fin n,rankSurplus p a t.val : ℤ)=m := by nlinarith
    rw [hs'] at hp
    omega
  exact ⟨a,ha,hh,(fun t => ⟨rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt),hbound t⟩),
    hb.1,hb.2,hdepth,hdesc,
    (fun r => bounded_height_predecessor p (height p a) 11 12 hb.1 hb.2 (by omega) r),hcount,hhigh⟩

#print axioms even_unpaid_minimum_offset_count
#print axioms even_unpaid_minimum_offset_low_arrow_count
#print axioms even_unpaid_rank_peak_le_eleven
#print axioms even_unpaid_bounded_rank_geometry
end LX.AnchoredPhases
