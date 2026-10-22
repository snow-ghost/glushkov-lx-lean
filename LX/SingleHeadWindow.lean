import LX.MinimumGapPhases

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem single_head_low_offset_count (p : State n) (a : Fin n) (R : ℕ) (E : Finset ℕ)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (hh : 2 ≤ height p a) (hn : n=2*height p a+2 ∨ n=2*height p a+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14)
    (hcorner : ∀ b,height p b=height p a → (b-p b).val ∉ E → (b-p b).val < 2*R+3 →
      ∃ w : List Letter,p*eval w=1 ∧ 4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14) :
    (minimumHeightOffsets p (height p a)).card ≤
      ((descendingPositions p).filter fun i => height p i=height p a).card+E.card+(if height p 0=height p a then 1 else 0) := by
  classical
  let B := E.image (fun k : ℕ => -(k : Fin n))
  let H : Finset (Fin n) := if height p 0=height p a then {p 0} else ∅
  let U := B ∪ H
  let V := ((descendingPositions p).filter fun i => height p i=height p a).image (fun i => p i-i)
  have hsub : minimumHeightOffsets p (height p a) ⊆ V ∪ U := by
    intro t ht
    by_cases hbad : t ∈ U
    · exact Finset.mem_union_right _ hbad
    obtain ⟨b,hb,hbt⟩ := Finset.mem_image.mp ht
    have hbh := (Finset.mem_filter.mp hb).2
    obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    have hcHeight : height p c=height p a := hch.trans hbh
    by_cases hback : (p c).val < c.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c,Finset.mem_filter.mpr
        ⟨(mem_descendingPositions _ _).mpr hback,hcHeight⟩,hct⟩
    have hgap : (c-p c).val ∉ E := by
      intro he
      apply hbad
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      refine ⟨(c-p c).val,he,?_⟩
      simp only [Fin.cast_val_eq_self]
      rw [← hct]
      ring
    have hgapK : 2*R+3 ≤ (c-p c).val := by
      by_contra hnot
      exact hunpaid (hcorner c hcHeight hgap (by omega))
    have hhead : p 0 ≠ p c-c := by
      intro he
      apply hbad
      have ht0 : t=p 0 := hct.symm.trans he.symm
      have hperm : permutation p 0=permutation p c := by
        apply Equiv.ext
        intro i
        change p i+(0-p 0)=p i+(c-p c)
        linear_combination -he
      have hheight : height p 0=height p a :=
        (congrArg (fun q : State n => (descendingPositions q).card) hperm).trans hcHeight
      simp [U,H,hheight,ht0]
    have hforward : c.val < (p c).val := by
      by_contra hnot
      have he : p c=c := Fin.ext (by omega)
      rw [he,sub_self,Fin.val_zero] at hgapK
      omega
    have hfinish : 2*R+3 ≤ c.val+(-p c).val := by
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hc' := rank_peak_next_depth p a R hR c (by omega)
    have hc : depthCount (displacement p c) (height p c-1) ≤ 2*R+3 := by omega
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
  have hV : V.card ≤ ((descendingPositions p).filter fun i => height p i=height p a).card := Finset.card_image_le
  have hB : B.card ≤ E.card := Finset.card_image_le
  have hH : H.card=(if height p 0=height p a then 1 else 0) := by
    dsimp [H]
    split_ifs <;> simp
  have hU : U.card ≤ E.card+(if height p 0=height p a then 1 else 0) := by
    have hc := Finset.card_union_le B H
    rw [hH] at hc
    change U.card ≤ _ at hc
    omega
  omega

theorem single_head_terminal_low_excluded (p : State n) (m R e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 9 < n)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14)
    (b : Fin n) (hglo : R ≤ (b-p b).val) (hghi : (b-p b).val ≤ e*m+12) :
    height p b+1 ≠ m := by
  intro hh
  have hr := anchor_reserve_nonneg p b
  interval_cases e
  · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega)
      (by have := hF b; omega)
    exact hunpaid ⟨w,hw,by omega⟩
  · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega)
      (by have := hF b; omega)
    exact hunpaid ⟨w,hw,by omega⟩

/-- Every threshold in the terminal interval is either high, the head, or
an actual backward arrow of the middle height. Missing occupied offsets
cannot be silently discarded: surplus one forces a paid next minimum. -/
theorem single_head_terminal_threshold (p : State n) (a : Fin n) (m R g e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 9 < n) (hupper : e*m+12 < n) (ha : height p a+1=m)
    (hmin : ∀ b,height p a ≤ height p b)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hdepth : ∀ b,height p b=m → depthCount (displacement p b) (height p b-1) ≤ 2*R+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*14)
    (hglo : 2*R+1 ≤ g) (hghi : g ≤ e*m+12) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      (-(g : Fin n)=p 0 ∧ height p 0=m) ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c= -(g : Fin n) := by
  let t : Fin n := -(g : Fin n)-(p a-a)
  have hgn : g < n := by interval_cases e <;> omega
  have hgv : (g : Fin n).val=g := Nat.mod_eq_of_lt hgn
  by_cases hhigh : 2 ≤ rankSurplus p a t.val
  · exact Or.inl hhigh
  have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
  have hnonzero : rankSurplus p a t.val ≠ 0 := by
    intro hz
    obtain ⟨b,hb,hh⟩ := zero_surplus_anchor p a hmin t hz
    have hraw : p b-b= -(g : Fin n) := by
      unfold cyclicOffset at hb
      dsimp only [t] at hb
      linear_combination hb
    have hgap : (b-p b).val=g := by
      have he : b-p b=(g : Fin n) := by linear_combination -hraw
      rw [he,hgv]
    exact single_head_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b (by omega) (by omega) (by omega)
  have hone : rankSurplus p a t.val=1 := by omega
  by_cases hhead : -(g : Fin n)=p 0
  · refine Or.inr (Or.inl ⟨hhead,?_⟩)
    have hoff : cyclicOffset p a 0=t := by
      dsimp [cyclicOffset,t]
      rw [hhead,sub_zero]
    have hh0 := reanchor_height p a 0
    rw [hoff] at hh0
    unfold rankSurplus at hone
    omega
  rcases rank_one_occupied_or_next_minimum p a t hmin hone with ⟨b,hb,hbHeight⟩ | ⟨b,hb,hbHeight⟩
  · have hraw : p b-b= -(g : Fin n) := by
      unfold cyclicOffset at hb
      dsimp only [t] at hb
      linear_combination hb
    obtain ⟨c,hcb,hch,_,hlast⟩ := last_offset_source p b
    have hcr : p c-c= -(g : Fin n) := hcb.trans hraw
    have hgap : (c-p c).val=g := by
      have he : c-p c=(g : Fin n) := by linear_combination -hcr
      rw [he,hgv]
    have hcHeight : height p c=m := by omega
    refine Or.inr (Or.inr ⟨c,?_,hcHeight,hcr⟩)
    rw [mem_descendingPositions]
    by_contra hnot
    have hforward : c.val < (p c).val := by
      by_contra hnot'
      have he : p c=c := Fin.ext (by omega)
      rw [he,sub_self,Fin.val_zero] at hgap
      omega
    have hcount : depthCount (displacement p c) (height p c-1) ≤ c.val+(-p c).val := by
      have hc := hdepth c hcHeight
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    have hg' : (c-p c).val=n+c.val-(p c).val :=
      Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)
    have hfinish : c.val+(-p c).val ≤ e*m+12 := by rw [hneg]; omega
    have hr := anchor_reserve_nonneg p c
    interval_cases e
    · obtain ⟨w,hw,hprice⟩ := even_higher_anchor_reserve_price p c (by omega) (by omega)
        (fun he => hhead (hcr.symm.trans he.symm)) hlast hcount
      exact hunpaid ⟨w,hw,by omega⟩
    · obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p c (by omega) (by omega)
        (fun he => hhead (hcr.symm.trans he.symm)) hlast hcount
      exact hunpaid ⟨w,hw,by omega⟩
  · have hraw : p b-b= -((g-1 : ℕ) : Fin n) := by
      unfold cyclicOffset at hb
      dsimp only [t] at hb
      rw [Nat.cast_sub (by omega : 1 ≤ g),Nat.cast_one]
      linear_combination hb
    have hgap : (b-p b).val=g-1 := by
      have he : b-p b=((g-1 : ℕ) : Fin n) := by linear_combination -hraw
      rw [he]
      exact Nat.mod_eq_of_lt (by omega)
    exact False.elim (single_head_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b
      (by omega) (by omega) (by omega))


#print axioms single_head_low_offset_count
#print axioms single_head_terminal_threshold
end LX.AnchoredPhases
