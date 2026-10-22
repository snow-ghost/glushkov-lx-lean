import LX.ConstantHeightEvenGeometry

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- At the remaining even height, a short cyclic gap absorbs the initial
cursor whenever it is at least the fixed-fiber count minus one. -/
theorem even_few_fixed_small_gap_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hh : 0 < height p a)
    (hf : (fixedPositions (permutation p a)).card ≤ (a-p a).val+1)
    (hgap : (a-p a).val ≤ 30) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  obtain ⟨r,hr,hhead⟩ := exists_head_with_count (displacement p a) (height p a) hh
  rw [top_depth_count_eq_fixed] at hr
  let T := height p a*(n-1)+(a-p a).val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)=0 := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+((a-p a).val : ℤ) := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have hg : ((a-p a).val : ℤ) ≤ 30 := by exact_mod_cast hgap
  exact ⟨w,hw,by nlinarith⟩

/-- The small-fiber branch selects an actual phase near the terminal cursor;
no assumed phase, reserve or energy minimum is supplied. -/
theorem even_constant_height_small_fibers_word (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hsmall : F ≤ 9) (hn22 : 22 ≤ n) (hn : n=2*h+2) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  let r : Fin n := -(F : Fin n)
  obtain ⟨b,hb⟩ := constant_height_predecessor p h F hall hF (by omega) r
  have hFv : (F : Fin n).val=F := by simp [Nat.mod_eq_of_lt (by omega : F < n)]
  have he : b-p b=(F : Fin n)+(r-(p b-b)) := by dsimp only [r]; ring
  have hgap : (b-p b).val=F+(r-(p b-b)).val := by
    rw [he,Fin.val_add,hFv,Nat.mod_eq_of_lt (by omega)]
  apply even_few_fixed_small_gap_word p b (by rw [hall]; omega) (by rw [hall]; omega)
  · have hf := hF b
    omega
  · omega

/-- If no paid word exists, each nonterminal, nonhead offset must be
represented by an ordinary backward arrow. Otherwise its last occurrence
gives a forward aligned word with the required price. -/
theorem even_constant_height_unpaid_raw_count (p : State n) (h F : ℕ)
    (hall : ∀ a,height p a=h)
    (hF : ∀ a,(fixedPositions (permutation p a)).card ≤ F)
    (hh : 2 ≤ h) (hn : n=2*h+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (rawOffsets p).card ≤ (descendingPositions p).card+2*F+2 := by
  classical
  let B := (Finset.range (2*F+1)).image (fun k : ℕ => -(k : Fin n))
  let U := B ∪ {p 0}
  let V := (descendingPositions p).image (fun i => p i-i)
  have hsub : rawOffsets p ⊆ V ∪ U := by
    intro t ht
    by_cases hbad : t ∈ U
    · exact Finset.mem_union_right _ hbad
    obtain ⟨b,_,hbt⟩ := Finset.mem_image.mp ht
    obtain ⟨c,hraw,_,_,hlast⟩ := last_offset_source p b
    have hct : p c-c=t := hraw.trans hbt
    by_cases hback : (p c).val < c.val
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨c,(mem_descendingPositions _ _).mpr hback,hct⟩
    have hgap : 2*F+1 ≤ (c-p c).val := by
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
      omega
    have hfinish : 2*F+1 ≤ c.val+(-p c).val := by
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hc := constant_height_next_depth p h F hall hF (by omega) c
    rw [← hall c] at hc
    obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p c (by rw [hall]; exact hh)
      (by rw [hall]; exact hn) hhead hlast (hc.trans hfinish)
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    rw [hneg,Nat.cast_sub (Nat.le_of_lt (p c).isLt)] at hprice
    have hr := anchor_reserve_nonneg p c
    exact False.elim (hunpaid ⟨w,hw,by omega⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le V U)
  have hV : V.card ≤ (descendingPositions p).card := Finset.card_image_le
  have hB : B.card ≤ 2*F+1 := (Finset.card_image_le).trans (by rw [Finset.card_range])
  have hU : U.card ≤ 2*F+2 := by
    have hc := Finset.card_union_le B {p 0}
    simp only [Finset.card_singleton] at hc
    change U.card ≤ _ at hc
    omega
  omega

/-- The entire constant-anchor-height family is paid in even size,
independently of the exchange reserve and fixed-fiber multiplicities. -/
theorem even_constant_anchor_height_upper_word (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m) (hall : ∀ a b,height p a=height p b) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  classical
  by_contra hunpaid
  have hn22 : 22 ≤ n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  obtain ⟨a,ha⟩ := exists_global_minimum p
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  let h := height p a
  have hall' (b : Fin n) : height p b=h := hall b a
  have hn' : n=2*h+2 := by dsimp [h]; omega
  obtain ⟨b,_,hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n))
    (fun b => (fixedPositions (permutation p b)).card) ⟨a,Finset.mem_univ _⟩
  let F := (fixedPositions (permutation p b)).card
  have hF (c : Fin n) : (fixedPositions (permutation p c)).card ≤ F := hmax c (Finset.mem_univ _)
  by_cases hsmall : F ≤ 9
  · exact hunpaid (even_constant_height_small_fibers_word p h F hall' hF hsmall hn22 hn')
  · have hlo := even_raw_offset_count_with_fixed p b
      (fun c => by rw [hall' b,hall' c]) (by rw [hall' b]; exact hn')
    change (n : ℤ)+((F : ℤ)-1)*(F-2) ≤ 2*((rawOffsets p).card : ℤ) at hlo
    have hhi := even_constant_height_unpaid_raw_count p h F hall' hF (by omega) hn' hunpaid
    have hdesc := constant_height_descending_bound p h F hall' hF hn'
    have hhi' : ((rawOffsets p).card : ℤ) ≤ (h : ℤ)+3*(F : ℤ)+1 := by omega
    have hnI : (n : ℤ)=2*(h : ℤ)+2 := by exact_mod_cast hn'
    have hp := mul_nonneg (show 0 ≤ (F : ℤ)-10 by omega) (show 0 ≤ (F : ℤ)+1 by positivity)
    nlinarith

/-- Any unpaid even input must have an actual phase strictly above its
minimum height; the constant-height case has no remaining exceptions. -/
theorem even_unpaid_higher_anchor (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,m ≤ height p b := by
  by_contra hnone
  have hall (a b : Fin n) : height p a=height p b := by
    have ha := even_unpaid_all_anchor_height_lower p m hn hn4 hunpaid a
    have hb := even_unpaid_all_anchor_height_lower p m hn hn4 hunpaid b
    have ha' : ¬m ≤ height p a := fun h => hnone ⟨a,h⟩
    have hb' : ¬m ≤ height p b := fun h => hnone ⟨b,h⟩
    omega
  exact hunpaid (even_constant_anchor_height_upper_word hn4 p m hn hall)

#print axioms even_few_fixed_small_gap_word
#print axioms even_constant_height_small_fibers_word
#print axioms even_constant_height_unpaid_raw_count
#print axioms even_constant_anchor_height_upper_word
#print axioms even_unpaid_higher_anchor
end LX.AnchoredPhases
