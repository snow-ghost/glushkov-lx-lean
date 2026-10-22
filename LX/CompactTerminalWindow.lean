import LX.OddQuadraticUpper

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem compact_terminal_low_excluded (p : State n) (m R e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 105 < n)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*158)
    (b : Fin n) (hglo : 3*R+4 ≤ (b-p b).val) (hghi : (b-p b).val ≤ e*m+53) :
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
theorem compact_terminal_threshold (p : State n) (a : Fin n) (m R g e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 105 < n) (ha : height p a+1=m)
    (hmin : ∀ b,height p a ≤ height p b)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hdepth : ∀ b,depthCount (displacement p b) (height p b-1) ≤ 3*R+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*158)
    (hglo : 3*R+5 ≤ g) (hghi : g ≤ e*m+53) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      -(g : Fin n)=p 0 ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c= -(g : Fin n) := by
  let t : Fin n := -(g : Fin n)-(p a-a)
  have hgn : g < n := by interval_cases e <;> omega
  have hgv : (g : Fin n).val=g := Nat.mod_eq_of_lt hgn
  by_cases hhigh : 2 ≤ rankSurplus p a t.val
  · exact Or.inl hhigh
  by_cases hhead : -(g : Fin n)=p 0
  · exact Or.inr (Or.inl hhead)
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
    exact compact_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b (by omega) (by omega) (by omega)
  have hone : rankSurplus p a t.val=1 := by omega
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
      have hc := hdepth c
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    have hg' : (c-p c).val=n+c.val-(p c).val :=
      Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)
    have hfinish : c.val+(-p c).val ≤ e*m+53 := by rw [hneg]; omega
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
    exact False.elim (compact_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b
      (by omega) (by omega) (by omega))

#print axioms compact_terminal_low_excluded
#print axioms compact_terminal_threshold
end LX.AnchoredPhases
