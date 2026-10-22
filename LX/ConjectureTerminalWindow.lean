import LX.ConjecturePhaseReduction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem conjecture_window_terminal_low_excluded (p : State n) (m R e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 6 < n)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ)))
    (b : Fin n) (hglo : R ≤ (b-p b).val) (hghi : (b-p b).val ≤ e*m+2) :
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

/-- Every terminal threshold is high, the head, the selected exceptional
source, or a backward arrow of the middle height. A missing occupied
surplus-one threshold forces a paid next minimum. -/
theorem conjecture_window_terminal_threshold (p : State n) (a z : Fin n) (m R g e : ℕ)
    (he : e ≤ 1) (hn : n=2*m+e) (hnlarge : 6 < n) (hupper : e*m+2 < n) (ha : height p a+1=m)
    (hmin : ∀ b,height p a ≤ height p b)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ R)
    (hz : ∀ c,height p c=m → R+1 ≤ (c-p c).val →
      height p z=m ∧ R+1 ≤ (z-p z).val ∧ (z-p z).val ≤ (c-p c).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ)))
    (hglo : R+1 ≤ g) (hghi : g ≤ e*m+2) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      (-(g : Fin n)=p 0 ∧ height p 0=m) ∨
      -(g : Fin n)=p z-z ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c= -(g : Fin n) := by
  let t : Fin n := -(g : Fin n)-(p a-a)
  by_cases hspecial : -(g : Fin n)=p z-z
  · exact Or.inr (Or.inr (Or.inl hspecial))
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
    exact conjecture_window_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b (by omega) (by omega) (by omega)
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
    refine Or.inr (Or.inr (Or.inr ⟨c,?_,hcHeight,hcr⟩))
    rw [mem_descendingPositions]
    by_contra hnot
    have hforward : c.val < (p c).val := by
      by_contra hnot'
      have he : p c=c := Fin.ext (by omega)
      rw [he,sub_self,Fin.val_zero] at hgap
      omega
    have hz' := hz c hcHeight (by omega)
    have hgaplt : (z-p z).val < (c-p c).val := by
      have hne : (z-p z).val ≠ (c-p c).val := by
        intro heq
        have he : z-p z=c-p c := Fin.ext heq
        apply hspecial
        rw [← hcr]
        linear_combination he
      omega
    have hf := gap_separation_bounds_fixed p c z (by omega) hgaplt
    have hd := rank_peak_next_depth_fiber p a R hR c (by omega)
    have hcount : depthCount (displacement p c) (height p c-1) ≤ c.val+(-p c).val := by
      have hg : (c-p c).val ≤ c.val+(-p c).val := by
        rw [sub_eq_add_neg,Fin.val_add]
        exact Nat.mod_le _ _
      omega
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    have hg' : (c-p c).val=n+c.val-(p c).val :=
      Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)
    have hfinish : c.val+(-p c).val ≤ e*m+2 := by rw [hneg]; omega
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
    exact False.elim (conjecture_window_terminal_low_excluded p m R e he hn hnlarge hF hunpaid b
      (by omega) (by omega) (by omega))


#print axioms conjecture_window_terminal_threshold
end LX.AnchoredPhases
