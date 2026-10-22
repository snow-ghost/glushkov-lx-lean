import LX.EvenQuadraticUpper

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem odd_fixed_gap_exact_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 0 < height p a)
    (hf : (fixedPositions (permutation p a)).card ≤ (a-p a).val+1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*(((a-p a).val : ℤ)-height p a-anchorReserve p a)-3 := by
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
  have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  nlinarith

theorem odd_terminal_low_excluded (p : State n) (m R : ℕ)
    (hn : n=2*m+1) (hnlarge : 4096 < n)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8192)
    (b : Fin n) (hglo : 3*R+4 ≤ (b-p b).val) (hghi : (b-p b).val ≤ m+100) :
    height p b+1 ≠ m := by
  intro hh
  obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega)
    (by have := hF b; omega)
  have hr := anchor_reserve_nonneg p b
  have hg : ((b-p b).val : ℤ) ≤ (m : ℤ)+100 := by exact_mod_cast hghi
  exact hunpaid ⟨w,hw,by omega⟩

/-- Every threshold in the terminal interval is either high, the head, or
an actual backward arrow of the middle height. Missing occupied offsets
cannot be silently discarded: surplus one forces a paid next minimum. -/
theorem odd_terminal_threshold (p : State n) (a : Fin n) (m R g : ℕ)
    (hn : n=2*m+1) (hnlarge : 4096 < n) (ha : height p a+1=m)
    (hmin : ∀ b,height p a ≤ height p b)
    (hF : ∀ b,(fixedPositions (permutation p b)).card ≤ R+1)
    (hdepth : ∀ b,depthCount (displacement p b) (height p b-1) ≤ 3*R+3)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*8192)
    (hglo : 3*R+5 ≤ g) (hghi : g ≤ m+100) :
    2 ≤ rankSurplus p a (-(g : Fin n)-(p a-a)).val ∨
      -(g : Fin n)=p 0 ∨
      ∃ c : Fin n,c ∈ descendingPositions p ∧ height p c=m ∧ p c-c= -(g : Fin n) := by
  let t : Fin n := -(g : Fin n)-(p a-a)
  have hgn : g < n := by omega
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
    exact odd_terminal_low_excluded p m R hn hnlarge hF hunpaid b (by omega) (by omega) (by omega)
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
    obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p c (by omega) (by omega)
      (fun he => hhead (hcr.symm.trans he.symm)) hlast hcount
    have hne : p c ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
    have hneg : (-p c).val=n-(p c).val := by simp [Fin.val_neg,hne]
    have hg' : (c-p c).val=n+c.val-(p c).val :=
      Fin.coe_sub_iff_lt.mpr (show c < p c from hforward)
    have hfinish : c.val+(-p c).val ≤ m+100 := by rw [hneg]; omega
    have hr := anchor_reserve_nonneg p c
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
    exact False.elim (odd_terminal_low_excluded p m R hn hnlarge hF hunpaid b
      (by omega) (by omega) (by omega))

#print axioms odd_fixed_gap_exact_word
#print axioms odd_terminal_low_excluded
#print axioms odd_terminal_threshold
end LX.AnchoredPhases
