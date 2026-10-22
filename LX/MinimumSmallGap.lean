import LX.MinimumHeadObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The inexpensive minimum-phase gap is paid even when its fixed fiber
is too large for the prefix construction, provided the head is not fixed. -/
theorem small_gap_minimum_conjecture_word (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hmin : ∀ b,height p a ≤ height p b)
    (hhead : p 0 ≠ p a-a)
    (hlast : ∀ i : Fin n,p i-i=p a-a → i.val ≤ a.val)
    (hpay : ((a-p a).val : ℤ)-anchorReserve p a ≤ 2+(e : ℤ)*((height p a : ℤ)+1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  let F := a.val+(-p a).val
  have hv : (a-p a).val=if n ≤ F then F-n else F := by
    simpa only [sub_eq_add_neg] using Fin.val_add_eq_ite a (-p a)
  by_cases hF : n ≤ F
  · have hfinish : F=n+(a-p a).val := by rw [ite_eq_left hF] at hv; omega
    have hhead' : permutation p a 0 ≠ 0 := by
      intro heq
      apply hhead
      change p 0+(a-p a)=0 at heq
      linear_combination heq
    obtain ⟨k,hk,_⟩ := minimum_height_early_low_depth p a hmin hh hhead'
    obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p a hh (by omega)
      hhead hlast k hk (by change k.val ≤ F; have := k.isLt; omega)
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
    have hfin : (a.val : ℤ)+((-p a).val : ℤ)=(n : ℤ)+(a-p a).val := by exact_mod_cast hfinish
    unfold anchorReserve at hpay
    refine ⟨w,hw,?_⟩
    interval_cases e <;> norm_num at hn' hpay ⊢ <;>
      nlinarith only [hprice,hpay,hn',hfin]
  · have hfinish : a.val+(-p a).val=(a-p a).val := by rw [ite_eq_right hF] at hv; exact hv.symm
    exact gap_aligned_minimum_conjecture_word p a e he hn hh hmin hfinish hhead hlast

/-- Every unpaid odd minimum phase, except the head phase itself, has a
gap beyond the entire terminal half-window. -/
theorem odd_unpaid_nonhead_minimum_gap (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c) (hb : height p b=height p a)
    (hhead : p 0 ≠ p b-b)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    height p a+3 < (b-p b).val := by
  by_contra hnot
  obtain ⟨c,hraw,hch,_,hlast⟩ := last_offset_source p b
  have hc : height p c=height p a := hch.trans hb
  have hgap : c-p c=b-p b := by linear_combination -hraw
  have hr := anchor_reserve_nonneg p c
  obtain ⟨w,hw,hprice⟩ := small_gap_minimum_conjecture_word p c 1 (by omega) (by omega)
    (by omega) (fun d => by rw [hc]; exact hmin d)
    (fun heq => hhead (heq.trans hraw)) hlast (by rw [hgap]; omega)
  exact hunpaid ⟨w,hw,by omega⟩

#print axioms small_gap_minimum_conjecture_word
#print axioms odd_unpaid_nonhead_minimum_gap
end LX.AnchoredPhases
