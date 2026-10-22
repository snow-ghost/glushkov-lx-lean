import LX.RankReserveTransport
import LX.LowForwardPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The rank area pays an actual minimum-height prefix word at the
conjectured parity price. The reserve is transported from the given source. -/
theorem rank_reserve_low_conjecture_word (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 0 < height p a)
    (hheight : height p b=height p a) (hgap : (b-p b).val ≤ (a-p a).val)
    (hf : (fixedPositions (permutation p b)).card ≤ (b-p b).val+1)
    (hpay : ((a-p a).val : ℤ)-anchorReserve p a+(e : ℤ)*(cyclicOffset p a b : ℤ) ≤
      2*(∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k) +
        2+(e : ℤ)*((height p a : ℤ)+1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hs : rankSurplus p a (cyclicOffset p a b).val=0 := by
    have hh := reanchor_height p a b
    unfold rankSurplus
    omega
  interval_cases e
  · have ht := even_gap_reserve_transport p a b (by omega) hgap
    rw [hs] at ht
    obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega) hf
    norm_num at hpay ⊢
    exact ⟨w,hw,by omega⟩
  · have ht := odd_gap_reserve_transport p a b (by omega) hgap
    rw [hs] at ht
    obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega) hf
    norm_num at hpay ⊢
    exact ⟨w,hw,by omega⟩

/-- A forward phase one level higher is paid using its actual final gap
and next-depth count, at the same conjectured constants. -/
theorem rank_reserve_high_conjecture_word (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 2 ≤ height p a)
    (hheight : height p b=height p a+1) (hgap : (b-p b).val ≤ (a-p a).val)
    (hforward : b.val < (p b).val) (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hcount : depthCount (displacement p b) (height p b-1) ≤ (b-p b).val)
    (hpay : ((a-p a).val : ℤ)-anchorReserve p a+(e : ℤ)*(cyclicOffset p a b : ℤ) ≤
      2*(∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k) +
        4+(e : ℤ)*height p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hs : rankSurplus p a (cyclicOffset p a b).val=1 := by
    have hh := reanchor_height p a b
    unfold rankSurplus
    omega
  have hpne : p b ≠ 0 := by intro he; rw [he,Fin.val_zero] at hforward; omega
  have hneg : (-p b).val=n-(p b).val := by simp [Fin.val_neg,hpne]
  have hgapval : (b-p b).val=n+b.val-(p b).val :=
    Fin.coe_sub_iff_lt.mpr (show b < p b from hforward)
  have hfinish : b.val+(-p b).val=(b-p b).val := by rw [hneg,hgapval]; have := (p b).isLt; omega
  have hcount' : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val := by omega
  interval_cases e
  · have ht := even_gap_reserve_transport p a b (by omega) hgap
    rw [hs] at ht
    obtain ⟨w,hw,hprice⟩ := even_higher_anchor_reserve_price p b (by omega) (by omega) hhead hlast hcount'
    norm_num at hpay ⊢
    have hf : (b.val : ℤ)+((-p b).val : ℤ)=((b-p b).val : ℤ) := by exact_mod_cast hfinish
    exact ⟨w,hw,by omega⟩
  · have ht := odd_gap_reserve_transport p a b (by omega) hgap
    rw [hs] at ht
    obtain ⟨w,hw,hprice⟩ := odd_higher_anchor_reserve_price p b (by omega) (by omega) hhead hlast hcount'
    norm_num at hpay ⊢
    have hf : (b.val : ℤ)+((-p b).val : ℤ)=((b-p b).val : ℤ) := by exact_mod_cast hfinish
    exact ⟨w,hw,by omega⟩

/-- Every genuinely unpaid input must fail the weighted low-phase
certificate at every eligible representative. -/
theorem conjecture_unpaid_low_rank_budget (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 0 < height p a)
    (hheight : height p b=height p a) (hgap : (b-p b).val ≤ (a-p a).val)
    (hf : (fixedPositions (permutation p b)).card ≤ (b-p b).val+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    2*(∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k) +
      3+(e : ℤ)*((height p a : ℤ)+1) ≤
        ((a-p a).val : ℤ)-anchorReserve p a+(e : ℤ)*(cyclicOffset p a b : ℤ) := by
  by_contra hnot
  obtain ⟨w,hw,hprice⟩ := rank_reserve_low_conjecture_word p a b e he hn hh hheight hgap hf (by omega)
  exact hunpaid ⟨w,hw,by omega⟩

#print axioms rank_reserve_low_conjecture_word
#print axioms rank_reserve_high_conjecture_word
#print axioms conjecture_unpaid_low_rank_budget
end LX.AnchoredPhases
