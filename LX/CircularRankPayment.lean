import LX.RankReserveSharpPayment
import LX.PrefixGapDeadline

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The full-circle price potential. Crossing zero adds one full turn;
omitting this term would incorrectly extend the nonwrapping criterion. -/
def circularRankPrice (p : State n) (a b : Fin n) (e : ℕ) : ℤ :=
  ((a-p a).val : ℤ)-anchorReserve p a+
    (e : ℤ)*(cyclicOffset p a b : ℤ)-
    2*(∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k)+
    if (a-p a).val < (b-p b).val then (n : ℤ) else 0

/-- Exact price transport on the entire circle, for actual permutations. -/
theorem circular_rank_price_eq (p : State n) (a b : Fin n) (e : ℕ)
    (hn : n=2*height p a+2+e) :
    circularRankPrice p a b e=
      ((b-p b).val : ℤ)-anchorReserve p b+
        rankSurplus p a (cyclicOffset p a b).val := by
  have ho : cyclicOffset p a b=(a-p a)-(b-p b) := by
    unfold cyclicOffset
    ring
  have hv := cyclic_subtraction_value (a-p a) (b-p b)
  rw [← ho] at hv
  have ht := anchor_reserve_rank_transport p a b
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  rw [hn'] at ht
  unfold circularRankPrice
  nlinarith only [hv,ht]

/-- The minimum-height prefix certificate now permits every phase,
including phases past the circular origin. -/
theorem circular_rank_low_conjecture_word (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 0 < height p a)
    (hheight : height p b=height p a)
    (hf : (fixedPositions (permutation p b)).card ≤ (b-p b).val+1)
    (hpay : circularRankPrice p a b e ≤ 2+(e : ℤ)*((height p a : ℤ)+1)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hs : rankSurplus p a (cyclicOffset p a b).val=0 := by
    have hh := reanchor_height p a b
    unfold rankSurplus
    omega
  rw [circular_rank_price_eq p a b e hn,hs,add_zero] at hpay
  interval_cases e
  · obtain ⟨w,hw,hprice⟩ := even_fixed_gap_exact_word p b (by omega) (by omega) hf
    norm_num at hpay ⊢
    exact ⟨w,hw,by omega⟩
  · obtain ⟨w,hw,hprice⟩ := odd_fixed_gap_exact_word p b (by omega) (by omega) hf
    norm_num at hpay ⊢
    exact ⟨w,hw,by omega⟩

/-- The higher phase may finish in either orientation. Its literal cursor
cost is retained and a prefix gap replaces the coarser depth-count bound. -/
theorem circular_rank_high_conjecture_word (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 1 ≤ height p a)
    (hheight : height p b=height p a+1)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (k : Fin n) (hk : backwardDepth (displacement p b) k < height p b-1)
    (hfinish : k.val ≤ b.val+(-p b).val)
    (hpay : circularRankPrice p a b e+
      ((b.val : ℤ)+((-p b).val : ℤ)-((b-p b).val : ℤ)) ≤
        4+(e : ℤ)*height p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hs : rankSurplus p a (cyclicOffset p a b).val=1 := by
    have hh := reanchor_height p a b
    unfold rankSurplus
    omega
  rw [circular_rank_price_eq p a b e hn,hs] at hpay
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p b
    (by omega) (by omega) hhead hlast k hk hfinish
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  have hh' : (height p b : ℤ)=(height p a : ℤ)+1 := by exact_mod_cast hheight
  unfold anchorReserve at hpay
  refine ⟨w,hw,?_⟩
  interval_cases e <;> norm_num at hn' hpay ⊢ <;>
    nlinarith only [hpay,hprice,hn',hh']

/-- All aligned phases use one criterion. The height rise is retained
quadratically, so low phases and rises greater than one are not discarded. -/
theorem circular_rank_aligned_conjecture_word (p : State n) (a b : Fin n) (e s : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e)
    (hheight : height p b=height p a+s) (hh : 2 ≤ height p b)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (k : Fin n) (hk : backwardDepth (displacement p b) k < height p b-1)
    (hfinish : k.val ≤ b.val+(-p b).val)
    (hpay : circularRankPrice p a b e+
      ((b.val : ℤ)+((-p b).val : ℤ)-((b-p b).val : ℤ)) ≤
        4+2*(height p a : ℤ)+(e : ℤ)*(height p a+2)-
          (s : ℤ)*(2*(height p a : ℤ)+2*e+1-s)) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  have hs : rankSurplus p a (cyclicOffset p a b).val=s := by
    have hh := reanchor_height p a b
    unfold rankSurplus
    omega
  rw [circular_rank_price_eq p a b e hn,hs] at hpay
  obtain ⟨w,hw,_,hprice⟩ := aligned_anchor_prefix_gap_zero_word p b hh
    (by omega) hhead hlast k hk hfinish
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  have hh' : (height p b : ℤ)=(height p a : ℤ)+s := by exact_mod_cast hheight
  unfold anchorReserve at hpay
  rw [hh',hn'] at hpay hprice
  rw [hn']
  refine ⟨w,hw,?_⟩
  interval_cases e <;> norm_num at hpay hprice ⊢ <;>
    nlinarith only [hpay,hprice]

/-- Precisely the two proved word constructions tested by the diagnostic:
the low prefix route and aligned routes at every nonnegative height rise.
Existence of this certificate for all remaining inputs is not postulated. -/
def CircularPhaseCertificate (p : State n) (a b : Fin n) (e : ℕ) : Prop :=
  (height p b=height p a ∧
    (fixedPositions (permutation p b)).card ≤ (b-p b).val+1 ∧
    circularRankPrice p a b e ≤ 2+(e : ℤ)*((height p a : ℤ)+1)) ∨
  ∃ s : ℕ,∃ k : Fin n,height p b=height p a+s ∧ 2 ≤ height p b ∧
    p 0 ≠ p b-b ∧ (∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val) ∧
    backwardDepth (displacement p b) k < height p b-1 ∧
    k.val ≤ b.val+(-p b).val ∧
    circularRankPrice p a b e+
      ((b.val : ℤ)+((-p b).val : ℤ)-((b-p b).val : ℤ)) ≤
        4+2*(height p a : ℤ)+(e : ℤ)*(height p a+2)-
          (s : ℤ)*(2*(height p a : ℤ)+2*e+1-s)

theorem circular_phase_certificate_word (p : State n) (a b : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 0 < height p a)
    (hc : CircularPhaseCertificate p a b e) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+12-3*e := by
  rcases hc with ⟨hheight,hf,hpay⟩ | ⟨s,k,hheight,hb,hhead,hlast,hk,hfinish,hpay⟩
  · exact circular_rank_low_conjecture_word p a b e he hn hh hheight hf hpay
  · exact circular_rank_aligned_conjecture_word p a b e s he hn hheight hb
      hhead hlast k hk hfinish hpay

/-- Every actual counterexample must fail all these circular certificates,
including the low aligned branch exhibited by PhaseSelectionRegression. -/
theorem conjecture_unpaid_circular_constraints (p : State n) (a : Fin n) (e : ℕ)
    (he : e ≤ 1) (hn : n=2*height p a+2+e) (hh : 0 < height p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*(4-(e : ℤ))) :
    ∀ b : Fin n,¬CircularPhaseCertificate p a b e := by
  intro b hc
  obtain ⟨w,hw,hprice⟩ := circular_phase_certificate_word p a b e he hn hh hc
  exact hunpaid ⟨w,hw,by omega⟩

#print axioms circular_rank_price_eq
#print axioms circular_rank_low_conjecture_word
#print axioms circular_rank_high_conjecture_word
#print axioms circular_rank_aligned_conjecture_word
#print axioms circular_phase_certificate_word
#print axioms conjecture_unpaid_circular_constraints
end LX.AnchoredPhases
