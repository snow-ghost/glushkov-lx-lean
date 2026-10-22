import LX.PhaseMinimumRescue
import LX.MinimumHeightRanks

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem head_displacement_offset (p : State n) (a : Fin n) :
    displacement p a 0=(cyclicOffset p a 0 : ℤ)-height p a := by
  have he : permutation p a 0=cyclicOffset p a 0 := by
    change p 0+(a-p a)=p 0-0-(p a-a)
    abel
  simp only [displacement,LRX.FiniteCuts.clockwiseRepresentative,Fin.val_zero,Nat.not_lt_zero,
    ite_false,add_zero,Nat.cast_zero,sub_zero,he]

/-- Choosing an anchor with a different cyclic displacement from position 0
makes the initial head strictly shallower than the maximal depth. -/
theorem head_reserve_of_distinct_offset (p : State n) (a : Fin n)
    (ha : cyclicOffset p a 0 ≠ 0) : backwardDepth (displacement p a) 0 < height p a := by
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  by_contra hnot
  have he : backwardDepth (displacement p a) 0=height p a := by have := hmax 0; omega
  have hd := maximum_depth_displacement (is_lift p a) 0 (by intro i; rw [he]; exact hmax i)
  rw [he,head_displacement_offset] at hd
  have hv : (cyclicOffset p a 0).val=0 := by omega
  exact ha (Fin.ext hv)

/-- The second even height is paid whenever its phase does not put a
maximum-depth token at the initial head. -/
theorem even_second_height_head_word (p : State n) (a : Fin n)
    (hn : n=2*height p a+4) (ha : cyclicOffset p a 0 ≠ 0) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n := by
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  obtain ⟨w,hw,hprice⟩ := realized_head_reserve_word (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) hmax (head_reserve_of_distinct_offset p a ha)
  have hx := (candidate_price_components p a).1
  have hna : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
  exact ⟨w,hw,by nlinarith⟩

/-- Any unpaid phase of the second even height must share its minimum offset
with the original head; this conclusion uses an actual LX word. -/
theorem even_second_unpaid_head_offset (p : State n) (a : Fin n)
    (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) : cyclicOffset p a 0=0 := by
  by_contra hnot
  obtain ⟨w,hw,hprice⟩ := even_second_height_head_word p a hn hnot
  exact hunpaid ⟨w,hw,by linarith⟩

/-- If the second even branch is unpaid, its cumulative rank profile has one
zero threshold only. Every other threshold has positive surplus. -/
theorem even_second_unpaid_rank_profile (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    cyclicOffset p a 0=0 ∧ ∀ t : Fin n,t≠0 → 1 ≤ rankSurplus p a t.val := by
  have hhead := even_second_unpaid_head_offset p a hn hunpaid
  refine ⟨hhead,?_⟩
  intro t ht
  have hnonneg := rank_surplus_nonnegative p a hmin t.val (Nat.le_of_lt t.isLt)
  by_contra hnot
  have hz : rankSurplus p a t.val=0 := by omega
  obtain ⟨b,hb,hheight⟩ := zero_surplus_anchor p a hmin t hz
  have hheadb := even_second_unpaid_head_offset p b (by omega) hunpaid
  rw [cyclic_offset_reanchor p a b 0,hhead,hb] at hheadb
  have he : t=0 := by simpa using congrArg Neg.neg hheadb
  exact ht he

/-- Removing the compulsory unit surplus leaves a nonnegative profile of
exact total mass n/2+1 in the second even branch. -/
theorem even_second_remaining_rank_mass (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (∀ t : Fin n,0 ≤ (if t=0 then (0 : ℤ) else rankSurplus p a t.val-1)) ∧
      2*(∑ t : Fin n,if t=0 then (0 : ℤ) else rankSurplus p a t.val-1)=(n : ℤ)+2 := by
  have hprofile := (even_second_unpaid_rank_profile p a hmin hn hunpaid).2
  constructor
  · intro t
    split_ifs with ht
    · omega
    · have hh := hprofile t ht
      omega
  · have hz : rankSurplus p a 0=0 := by simp [rankSurplus,belowCount]
    have he (t : Fin n) : (if t=0 then (0 : ℤ) else rankSurplus p a t.val-1)=
        rankSurplus p a t.val-1+(if t=0 then 1 else 0) := by
      by_cases ht : t=0
      · subst t
        simp [hz]
      · simp [ht]
    simp_rw [he]
    rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,
      Finset.sum_ite_eq',Finset.mem_univ,ite_true]
    have hsum := rank_surplus_sum p a
    have hna : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
    nlinarith

#print axioms even_second_height_head_word
#print axioms even_second_unpaid_rank_profile
#print axioms even_second_remaining_rank_mass
end LX.AnchoredPhases
