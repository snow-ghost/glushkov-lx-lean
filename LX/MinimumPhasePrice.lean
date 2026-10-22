import LX.CriticalPhaseWord

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The partial cumulative count is the complementary mass of offsets below
the threshold. This is an identity for the actual input, including ties. -/
theorem below_count_partial_mass (p : State n) (a : Fin n) (t : ℕ) :
    (∑ k ∈ Finset.range t, (belowCount p a k : ℤ)) =
      ((t : ℤ)-1)*(belowCount p a t : ℤ)-
        ∑ i ∈ Finset.univ.filter (fun i => (cyclicOffset p a i).val < t),
          (cyclicOffset p a i : ℤ) := by
  classical
  have hpoint (r : ℕ) :
      (∑ k ∈ Finset.range t, if r < k then (1 : ℤ) else 0)=
        if r < t then (t : ℤ)-1-r else 0 := by
    have he : (Finset.range t).filter (fun k => r < k)=Finset.Ioo r t := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ioo]
      tauto
    rw [← Finset.sum_filter,he]
    simp only [Finset.sum_const,Nat.card_Ioo,nsmul_eq_mul,mul_one]
    split_ifs <;> omega
  simp only [belowCount,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,
    Nat.cast_one,Nat.cast_zero]
  rw [Finset.sum_comm]
  simp_rw [hpoint]
  rw [← Finset.sum_filter]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const,nsmul_eq_mul]
  rw [mul_comm]
  congr 1
  simp

/-- Arbitrary equal-height phases, with all intermediate height excursions
included in a partial rank-surplus sum. No energy-minimality is assumed. -/
theorem equal_height_exchange_rank_sum (p : State n) (a b : Fin n)
    (hh : height p b=height p a) :
    (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
      (cyclicOffset p a b : ℤ)*((n : ℤ)-2*height p a-1)-
        2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k := by
  classical
  let t := (cyclicOffset p a b).val
  let A := Finset.univ.filter fun i => (cyclicOffset p a i).val < t
  have ht : t ≤ n := Nat.le_of_lt (cyclicOffset p a b).isLt
  have hcount : belowCount p a t=t := by
    have hc := reanchor_height p a b
    rw [hh] at hc
    change (height p a : ℤ)=(height p a : ℤ)-(t : ℤ)+belowCount p a t at hc
    omega
  have hAc : A.card=t := hcount
  have hcard : (reanchorSet p a b).card=n-t := by
    rw [reanchor_set_card,hcount]
  have hsum : (∑ i ∈ reanchorSet p a b,displacement p a i)=
      (t : ℤ)*height p a-∑ i ∈ A,(cyclicOffset p a i : ℤ) := by
    have hs := Finset.sum_compl_add_sum A (displacement p a)
    rw [displacement_balance] at hs
    have hm : (∑ i ∈ A,displacement p a i)=
        (∑ i ∈ A,(cyclicOffset p a i : ℤ))-(t : ℤ)*height p a := by
      simp_rw [displacement_offset]
      rw [Finset.sum_sub_distrib]
      simp [hAc]
    rw [hm] at hs
    change (∑ i ∈ Aᶜ,displacement p a i)=_
    omega
  have hx := reanchor_inversion_difference p a b
  rw [hcard,Nat.cast_sub ht,hsum] at hx
  have hm := below_count_partial_mass p a t
  rw [hcount] at hm
  change (∑ k ∈ Finset.range t,(belowCount p a k : ℤ))=
    ((t : ℤ)-1)*(t : ℤ)-∑ i ∈ A,(cyclicOffset p a i : ℤ) at hm
  have hr : (∑ k ∈ Finset.range t,rankSurplus p a k)=
      (∑ k ∈ Finset.range t,(belowCount p a k : ℤ))-
        ∑ k ∈ Finset.range t,(k : ℤ) := by
    simp only [rankSurplus,Finset.sum_sub_distrib]
  have htri := LRX.FiniteCoordinates.range_sum_twice t
  change (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
    (t : ℤ)*((n : ℤ)-2*height p a-1)-2*∑ k ∈ Finset.range t,rankSurplus p a k
  nlinarith

/-- The cumulative correction is nonnegative at a minimum-height source. -/
theorem minimum_height_partial_rank_nonneg (p : State n) (a : Fin n)
    (hmin : ∀ b,height p a ≤ height p b) (t : ℕ) (ht : t ≤ n) :
    0 ≤ ∑ k ∈ Finset.range t,rankSurplus p a k := by
  apply Finset.sum_nonneg
  intro k hk
  exact rank_surplus_nonnegative p a hmin k
    (by have := Finset.mem_range.mp hk; omega)

/-- In even size, moving between minimum-height phases costs at most the
cyclic raw-offset distance, however many higher phases lie between them. -/
theorem even_minimum_height_exchange_bound (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hh : height p b=height p a)
    (hmin : ∀ c,height p a ≤ height p c) :
    (inversions (displacement p b) : ℤ)-inversions (displacement p a) ≤
      (cyclicOffset p a b : ℤ) := by
  have he := equal_height_exchange_rank_sum p a b hh
  have hs := minimum_height_partial_rank_nonneg p a hmin (cyclicOffset p a b).val
    (Nat.le_of_lt (cyclicOffset p a b).isLt)
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  nlinarith

/-- Exact improvement of the cyclic finishing price. The sum accounts for
all intermediate phases, so no same-height chain hypothesis is needed. -/
theorem even_equal_height_cyclic_price (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hh : height p b=height p a)
    (hgap : (b-p b).val ≤ (a-p a).val) :
    ((b-p b).val : ℤ)-anchorReserve p b=
      ((a-p a).val : ℤ)-anchorReserve p a-
        2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k := by
  have hoff : cyclicOffset p a b=(a-p a)-(b-p b) := by
    unfold cyclicOffset
    ring
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    rw [hoff,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hgap)]
  have he := equal_height_exchange_rank_sum p a b hh
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have htv : (cyclicOffset p a b : ℤ)=((a-p a).val : ℤ)-((b-p b).val : ℤ) := by
    rw [ht,Nat.cast_sub hgap]
  rw [htv] at he
  unfold anchorReserve
  rw [hh]
  nlinarith

/-- Among even minimum-height phases, a smaller cyclic finishing gap has
no larger finishing-gap-minus-reserve price. Global energy minimality of
either phase is unnecessary. -/
theorem even_minimum_height_cyclic_price_le (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hh : height p b=height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hgap : (b-p b).val ≤ (a-p a).val) :
    ((b-p b).val : ℤ)-anchorReserve p b ≤
      ((a-p a).val : ℤ)-anchorReserve p a := by
  have he := even_equal_height_cyclic_price p a b hn hh hgap
  have hs := minimum_height_partial_rank_nonneg p a hmin (cyclicOffset p a b).val
    (Nat.le_of_lt (cyclicOffset p a b).isLt)
  omega

/-- A single endpoint minimizes the cyclic price over all minimum-height
phases. This does not assert that its literal word meets the diameter bound:
the head, orientation and next-depth scheduling conditions remain relevant. -/
theorem even_minimum_height_price_minimizer (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hmin : ∀ c,height p a ≤ height p c) :
    ∃ b : Fin n,height p b=height p a ∧
      ∀ c : Fin n,height p c=height p a →
        (b-p b).val ≤ (c-p c).val ∧
        ((b-p b).val : ℤ)-anchorReserve p b ≤
          ((c-p c).val : ℤ)-anchorReserve p c := by
  classical
  let S := Finset.univ.filter fun b => height p b=height p a
  obtain ⟨b,hb,hbmin⟩ := Finset.exists_min_image S (fun b => (b-p b).val)
    ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hh := (Finset.mem_filter.mp hb).2
  refine ⟨b,hh,?_⟩
  intro c hc
  have hgap := hbmin c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc⟩)
  exact ⟨hgap,even_minimum_height_cyclic_price_le p c b (by omega) (by omega)
    (fun d => by rw [hc]; exact hmin d) hgap⟩

/-- The accumulated rank surplus can pay an actual backward finishing
arrow. This connects the arbitrary-phase identity to a literal LX word. -/
theorem even_equal_height_rank_payment (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hh : height p b=height p a) (hheight : 2 ≤ height p a)
    (hgap : (b-p b).val ≤ (a-p a).val)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hpos : 0 < (p b).val) (hback : (p b).val < b.val)
    (hpay : ((a-p a).val : ℤ)-anchorReserve p a ≤
      2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k+30) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  have he := even_equal_height_cyclic_price p a b hn hh hgap
  have hv : (b-p b).val=b.val-(p b).val :=
    Fin.coe_sub_iff_le.mpr (show p b ≤ b from Nat.le_of_lt hback)
  rw [hv,Nat.cast_sub (Nat.le_of_lt hback)] at he
  exact even_backward_anchor_reserve_word p b (by omega) (by omega)
    hhead hlast hpos hback (by omega)

/-- Every eligible later minimum-height phase constrains an unpaid critical
input. This is a necessary condition on the original permutation, not a
postulated bound on an abstract family of phase costs. -/
theorem even_unpaid_critical_rank_budget (hn4 : 4 ≤ n) (p : State n) (a : Fin n)
    (ha : CriticalPhase p a) (hn : n=2*height p a+2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32)
    (b : Fin n) (hh : height p b=height p a)
    (hgap : (b-p b).val ≤ (a-p a).val)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hpos : 0 < (p b).val) (hback : (p b).val < b.val) :
    0 ≤ (∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k) ∧
      2*(∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k)+31 ≤
        ((a-p a).val : ℤ)-anchorReserve p a := by
  have hmin := unpaid_critical_minimum_height hn4 p a ha hunpaid
  refine ⟨minimum_height_partial_rank_nonneg p a hmin (cyclicOffset p a b).val
    (Nat.le_of_lt (cyclicOffset p a b).isLt),?_⟩
  have hheight : 2 ≤ height p a := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hnsmall : (n : ℤ) ≤ 4 := by omega
    nlinarith
  by_contra hnot
  exact hunpaid (even_equal_height_rank_payment p a b hn hh hheight hgap
    hhead hlast hpos hback (by omega))

#print axioms below_count_partial_mass
#print axioms equal_height_exchange_rank_sum
#print axioms minimum_height_partial_rank_nonneg
#print axioms even_minimum_height_exchange_bound
#print axioms even_equal_height_cyclic_price
#print axioms even_minimum_height_cyclic_price_le
#print axioms even_minimum_height_price_minimizer
#print axioms even_equal_height_rank_payment
#print axioms even_unpaid_critical_rank_budget
end LX.AnchoredPhases
