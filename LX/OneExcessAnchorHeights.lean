import LX.OddThreeRankObstruction

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A rank-three occupied threshold would force a second rank-three
threshold immediately after it. One unit of second excess forbids this. -/
theorem one_second_excess_anchor_height (p : State n) (a b : Fin n)
    (hQ : secondExcess p a ≤ 1) : height p b ≤ height p a+2 := by
  classical
  by_contra hnot
  let r := cyclicOffset p a b
  have hrank : 3 ≤ rankSurplus p a r.val := by
    have hh := reanchor_height p a b
    change (height p b : ℤ)=(height p a : ℤ)-(r : ℤ)+belowCount p a r.val at hh
    unfold rankSurplus
    omega
  have hcount : belowCount p a r.val ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hrn : r.val+1 < n := by unfold rankSurplus at hrank; omega
  let u : Fin n := ⟨r.val+1,hrn⟩
  have hsucc := below_count_succ p a r.val
  have hf : 0 < (Finset.univ.filter fun i : Fin n => (cyclicOffset p a i).val=r.val).card := by
    apply Finset.card_pos.mpr
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩⟩
  have hunext : 3 ≤ rankSurplus p a u.val := by
    change 3 ≤ rankSurplus p a (r.val+1)
    unfold rankSurplus at hrank ⊢
    omega
  have hne : r ≠ u := by
    intro he
    have hv := congrArg Fin.val he
    change r.val=r.val+1 at hv
    omega
  have hs : (∑ t ∈ ({r,u} : Finset (Fin n)),max (rankSurplus p a t.val-2) 0) ≤ secondExcess p a := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _
    exact le_max_right _ _
  rw [Finset.sum_pair hne] at hs
  have hrt : 1 ≤ max (rankSurplus p a r.val-2) 0 := by omega
  have hut : 1 ≤ max (rankSurplus p a u.val-2) 0 := by omega
  omega

theorem odd_unpaid_three_anchor_heights (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    ∀ b,height p b=height p a ∨ height p b=height p a+1 ∨ height p b=height p a+2 := by
  have hQ := odd_unpaid_second_excess_le_one p a hn hh hmin hunpaid
  intro b
  have hu := one_second_excess_anchor_height p a b hQ
  have hl := hmin b
  omega

#print axioms one_second_excess_anchor_height
#print axioms odd_unpaid_three_anchor_heights
end LX.AnchoredPhases
