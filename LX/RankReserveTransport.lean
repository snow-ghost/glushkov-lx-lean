import LX.MinimumPhasePrice

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Exact transport of the reserve through every intermediate threshold.
The two anchors may have different heights and need not minimize energy. -/
theorem anchor_reserve_rank_transport (p : State n) (a b : Fin n) :
    anchorReserve p b-anchorReserve p a=
      rankSurplus p a (cyclicOffset p a b).val-
      (cyclicOffset p a b : ℤ)*((n : ℤ)-2*height p a-1)+
      2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k := by
  classical
  let t := (cyclicOffset p a b).val
  let C := belowCount p a t
  let A := Finset.univ.filter fun i => (cyclicOffset p a i).val < t
  have hCn : C ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hAc : A.card=C := rfl
  have hcard : (reanchorSet p a b).card=n-C := reanchor_set_card p a b
  have hsum : (∑ i ∈ reanchorSet p a b,displacement p a i)=
      (C : ℤ)*height p a-∑ i ∈ A,(cyclicOffset p a i : ℤ) := by
    have hs := Finset.sum_compl_add_sum A (displacement p a)
    rw [displacement_balance] at hs
    have hm : (∑ i ∈ A,displacement p a i)=
        (∑ i ∈ A,(cyclicOffset p a i : ℤ))-(C : ℤ)*height p a := by
      simp_rw [displacement_offset]
      rw [Finset.sum_sub_distrib]
      simp [hAc]
    rw [hm] at hs
    change (∑ i ∈ Aᶜ,displacement p a i)=_
    omega
  have hx := reanchor_inversion_difference p a b
  rw [hcard,Nat.cast_sub hCn,hsum] at hx
  have hm := below_count_partial_mass p a t
  change (∑ k ∈ Finset.range t,(belowCount p a k : ℤ))=
    ((t : ℤ)-1)*(C : ℤ)-∑ i ∈ A,(cyclicOffset p a i : ℤ) at hm
  have hr : (∑ k ∈ Finset.range t,rankSurplus p a k)=
      (∑ k ∈ Finset.range t,(belowCount p a k : ℤ))-
        ∑ k ∈ Finset.range t,(k : ℤ) := by
    simp only [rankSurplus,Finset.sum_sub_distrib]
  have htri := LRX.FiniteCoordinates.range_sum_twice t
  have hh := reanchor_height p a b
  change (height p b : ℤ)=(height p a : ℤ)-(t : ℤ)+C at hh
  change anchorReserve p b-anchorReserve p a=
    ((C : ℤ)-t)-(t : ℤ)*((n : ℤ)-2*height p a-1)+
      2*∑ k ∈ Finset.range t,rankSurplus p a k
  unfold anchorReserve
  rw [hh]
  nlinarith only [hx,hm,hr,htri]

/-- In the even critical strip, a lower gap gains both the full rank area
and the height rise. This extends the older equal-height price identity. -/
theorem even_gap_reserve_transport (p : State n) (a b : Fin n)
    (hn : n=2*height p a+2) (hgap : (b-p b).val ≤ (a-p a).val) :
    ((b-p b).val : ℤ)-anchorReserve p b=
      ((a-p a).val : ℤ)-anchorReserve p a-
        rankSurplus p a (cyclicOffset p a b).val-
        2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k := by
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    have he : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
    rw [he,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hgap)]
  have hv : (cyclicOffset p a b : ℤ)=((a-p a).val : ℤ)-((b-p b).val : ℤ) := by
    rw [ht,Nat.cast_sub hgap]
  have he := anchor_reserve_rank_transport p a b
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  rw [hn',hv] at he
  nlinarith only [he]

/-- The odd analogue retains its extra linear threshold term instead of
silently reusing the even transport formula. -/
theorem odd_gap_reserve_transport (p : State n) (a b : Fin n)
    (hn : n=2*height p a+3) (hgap : (b-p b).val ≤ (a-p a).val) :
    ((b-p b).val : ℤ)-anchorReserve p b=
      ((a-p a).val : ℤ)-anchorReserve p a+(cyclicOffset p a b : ℤ)-
        rankSurplus p a (cyclicOffset p a b).val-
        2*∑ k ∈ Finset.range (cyclicOffset p a b).val,rankSurplus p a k := by
  have ht : (cyclicOffset p a b).val=(a-p a).val-(b-p b).val := by
    have he : cyclicOffset p a b=(a-p a)-(b-p b) := by unfold cyclicOffset; ring
    rw [he,Fin.coe_sub_iff_le.mpr (show b-p b ≤ a-p a from hgap)]
  have hv : (cyclicOffset p a b : ℤ)=((a-p a).val : ℤ)-((b-p b).val : ℤ) := by
    rw [ht,Nat.cast_sub hgap]
  have he := anchor_reserve_rank_transport p a b
  have hn' : (n : ℤ)=2*(height p a : ℤ)+3 := by exact_mod_cast hn
  rw [hn',hv] at he
  rw [hv]
  nlinarith only [he]

#print axioms anchor_reserve_rank_transport
#print axioms even_gap_reserve_transport
#print axioms odd_gap_reserve_transport
end LX.AnchoredPhases
