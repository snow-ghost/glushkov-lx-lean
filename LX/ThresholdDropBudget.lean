import LX.LowOffsetDropBudget
import LX.RankProfileGeometry
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

def thresholdPermutation (p : State n) (t : Fin n) : State n := p.trans (Equiv.addRight (-t))

def thresholdHeight (p : State n) (t : Fin n) : ℕ :=
  (descendingPositions (thresholdPermutation p t)).card

theorem threshold_height_rank (p : State n) (a t : Fin n) :
    (thresholdHeight p t : ℤ)=(height p a : ℤ)+rankSurplus p a (t-(p a-a)).val := by
  have hm := shifted_offset_rank_mass p a (t-(p a-a))
  have he (i : Fin n) : cyclicOffset p a i-(t-(p a-a))=
      thresholdPermutation p t i-i := by
    change (p i-i)-(p a-a)-(t-(p a-a))=(p i+(-t))-i
    ring
  simp_rw [he] at hm
  rw [raw_offset_mass] at hm
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  exact mul_left_cancel₀ hn hm

/-- The backward-arrow bound also holds at unoccupied thresholds.
The physical preimage of the cut still contributes the additional drop. -/
theorem lower_offset_threshold_drop_bound (p : State n) (t : Fin n) :
    (lowerOffsetDrops p t).card+(if p 0=t then 0 else 1) ≤ thresholdHeight p t := by
  classical
  let D := lowerOffsetDrops p t
  let q := thresholdPermutation p t
  have hpoint (i : Fin n) (hi : i ∈ D) :
      (p i).val < t.val ∧ i ∈ descendingPositions q := by
    obtain ⟨hid,hit⟩ := Finset.mem_filter.mp hi
    have hback := (mem_descendingPositions _ _).mp hid
    have hraw : (p i-i).val=n+(p i).val-i.val :=
      Fin.coe_sub_iff_lt.mpr (show p i < i from hback)
    have hip := i.isLt
    have hpt : (p i).val < t.val := by omega
    refine ⟨hpt,(mem_descendingPositions _ _).mpr ?_⟩
    have hq : q i=p i-t := by change p i+(-t)=p i-t; ring
    rw [hq,Fin.coe_sub_iff_lt.mpr (show p i < t from hpt)]
    omega
  have hs : D ⊆ descendingPositions q := fun i hi => (hpoint i hi).2
  change D.card+(if p 0=t then 0 else 1) ≤ (descendingPositions q).card
  by_cases hp0 : p 0=t
  · rw [ite_eq_left hp0,add_zero]
    exact Finset.card_le_card hs
  rw [ite_eq_right hp0]
  let j := p.symm t
  have hj0 : j ≠ 0 := by
    intro he
    have hpj : p j=t := p.apply_symm_apply t
    rw [he] at hpj
    exact hp0 hpj
  have hqj : q j=0 := by change p (p.symm t)+(-t)=0; simp
  have hjd : j ∈ descendingPositions q := by
    rw [mem_descendingPositions,hqj,Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr hj0
  have hjnot : j ∉ D := by
    intro hj
    have hpj := (hpoint j hj).1
    change (p (p.symm t)).val < t.val at hpj
    rw [Equiv.apply_symm_apply] at hpj
    omega
  have hc := Finset.card_le_card (Finset.insert_subset hjd hs)
  rw [Finset.card_insert_of_notMem hjnot] at hc
  exact hc

#print axioms threshold_height_rank
#print axioms lower_offset_threshold_drop_bound
end LX.AnchoredPhases
