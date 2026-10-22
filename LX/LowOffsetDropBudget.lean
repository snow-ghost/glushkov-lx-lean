import LX.EvenConstantHeightConjecture

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

def lowerOffsetDrops (p : State n) (t : Fin n) : Finset (Fin n) :=
  (descendingPositions p).filter fun i => (p i-i).val < t.val

/-- Every ordinary backward arrow below a raw-offset threshold remains
backward in that normalized phase. The preimage of zero supplies one
additional arrow unless the head carries the threshold offset. -/
theorem lower_offset_drop_bound (p : State n) (a : Fin n) :
    (lowerOffsetDrops p (p a-a)).card+(if p 0=p a-a then 0 else 1) ≤ height p a := by
  classical
  let t := p a-a
  let D := lowerOffsetDrops p t
  have hpoint (i : Fin n) (hi : i ∈ D) :
      (p i).val < t.val ∧ i ∈ descendingPositions (permutation p a) := by
    obtain ⟨hid,hit⟩ := Finset.mem_filter.mp hi
    have hback : (p i).val < i.val := (mem_descendingPositions _ _).mp hid
    have hraw : (p i-i).val=n+(p i).val-i.val :=
      Fin.coe_sub_iff_lt.mpr (show p i < i from hback)
    have hip := i.isLt
    have hpt : (p i).val < t.val := by omega
    refine ⟨hpt,(mem_descendingPositions _ _).mpr ?_⟩
    have hq : permutation p a i=p i-t := by change p i+(a-p a)=p i-(p a-a); ring
    rw [hq,Fin.coe_sub_iff_lt.mpr (show p i < t from hpt)]
    omega
  have hsub : D ⊆ descendingPositions (permutation p a) := fun i hi => (hpoint i hi).2
  change D.card+(if p 0=t then 0 else 1) ≤ height p a
  by_cases hhead : p 0=t
  · rw [ite_eq_left hhead,add_zero]
    exact Finset.card_le_card hsub
  rw [ite_eq_right hhead]
  let j := p.symm t
  have hj0 : j ≠ 0 := by
    intro he
    have hpj : p j=t := p.apply_symm_apply t
    rw [he] at hpj
    exact hhead hpj
  have hqj : permutation p a j=0 := by
    change p (p.symm t)+(a-p a)=0
    rw [Equiv.apply_symm_apply]
    dsimp only [t]
    ring
  have hjd : j ∈ descendingPositions (permutation p a) := by
    rw [mem_descendingPositions,hqj,Fin.val_zero]
    exact Fin.pos_iff_ne_zero.mpr hj0
  have hjnot : j ∉ D := by
    intro hj
    have hpj := (hpoint j hj).1
    change (p (p.symm t)).val < t.val at hpj
    rw [Equiv.apply_symm_apply] at hpj
    omega
  have hc := Finset.card_le_card (Finset.insert_subset hjd hsub)
  rw [Finset.card_insert_of_notMem hjnot] at hc
  exact hc

#print axioms lower_offset_drop_bound
end LX.AnchoredPhases
