import LX.OddHeadLeastGap

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

def nonzeroLowerOffsetDrops (p : State n) (t : Fin n) : Finset (Fin n) :=
  (lowerOffsetDrops p t).filter fun i => p i ≠ 0

theorem nonzero_lower_drops_subset (p : State n) (t : Fin n) :
    nonzeroLowerOffsetDrops p t ⊆ descendingPositions (thresholdPermutation p t) := by
  intro i hi
  have hilow := (Finset.mem_filter.mp hi).1
  obtain ⟨hid,hit⟩ := Finset.mem_filter.mp hilow
  have hback := (mem_descendingPositions _ _).mp hid
  have hraw : (p i-i).val=n+(p i).val-i.val :=
    Fin.coe_sub_iff_lt.mpr (show p i < i from hback)
  have hip := i.isLt
  have hpt : (p i).val < t.val := by omega
  apply (mem_descendingPositions _ _).mpr
  have hq : thresholdPermutation p t i=p i-t := by change p i+(-t)=p i-t; ring
  rw [hq,Fin.coe_sub_iff_lt.mpr (show p i < t from hpt)]
  omega

/-- The last fixed source of the aligned phase supplies an additional
head-normalized descent outside all nonzero physical backward arrows. -/
theorem rank_two_unpaid_head_drop_upper (p : State n) (a : Fin n)
    (hn : n=2*height p a+3) (hh : 2 ≤ height p a)
    (hmin : ∀ c,height p a ≤ height p c)
    (hR : ∀ t : Fin n,rankSurplus p a t.val ≤ 2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) ≤ 3*(n : ℤ)^2-8*n+9) :
    (nonzeroLowerOffsetDrops p (p 0)).card ≤ height p a := by
  classical
  obtain ⟨b,hb⟩ := rank_two_unpaid_aligned_exists p a hn hh hmin hR hunpaid
  have hklt := (rank_two_unpaid_aligned_source_after_head_offset p a b hn hh hmin hR hb hunpaid).1
  have hkpos := (rank_two_unpaid_aligned_gap p a b hn hh hR hb hunpaid).2.2.2.2.1
  have hbdesc : b ∈ descendingPositions (thresholdPermutation p (p 0)) := by
    apply (mem_descendingPositions _ _).mpr
    have he : thresholdPermutation p (p 0) b=b-cyclicOffset p b 0 := by
      change p b+(-p 0)=b-((p 0-0)-(p b-b))
      ring
    rw [he,Fin.coe_sub_iff_le.mpr (show cyclicOffset p b 0 ≤ b from le_of_lt hklt)]
    omega
  have hbnot : b ∉ nonzeroLowerOffsetDrops p (p 0) := by
    intro hi
    obtain ⟨hilow,hpne⟩ := Finset.mem_filter.mp hi
    have hback := (mem_descendingPositions _ _).mp (Finset.mem_filter.mp hilow).1
    have hfinish := hb.2.2.2.1
    rw [Fin.val_neg,ite_eq_right hpne,
      Fin.coe_sub_iff_le.mpr (show p b ≤ b from le_of_lt hback)] at hfinish
    have hp := (p b).isLt
    have hib := b.isLt
    omega
  have hc := Finset.card_le_card (Finset.insert_subset hbdesc (nonzero_lower_drops_subset p (p 0)))
  rw [Finset.card_insert_of_notMem hbnot] at hc
  have heq : thresholdPermutation p (p 0)=permutation p 0 := by
    apply Equiv.ext
    intro i
    change p i+(-p 0)=p i+(0-p 0)
    simp
  rw [heq] at hc
  change (nonzeroLowerOffsetDrops p (p 0)).card+1 ≤ height p 0 at hc
  have hhead := (rank_two_unpaid_higher_head p a hn hh hmin hR hunpaid).1
  omega

#print axioms rank_two_unpaid_head_drop_upper
end LX.AnchoredPhases
