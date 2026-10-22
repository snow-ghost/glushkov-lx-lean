import LRX.RankNeighborCutGeometry

namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem shift_support_carrier (p : State n) (c : Fin n) :
    (FiniteCuts.shiftConjugate p c.val).support=shiftCarrier p.support c := by
  ext j
  have h1 := FiniteCuts.shift_support p c (j+c)
  have h2 := mem_shift_carrier p.support c (j+c)
  simpa only [add_sub_cancel_right] using h1.trans h2.symm

theorem shift_carrier_card (S : Finset (Fin n)) (c : Fin n) : (shiftCarrier S c).card=S.card := by
  rw [shiftCarrier,Finset.card_image_of_injective _ (shift_injective c)]

theorem ordered_gap_becomes_extreme (S : Finset (Fin n)) (a b : Fin n)
    (hab : a.val < b.val) (hgap : RankAdjacent S a b) :
    ExtremePair (shiftCarrier S b) (a-b) (b-b) := by
  refine ⟨(mem_shift_carrier S b a).mpr hgap.1,(mem_shift_carrier S b b).mpr hgap.2.1,
    fun h => hgap.2.2.1 (shift_injective b h),?_⟩
  intro z hz
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
  simp only [sub_self,Fin.val_zero,Nat.min_zero,Nat.max_zero]
  refine ⟨Nat.zero_le _,?_⟩
  have hnot := hgap.2.2.2 i hi
  simp only [min_eq_left (le_of_lt hab),max_eq_right (le_of_lt hab)] at hnot
  simp only [shift_value]
  split_ifs <;> omega

theorem adjacent_small_is_extreme (S : Finset (Fin n)) (x y : Fin n)
    (h : RankAdjacent S x y) (hc : S.card ≤ 2) : ExtremePair S x y := by
  classical
  have hsub : ({x,y} : Finset (Fin n)) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert,Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact h.1
    · exact h.2.1
  have heq : ({x,y} : Finset (Fin n))=S := by
    apply Finset.eq_of_subset_of_card_le hsub
    simpa only [Finset.card_pair h.2.2.1] using hc
  refine ⟨h.1,h.2.1,h.2.2.1,?_⟩
  intro z hz
  rw [← heq] at hz
  simp only [Finset.mem_insert,Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> omega

#print axioms ordered_gap_becomes_extreme
end LRX.ZeroGap
