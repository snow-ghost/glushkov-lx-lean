import LRX.FiniteGapPartition

/-! Exact cardinality and sum identities for the partition into finite gaps. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

theorem positions_image (S : Finset (Fin n)) (a : Fin n) :
    positions S a=Finset.univ.image (FiniteWindow.embed (window S a)) := by
  ext i
  simp only [positions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  exact FiniteWindow.contains_iff (window S a) i

theorem positions_card (S : Finset (Fin n)) (a : Fin n) : (positions S a).card=size S a := by
  rw [positions_image,Finset.card_image_of_injective _ (FiniteWindow.embed_injective _)]
  simp

theorem sum_positions (S : Finset (Fin n)) (a : Fin n) (f : Fin n → ℤ) :
    (∑ i ∈ positions S a, f i)=∑ j : Fin (size S a), f (FiniteWindow.embed (window S a) j) := by
  rw [positions_image]
  exact Finset.sum_image (fun _ _ _ _ h => FiniteWindow.embed_injective _ h)

theorem sum_gap_sizes (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S) :
    (∑ a ∈ S, size S a)=n-S.card := by
  have h := Finset.card_biUnion (gaps_disjoint S)
  rw [union_gaps S hzero] at h
  simpa only [positions_card,Finset.card_compl,Fintype.card_fin] using h.symm

theorem sum_gap_values (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S) (f : Fin n → ℤ) :
    (∑ i ∈ Sᶜ, f i)=∑ a ∈ S, ∑ j : Fin (size S a), f (FiniteWindow.embed (window S a) j) := by
  rw [← union_gaps S hzero,Finset.sum_biUnion (gaps_disjoint S)]
  exact Finset.sum_congr rfl (fun a _ => sum_positions S a f)

theorem total_sum (S : Finset (Fin n)) (hzero : (0 : Fin n) ∈ S) (f : Fin n → ℤ) :
    (∑ i : Fin n, f i)=(∑ i ∈ S, f i)+
      ∑ a ∈ S, ∑ j : Fin (size S a), f (FiniteWindow.embed (window S a) j) := by
  have h := Finset.sum_add_sum_compl S f
  rw [sum_gap_values S hzero f] at h
  exact h.symm

#print axioms sum_gap_sizes
#print axioms total_sum
end LRX.FiniteGaps
