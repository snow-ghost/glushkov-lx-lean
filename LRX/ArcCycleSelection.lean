import LRX.ArcPacketServiceFamily
import LRX.TwoArcServiceWord

/-! Assign each outside cycle to one complementary arc containing its
positive service port. The two selected lists partition the actual cycles. -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

theorem arc_not_forward_is_reverse (start finish port : Fin n) (hne : start ≠ finish)
    (hnot : ¬(arcCoordinate true start port).val ≤ (arcCoordinate true start finish).val) :
    (arcCoordinate false start port).val ≤ (arcCoordinate false start finish).val := by
  have hp : start ≠ port := by
    intro h
    subst port
    simp [arcCoordinate] at hnot
  have hs := complementary_arc_lengths start finish hne
  have ht := complementary_arc_lengths start port hp
  omega
end LRX.RotationWords

namespace LRX.ZeroGap
open RotationWords
variable {n : ℕ} [NeZero n]

theorem outside_list_disjoint {p : State n} {d : Fin n → ℤ} (cycles : List (State n))
    (hnodup : cycles.Nodup) (hc : ∀ q ∈ cycles, q ∈ outsideCycles p d 0) :
    cycles.Pairwise Equiv.Perm.Disjoint := by
  apply hnodup.imp_of_mem
  intro a b ha hb hab
  exact (Equiv.Perm.cycleFactorsFinset_pairwise_disjoint (p⁻¹))
    (Finset.mem_filter.mp (hc a ha)).1 (Finset.mem_filter.mp (hc b hb)).1 hab

theorem arc_cycle_partition (p : State n) (d : Fin n → ℤ) (start finish : Fin n)
    (hne : start ≠ finish) :
    ∃ cycles : Bool → List (State n),
      (∀ dir, (cycles dir).Pairwise Equiv.Perm.Disjoint) ∧
      (∀ dir q, q ∈ cycles dir → q ∈ outsideCycles p d 0) ∧
      (∀ dir q, q ∈ cycles dir → (arcCoordinate dir start (cycleRoot q)).val ≤
        (arcCoordinate dir start finish).val) ∧
      (cycles true).length+(cycles false).length=(outsideCycles p d 0).card := by
  classical
  let all := (outsideCycles p d 0).toList
  let forward : State n → Bool := fun q => decide
    ((arcCoordinate true start (cycleRoot q)).val ≤ (arcCoordinate true start finish).val)
  let selected : Bool → List (State n) := fun dir =>
    if dir then all.filter forward else all.filter (fun q => !forward q)
  have hmem : ∀ dir q, q ∈ selected dir → q ∈ outsideCycles p d 0 := by
    intro dir q hq
    cases dir <;> simp only [selected,Bool.false_eq_true,ite_false,ite_true,List.mem_filter] at hq <;>
      exact Finset.mem_toList.mp hq.1
  have hnodup : ∀ dir, (selected dir).Nodup := by
    intro dir
    cases dir <;> exact (Finset.nodup_toList _).filter _
  refine ⟨selected,fun dir => outside_list_disjoint _ (hnodup dir) (hmem dir),hmem,?_,?_⟩
  · intro dir q hq
    cases dir
    · apply arc_not_forward_is_reverse start finish (cycleRoot q) hne
      intro h
      have hbad := (List.mem_filter.mp hq).2
      have hf : forward q=true := decide_eq_true_eq.mpr h
      rw [hf] at hbad
      contradiction
    · exact of_decide_eq_true (List.mem_filter.mp hq).2
  · have hsplit : ∀ (xs : List (State n)) (f : State n → Bool),
        (xs.filter f).length+(xs.filter (fun q => !f q)).length=xs.length := by
      intro xs f
      induction xs with
      | nil => rfl
      | cons q rest ih => cases hf : f q <;> simp [hf] <;> omega
    simpa only [selected,ite_true,Bool.false_eq_true,ite_false,all,Finset.length_toList] using hsplit all forward

#print axioms arc_cycle_partition
end LRX.ZeroGap
