import LRX.PortRoute
import Mathlib.Data.List.Sort

/-! A monotone traversal of service ports pays at most the length of the
containing interval. Services may be reordered because their targets commute. -/
namespace LRX.RotationWords
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem short_move_le_difference (s t : Fin n) (h : s.val ≤ t.val) :
    min (t-s).val (n-(t-s).val) ≤ t.val-s.val := by
  rw [Fin.sub_val_of_le h]
  exact min_le_left _ _

theorem ordered_walk_cost (s t : Fin n) (services : List (ClosedService n))
    (hst : s.val ≤ t.val)
    (horder : services.Pairwise (fun a b => a.port.val ≤ b.port.val))
    (hrange : ∀ a ∈ services, s.val ≤ a.port.val ∧ a.port.val ≤ t.val) :
    walkCost s t services ≤ t.val-s.val := by
  induction services generalizing s with
  | nil => exact short_move_le_difference s t hst
  | cons a rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp horder
    have ha := hrange a (by simp)
    have hw := ih a.port ha.2 htail (fun r hr =>
      ⟨hhead r hr, (hrange r (by simp [hr])).2⟩)
    have hm := short_move_le_difference s a.port ha.1
    simp only [walkCost]
    omega

theorem exists_ordered_services (services : List (ClosedService n)) :
    ∃ ordered : List (ClosedService n), services.Perm ordered ∧
      ordered.Pairwise (fun a b => a.port.val ≤ b.port.val) := by
  let le : ClosedService n → ClosedService n → Bool := fun a b => a.port.val ≤ b.port.val
  refine ⟨services.mergeSort le, (List.mergeSort_perm services le).symm, ?_⟩
  simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using List.pairwise_mergeSort (le := le)
    (fun a b c hab hbc => by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_trans (by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using hab) (by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using hbc))
    (fun a b => by simpa only [le, Bool.or_eq_true, decide_eq_true_eq] using Nat.le_total a.port.val b.port.val) services

/-- Literal route with a bounded cursor cost through pairwise disjoint targets. -/
theorem interval_route (s t : Fin n) (services : List (ClosedService n))
    (hst : s.val ≤ t.val)
    (hdis : services.Pairwise (fun a b => Disjoint a.target.support b.target.support))
    (hrange : ∀ a ∈ services, s.val ≤ a.port.val ∧ a.port.val ≤ t.val) :
    ∃ w : List Letter,
      eval w=(rotation s)⁻¹*(services.map ClosedService.target).prod*rotation t ∧
      w.length ≤ (services.map (fun a => a.word.length)).sum+(t.val-s.val) := by
  obtain ⟨ordered, hp, ho⟩ := exists_ordered_services services
  refine ⟨route s t ordered, ?_, ?_⟩
  · rw [← route_permuted s t services ordered hdis hp, route_eval]
  · rw [route_length, ← (hp.map (fun a => a.word.length)).sum_eq]
    exact Nat.add_le_add_left (ordered_walk_cost s t ordered hst ho
      (fun a ha => hrange a (hp.mem_iff.mpr ha))) _

#print axioms ordered_walk_cost
#print axioms interval_route
end LRX.RotationWords
