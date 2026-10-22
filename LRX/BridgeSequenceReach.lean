import LRX.ComponentBridgeFamily

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem valid_bridge_moved_iff (p : State n) (uv : Fin n × Fin n) (hv : ValidBridge p uv)
    (i : Fin n) : (componentBridge p uv.1 uv.2).symm i ≠ i ↔ p.symm i ≠ i := by
  constructor
  · intro hnew
    by_contra h
    have he : p.symm i=i := by simpa using h
    have hiu : i ≠ uv.1 := by
      intro hi; subst i
      have hh := congrArg Fin.val he
      have := hv.2.1
      omega
    have hiv : i ≠ uv.2 := by
      intro hi; subst i
      have hh := congrArg Fin.val he
      have := hv.2.2.1
      omega
    exact hnew (by rw [component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hiu hiv,he])
  · exact component_bridge_moved p uv.1 uv.2 hv.1 (le_of_lt hv.2.1) (le_of_lt hv.2.2.1) i

theorem bridge_sequence_support (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs) :
    (bridgeSequence p xs).support=p.support := by
  induction xs generalizing p with
  | nil => rfl
  | cons uv xs ih =>
    rw [bridgeSequence,ih _ (valid_bridge_tail p uv xs hv hs) (List.pairwise_cons.mp hs).2]
    ext i
    rw [mem_support_inverse,mem_support_inverse]
    exact valid_bridge_moved_iff p uv (hv uv (by simp)) i

theorem bridge_sequence_preserves_reach (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs)
    {i j : Fin n} (hp : FiniteReach p i j) : FiniteReach (bridgeSequence p xs) i j := by
  induction xs generalizing p with
  | nil => exact hp
  | cons uv xs ih =>
    have hh := hv uv (by simp)
    exact ih _ (valid_bridge_tail p uv xs hv hs) (List.pairwise_cons.mp hs).2
      (component_bridge_preserves_reach p uv.1 uv.2 hh.1 (le_of_lt hh.2.1) (le_of_lt hh.2.2.1) hp)

theorem bridge_sequence_cross_reach (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs)
    (uv : Fin n × Fin n) (huv : uv ∈ xs) :
    FiniteReach (bridgeSequence p xs) uv.1 uv.2 ∧ FiniteReach (bridgeSequence p xs) uv.2 uv.1 := by
  induction xs generalizing p with
  | nil => simp at huv
  | cons xy xs ih =>
    have hvt := valid_bridge_tail p xy xs hv hs
    have hst := (List.pairwise_cons.mp hs).2
    rcases List.mem_cons.mp huv with he | he
    · subst uv
      have hh := hv xy (by simp)
      obtain ⟨hf,hb⟩ := bridge_cross_edges p xy.1 xy.2 hh.1 (le_of_lt hh.2.1) (le_of_lt hh.2.2.1)
      exact ⟨bridge_sequence_preserves_reach _ xs hvt hst (Relation.ReflTransGen.single hf),
        bridge_sequence_preserves_reach _ xs hvt hst (Relation.ReflTransGen.single hb)⟩
    · exact ih _ hvt hst he

theorem bridge_sequence_half_load (p : State n) (xs : List (Fin n × Fin n))
    (hv : ∀ xy ∈ xs, ValidBridge p xy) (hs : SeparatedBridges xs) (e : ℕ) :
    halfLoad p.symm e ≤ halfLoad (bridgeSequence p xs).symm e := by
  induction xs generalizing p with
  | nil => exact le_rfl
  | cons uv xs ih =>
    have hh := hv uv (by simp)
    have hb := component_bridge_half_load p uv.1 uv.2 hh.1 (le_of_lt hh.2.1) (le_of_lt hh.2.2.1) e
    have ht := ih _ (valid_bridge_tail p uv xs hv hs) (List.pairwise_cons.mp hs).2
    change halfLoad p.symm e ≤ halfLoad (bridgeSequence (componentBridge p uv.1 uv.2) xs).symm e
    omega

#print axioms bridge_sequence_support
#print axioms bridge_sequence_preserves_reach
#print axioms bridge_sequence_cross_reach
#print axioms bridge_sequence_half_load
end LRX.FiniteCuts
