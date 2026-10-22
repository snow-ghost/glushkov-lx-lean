import LRX.FiniteBridgeLoad

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

abbrev FiniteReach (p : State n) := Relation.ReflTransGen
  (BufferProgram.ServiceEdge p (displacement p.symm))

theorem component_bridge_moved (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (i : Fin n) (hi : p.symm i ≠ i) : (componentBridge p u v).symm i ≠ i := by
  rw [component_bridge_inverse]
  by_cases hiu : i=u
  · subst i
    rw [Equiv.swap_apply_left]
    intro he
    have := congrArg Fin.val he
    omega
  · by_cases hiv : i=v
    · subst i
      rw [Equiv.swap_apply_right]
      intro he
      have := congrArg Fin.val he
      omega
    · simpa only [Equiv.swap_apply_of_ne_of_ne hiu hiv] using hi

theorem bridge_cross_edges (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val) :
    BufferProgram.ServiceEdge (componentBridge p u v) (displacement (componentBridge p u v).symm) u v ∧
    BufferProgram.ServiceEdge (componentBridge p u v) (displacement (componentBridge p u v).symm) v u := by
  constructor
  · right
    refine ⟨?_,0,?_,?_⟩
    · change (componentBridge p u v).symm v ≠ v
      rw [component_bridge_inverse,Equiv.swap_apply_right]
      intro he; have := congrArg Fin.val he; omega
    · simp only [displacement,component_bridge_inverse,Equiv.swap_apply_left,zero_mul,add_zero]
      omega
    · simp only [displacement,component_bridge_inverse,Equiv.swap_apply_left,zero_mul,add_zero]
      omega
  · right
    refine ⟨?_,0,?_,?_⟩
    · change (componentBridge p u v).symm u ≠ u
      rw [component_bridge_inverse,Equiv.swap_apply_left]
      intro he; have := congrArg Fin.val he; omega
    · simp only [displacement,component_bridge_inverse,Equiv.swap_apply_right,zero_mul,add_zero]
      omega
    · simp only [displacement,component_bridge_inverse,Equiv.swap_apply_right,zero_mul,add_zero]
      omega

theorem bridge_preserves_touch_reach (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (i j : Fin n) (hj : p.symm j ≠ j)
    (ht : BufferProgram.Touches n (i : ℤ) (displacement p.symm i) (j : ℤ)) :
    FiniteReach (componentBridge p u v) i j := by
  have hm := component_bridge_moved p u v huv ha hb j hj
  obtain ⟨t,hl,hh⟩ := ht
  obtain ⟨huv',hvu'⟩ := bridge_cross_edges p u v huv ha hb
  by_cases hiu : i=u
  · subst i
    apply (Relation.ReflTransGen.single huv').trans
    apply Relation.ReflTransGen.single
    right
    refine ⟨hm,t,?_,?_⟩ <;>
      simp only [displacement,component_bridge_inverse,Equiv.swap_apply_right] at hl hh ⊢ <;> omega
  · by_cases hiv : i=v
    · subst i
      apply (Relation.ReflTransGen.single hvu').trans
      apply Relation.ReflTransGen.single
      right
      refine ⟨hm,t,?_,?_⟩ <;>
        simp only [displacement,component_bridge_inverse,Equiv.swap_apply_left] at hl hh ⊢ <;> omega
    · apply Relation.ReflTransGen.single
      right
      refine ⟨hm,t,?_,?_⟩ <;>
        simpa only [displacement,component_bridge_inverse,Equiv.swap_apply_of_ne_of_ne hiu hiv] using
          (by assumption)

theorem bridge_preserves_inverse_step (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val) (i : Fin n) :
    FiniteReach (componentBridge p u v) i (p.symm i) := by
  by_cases hi : p.symm i=i
  · simpa only [hi] using (Relation.ReflTransGen.refl : FiniteReach (componentBridge p u v) i i)
  · have hj : p.symm (p.symm i) ≠ p.symm i := by
      intro he
      exact hi (p.symm.injective he)
    apply bridge_preserves_touch_reach p u v huv ha hb i (p.symm i) hj
    refine ⟨0,?_,?_⟩ <;> simp [displacement]

theorem bridge_preserves_service_edge (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    (i j : Fin n) (he : BufferProgram.ServiceEdge p (displacement p.symm) i j) :
    FiniteReach (componentBridge p u v) i j := by
  rcases he with hcycle | ⟨hj,ht⟩
  · obtain ⟨t,ht⟩ := hcycle.exists_nat_pow_eq
    have hh : ∀ t : ℕ, FiniteReach (componentBridge p u v) i (((p⁻¹)^t) i) := by
      intro t
      induction t with
      | zero => simpa using (Relation.ReflTransGen.refl : FiniteReach (componentBridge p u v) i i)
      | succ t ih =>
        rw [pow_succ',Equiv.Perm.mul_apply]
        exact ih.trans (bridge_preserves_inverse_step p u v huv ha hb _)
    simpa only [ht] using hh t
  · exact bridge_preserves_touch_reach p u v huv ha hb i j hj ht

theorem component_bridge_preserves_reach (p : State n) (u v : Fin n) (huv : u.val < v.val)
    (ha : (p.symm u).val ≤ u.val) (hb : v.val ≤ (p.symm v).val)
    {i j : Fin n} (hr : FiniteReach p i j) : FiniteReach (componentBridge p u v) i j := by
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | tail h he ih => exact ih.trans (bridge_preserves_service_edge p u v huv ha hb _ _ he)

#print axioms component_bridge_preserves_reach
end LRX.FiniteCuts
