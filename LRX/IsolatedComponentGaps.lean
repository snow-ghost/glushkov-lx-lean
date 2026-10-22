import LRX.ComponentRootCorrespondence

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

/-- Every vertex strictly between consecutive components is its own load component. -/
theorem consecutive_component_gap_singleton (p : State n) (a b : Fin n)
    (ha : a ∈ componentRoots p) (hb : b ∈ componentRoots p)
    (hnext : ∀ c ∈ componentRoots p, ¬(a.val < c.val ∧ c.val < b.val))
    (x : Fin n) (hax : (componentRight p a).val < x.val)
    (hxb : x.val < (componentLeft p b).val) : (componentSet p x).card = 1 := by
  have hpos := Finset.card_pos.mpr (component_set_nonempty p x)
  by_contra h
  have hsize : 2 ≤ (componentSet p x).card := by omega
  let c := componentLeft p x
  have hc : c ∈ componentRoots p := nontrivial_component_left_root p x hsize
  have hcx := CycleFootprint.load_path_symm _ (component_left_path p x)
  have hclo := component_left_bound p c x hcx
  have hchi := component_right_bound p c x hcx
  have hac : a.val < c.val := by
    by_contra hh
    by_cases he : c = a
    · rw [he] at hchi
      omega
    · have hne : c.val ≠ a.val := fun h => he (Fin.ext h)
      have horder := ordered_component_roots p hc ha (by omega)
      have habound := component_left_bound p a (componentRight p a) (component_right_path p a)
      omega
  have hcb : c.val < b.val := by
    by_contra hh
    by_cases he : c = b
    · rw [he] at hclo
      omega
    · have hne : c.val ≠ b.val := fun h => he (Fin.ext h)
      have horder := ordered_component_roots p hb hc (by omega)
      have hbbound := component_left_bound p b (componentRight p b) (component_right_path p b)
      omega
  exact hnext c hc ⟨hac,hcb⟩

theorem ordered_bridge_gap_singleton (p : State n) (hcard : (componentRoots p).card = k+1)
    (i : Fin k) (x : Fin n)
    (hlo : (bridgeEndpoints p hcard i).1.val < x.val)
    (hhi : x.val < (bridgeEndpoints p hcard i).2.val) : (componentSet p x).card = 1 := by
  let e := componentOrder p hcard
  apply consecutive_component_gap_singleton p (e i.castSucc) (e i.succ)
    (component_order_mem p hcard i.castSucc) (component_order_mem p hcard i.succ) ?_ x hlo hhi
  intro c hc hbetween
  obtain ⟨j,hj⟩ := component_order_surjective p hcard c hc
  change e j = c at hj
  rw [← hj] at hbetween
  have hleft := e.strictMono.lt_iff_lt.mp hbetween.1
  have hright := e.strictMono.lt_iff_lt.mp hbetween.2
  change i.val < j.val at hleft
  change j.val < i.val+1 at hright
  omega

noncomputable def isolatedVertices (p : State n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => (componentSet p i).card = 1)

@[simp] theorem mem_isolated_vertices (p : State n) (i : Fin n) :
    i ∈ isolatedVertices p ↔ (componentSet p i).card = 1 := by
  classical
  simp [isolatedVertices]

/-- A singleton component's vertex is fixed, although fixed vertices need not be isolated. -/
theorem isolated_vertex_fixed (p : State n) (i : Fin n) (hi : i ∈ isolatedVertices p) : p i = i := by
  have hc : (componentSet p i).card ≤ 1 := by rw [(mem_isolated_vertices p i).mp hi]
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have he : p.symm i = i := (Finset.card_le_one.mp hc) _
    ((CycleFootprint.mem_component _ _ _).mpr (CycleFootprint.arrow_target_load_path hd i)) _
    ((CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl)
  have h := congrArg p he
  simpa only [Equiv.apply_symm_apply] using h.symm

#print axioms ordered_bridge_gap_singleton
#print axioms isolated_vertex_fixed
end LRX.FiniteCuts
