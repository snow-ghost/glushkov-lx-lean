import LRX.IsolatedBridgeBudget

namespace LRX.FiniteCuts
variable {n k : ℕ} [NeZero n]

/-- Every vertex of a nontrivial load component lies within the outer roots. -/
theorem nontrivial_vertex_between_outer (p : State n) (hc : (componentRoots p).card = k+1)
    (x : Fin n) (hx : 2 ≤ (componentSet p x).card) :
    (outerLeft p hc).val ≤ x.val ∧ x.val ≤ (outerRight p hc).val := by
  let e := componentOrder p hc
  let a := componentLeft p x
  have ha : a ∈ componentRoots p := nontrivial_component_left_root p x hx
  have hax := CycleFootprint.load_path_symm _ (component_left_path p x)
  obtain ⟨j,hj⟩ := component_order_surjective p hc a ha
  change CycleFootprint.LoadPath (displacement p.symm) a x at hax
  rw [← hj] at hax
  have hlo := component_left_bound p (e j) x hax
  have hhi := component_right_bound p (e j) x hax
  constructor
  · by_cases hz : j = 0
    · simpa only [hz,e,outerLeft] using hlo
    · have hjpos : (0 : Fin (k+1)) < j := by
        change 0 < j.val
        have hh : j.val ≠ 0 := fun h => hz (Fin.ext h)
        omega
      have hh := ordered_component_roots p (component_order_mem p hc 0)
        (component_order_mem p hc j) (e.strictMono hjpos)
      have hb := component_left_bound p (e 0) (componentRight p (e 0)) (component_right_path p (e 0))
      change (componentRight p (e 0)).val < (componentLeft p (e j)).val at hh
      change (componentLeft p (e 0)).val ≤ x.val
      omega
  · by_cases hz : j = Fin.last k
    · simpa only [hz,e,outerRight] using hhi
    · have hjlt : j < Fin.last k := by
        change j.val < k
        have hh : j.val ≠ k := fun h => hz (Fin.ext h)
        have := j.isLt
        omega
      have hh := ordered_component_roots p (component_order_mem p hc j)
        (component_order_mem p hc (Fin.last k)) (e.strictMono hjlt)
      have hb := component_right_bound p (e (Fin.last k)) (componentLeft p (e (Fin.last k)))
        (component_left_path p (e (Fin.last k)))
      change (componentRight p (e j)).val < (componentLeft p (e (Fin.last k))).val at hh
      change x.val ≤ (componentRight p (e (Fin.last k))).val
      omega

/-- The exterior gap contains only isolated load vertices. -/
theorem outer_gap_isolated_budget (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card = k+1) (hk : 0 < k) :
    n+(outerLeft p hc).val-(outerRight p hc).val-1 ≤ (isolatedVertices p).card := by
  classical
  have hsub : (Finset.Icc (outerLeft p hc) (outerRight p hc))ᶜ ⊆ isolatedVertices p := by
    intro x hx
    apply (mem_isolated_vertices p x).mpr
    have hpos := Finset.card_pos.mpr (component_set_nonempty p x)
    by_contra hh
    have hsize : 2 ≤ (componentSet p x).card := by omega
    have hb := nontrivial_vertex_between_outer p hc x hsize
    exact (Finset.mem_compl.mp hx) (Finset.mem_Icc.mpr hb)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_compl,Fintype.card_fin,Fin.card_Icc] at hh
  have horder := (joined_outer_ports hn p hc hk).1
  have hr := (outerRight p hc).isLt
  omega

/-- Each actual bridge's internal vertices are counted by the isolated set. -/
theorem bridge_gap_isolated_width (p : State n) (hc : (componentRoots p).card = k+1) (i : Fin k) :
    (bridgeEndpoints p hc i).2.val-(bridgeEndpoints p hc i).1.val ≤ (isolatedVertices p).card+1 := by
  classical
  have hsub : Finset.Ioo (bridgeEndpoints p hc i).1 (bridgeEndpoints p hc i).2 ⊆ isolatedVertices p := by
    intro x hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hx
    exact (mem_isolated_vertices p x).mpr (ordered_bridge_gap_singleton p hc i x hlo hhi)
  have hh := Finset.card_le_card hsub
  rw [Fin.card_Ioo] at hh
  omega

#print axioms outer_gap_isolated_budget
#print axioms bridge_gap_isolated_width
end LRX.FiniteCuts
