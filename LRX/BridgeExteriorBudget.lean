import LRX.TwoComponentPeakReduction

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- Bridge interiors and the exterior gap are disjoint sets of isolated
vertices. Counting them together retains the exterior-width contribution. -/
theorem bridge_plus_exterior_isolated_budget (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    bridgeBudget (componentBridges p hc)+externalWidth p ≤ (isolatedVertices p).card+k+1 := by
  classical
  let E := (Finset.Icc (outerLeft p hc) (outerRight p hc))ᶜ
  have hE : E ⊆ isolatedVertices p := by
    intro x hx
    apply (mem_isolated_vertices p x).mpr
    have hp := Finset.card_pos.mpr (component_set_nonempty p x)
    by_contra hh
    exact (Finset.mem_compl.mp hx) (Finset.mem_Icc.mpr
      (nontrivial_vertex_between_outer p hc x (by omega)))
  have hdis : Disjoint (bridgeInterior p hc) E := by
    apply Finset.disjoint_left.mpr
    intro x hx he
    exact (Finset.mem_compl.mp he) (Finset.mem_Icc.mpr (bridge_interior_between_outer p hc x hx))
  have hb := bridge_interior_card p hc
  have hsum := Finset.card_le_card (Finset.union_subset hb.2 hE)
  rw [Finset.card_union_of_disjoint hdis] at hsum
  have hcard : E.card=n-((outerRight p hc).val+1-(outerLeft p hc).val) := by
    simp only [E,Finset.card_compl,Fintype.card_fin,Fin.card_Icc]
  have he := external_width_eq_outer hn p hc hk
  have ho := (joined_outer_ports hn p hc hk).1
  have hr := (outerRight p hc).isLt
  omega

/-- For exactly two components the actual bridge is no wider than the
maximal exterior separator, so twice its width is at most a+2. -/
theorem two_component_twice_bridge_budget (hn : 2 ≤ n) (p : State n)
    (hmax : MaximalZeroCut p) (hc : (componentRoots p).card=1+1) :
    2*bridgeBudget (componentBridges p hc) ≤ (isolatedVertices p).card+2 := by
  have hsum := bridge_plus_exterior_isolated_budget hn p hc (by omega)
  have hb : bridgeBudget (componentBridges p hc) ≤ externalWidth p := by
    simp only [bridgeBudget,componentBridges,List.map_ofFn,List.sum_ofFn,Function.comp_def]
    calc
      _ ≤ ∑ _i : Fin 1, externalWidth p := Finset.sum_le_sum (fun i _ => maximal_cut_bridge_width p hmax hc i)
      _ = externalWidth p := by simp
  omega

#print axioms bridge_plus_exterior_isolated_budget
#print axioms two_component_twice_bridge_budget
end LRX.FiniteCuts
