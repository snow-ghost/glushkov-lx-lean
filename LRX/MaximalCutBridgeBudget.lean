import LRX.BridgeInteriorCard

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- A non-unit exterior separator contains an isolated vertex unused by every bridge. -/
theorem exterior_isolated_outside_bridges (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (hw : 2 ≤ externalWidth p) :
    ∃ x ∈ isolatedVertices p, x ∉ bridgeInterior p hc := by
  classical
  have he := external_width_eq_outer hn p hc hk
  have ho := (joined_outer_ports hn p hc hk).1
  have hpos : 0 < (Finset.Icc (outerLeft p hc) (outerRight p hc))ᶜ.card := by
    rw [Finset.card_compl,Fintype.card_fin,Fin.card_Icc]
    have hr := (outerRight p hc).isLt
    omega
  obtain ⟨x,hx⟩ := Finset.card_pos.mp hpos
  have hout : x ∉ Finset.Icc (outerLeft p hc) (outerRight p hc) := Finset.mem_compl.mp hx
  have hiso : x ∈ isolatedVertices p := by
    apply (mem_isolated_vertices p x).mpr
    have hp := Finset.card_pos.mpr (component_set_nonempty p x)
    by_contra hh
    exact hout (Finset.mem_Icc.mpr (nontrivial_vertex_between_outer p hc x (by omega)))
  refine ⟨x,hiso,?_⟩
  intro hb
  exact hout (Finset.mem_Icc.mpr (bridge_interior_between_outer p hc x hb))

/-- A maximal zero cut supplies the strict bridge budget required by the 577 cutoff. -/
theorem maximal_cut_bridge_strict_budget (hn : 2 ≤ n) (p : State n)
    (hmax : MaximalZeroCut p) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (ha : 0 < (isolatedVertices p).card) :
    bridgeBudget (componentBridges p hc) ≤ (isolatedVertices p).card+k-1 := by
  classical
  by_cases hw : externalWidth p ≤ 1
  · have hb : bridgeBudget (componentBridges p hc) ≤ k := by
      simp only [bridgeBudget,componentBridges,List.map_ofFn,List.sum_ofFn,Function.comp_def]
      calc
        _ ≤ ∑ _i : Fin k, (1 : ℕ) := Finset.sum_le_sum (fun i _ =>
          (maximal_cut_bridge_width p hmax hc i).trans hw)
        _ = k := by simp
    omega
  · obtain ⟨x,hx,hnot⟩ := exterior_isolated_outside_bridges hn p hc hk (by omega)
    obtain ⟨hcard,hsub⟩ := bridge_interior_card p hc
    have hstrict : bridgeInterior p hc ⊂ isolatedVertices p := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨hsub,?_⟩
      intro he
      rw [he] at hnot
      exact hnot hx
    have hh := Finset.card_lt_card hstrict
    omega

/-- Both integer bridge premises of CoupledPeakCutoff, for the actual routed cut. -/
theorem maximal_cut_bridge_unpaid_bounds (hn : 2 ≤ n) (p : State n)
    (hmax : MaximalZeroCut p) (hc : (componentRoots p).card=k+1) (hk : 0 < k) :
    let a : ℤ := (isolatedVertices p).card
    let B : ℤ := bridgeBudget (componentBridges p hc)
    (a=0 → B ≤ (k : ℤ)) ∧ (1 ≤ a → B ≤ a+(k : ℤ)-1) := by
  dsimp only
  constructor
  · intro ha
    have hb := component_bridge_isolated_budget p hc
    omega
  · intro ha
    have hb := maximal_cut_bridge_strict_budget hn p hmax hc hk (by omega)
    omega

#print axioms external_width_eq_outer
#print axioms maximal_cut_bridge_strict_budget
#print axioms maximal_cut_bridge_unpaid_bounds
end LRX.FiniteCuts
