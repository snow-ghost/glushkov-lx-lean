import LRX.IsolatedGapWidths
import LRX.MaximumSeparatorBound

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

noncomputable def bridgeInterior (p : State n) (hc : (componentRoots p).card=k+1) : Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion (fun i : Fin k =>
    Finset.Ioo (bridgeEndpoints p hc i).1 (bridgeEndpoints p hc i).2)

/-- The exact bridge budget counts bridge interiors once, plus one per bridge. -/
theorem bridge_interior_card (p : State n) (hc : (componentRoots p).card=k+1) :
    bridgeBudget (componentBridges p hc) = (bridgeInterior p hc).card+k ∧
      bridgeInterior p hc ⊆ isolatedVertices p := by
  classical
  let gaps : Fin k → Finset (Fin n) := fun i =>
    Finset.Ioo (bridgeEndpoints p hc i).1 (bridgeEndpoints p hc i).2
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) gaps := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hix,hxi⟩ := Finset.mem_Ioo.mp hx
    obtain ⟨hjx,hxj⟩ := Finset.mem_Ioo.mp hy
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hlt : i.val < j.val
    · have hh := ordered_component_bridges_separated p hc i j hlt
      change (bridgeEndpoints p hc i).1.val < x.val at hix
      change x.val < (bridgeEndpoints p hc i).2.val at hxi
      change (bridgeEndpoints p hc j).1.val < x.val at hjx
      omega
    · have hh := ordered_component_bridges_separated p hc j i (by omega)
      change (bridgeEndpoints p hc i).1.val < x.val at hix
      change x.val < (bridgeEndpoints p hc j).2.val at hxj
      omega
  have hwidth (i : Fin k) :
      (bridgeEndpoints p hc i).2.val-(bridgeEndpoints p hc i).1.val = (gaps i).card+1 := by
    have hh := (ordered_component_bridge_valid p hc i).1
    simp only [gaps,Fin.card_Ioo]
    omega
  constructor
  · change bridgeBudget (componentBridges p hc)=(Finset.univ.biUnion gaps).card+k
    rw [Finset.card_biUnion hdis]
    simp only [bridgeBudget,componentBridges,List.map_ofFn,List.sum_ofFn,Function.comp_def,hwidth,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  · intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hi
    exact (mem_isolated_vertices p x).mpr (ordered_bridge_gap_singleton p hc i x hlo hhi)

/-- Bridge interiors lie inside the original support hull. -/
theorem bridge_interior_between_outer (p : State n) (hc : (componentRoots p).card=k+1)
    (x : Fin n) (hx : x ∈ bridgeInterior p hc) :
    (outerLeft p hc).val ≤ x.val ∧ x.val ≤ (outerRight p hc).val := by
  classical
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hi
  have hv := ordered_component_bridge_valid p hc i
  have hvleft := hv.2.1
  have hvright := hv.2.2.1
  have hu : p.symm (bridgeEndpoints p hc i).1 ≠ (bridgeEndpoints p hc i).1 := by
    intro he
    have hh := congrArg Fin.val he
    omega
  have hw : p.symm (bridgeEndpoints p hc i).2 ≠ (bridgeEndpoints p hc i).2 := by
    intro he
    have hh := congrArg Fin.val he
    omega
  have hb := moving_between_outer p hc _ hu
  have hb' := moving_between_outer p hc _ hw
  change (bridgeEndpoints p hc i).1.val < x.val at hlo
  change x.val < (bridgeEndpoints p hc i).2.val at hhi
  constructor <;> omega

#print axioms bridge_interior_card
end LRX.FiniteCuts
