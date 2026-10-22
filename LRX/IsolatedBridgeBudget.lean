import LRX.IsolatedComponentGaps

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- Isolated vertices enumerate singleton component blocks without multiplicity. -/
theorem isolated_vertices_image (p : State n) :
    (isolatedVertices p).image (componentSet p) = singletonSuffixComponents p 0 := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_image.mpr ⟨i,by simp,rfl⟩,(mem_isolated_vertices p i).mp hi⟩
  · intro hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hC
    exact Finset.mem_image.mpr ⟨i,(mem_isolated_vertices p i).mpr hsize,rfl⟩

theorem isolated_vertices_card (p : State n) :
    (isolatedVertices p).card = (singletonSuffixComponents p 0).card := by
  classical
  rw [← isolated_vertices_image]
  symm
  apply Finset.card_image_iff.mpr
  intro i hi j hj he
  have hc : (componentSet p i).card ≤ 1 := by rw [(mem_isolated_vertices p i).mp hi]
  apply (Finset.card_le_one.mp hc)
  · exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl
  · rw [he]
    exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl

/-- The actual bridge budget depends only on isolated vertices and the number
of bridges; fixed positions inside nontrivial components are not charged. -/
theorem component_bridge_isolated_budget (p : State n) (hcard : (componentRoots p).card = k+1) :
    bridgeBudget (componentBridges p hcard) ≤ (isolatedVertices p).card+k := by
  classical
  let gaps : Fin k → Finset (Fin n) := fun i =>
    Finset.Ioo (bridgeEndpoints p hcard i).1 (bridgeEndpoints p hcard i).2
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin k))) gaps := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨hix,hxi⟩ := Finset.mem_Ioo.mp hx
    obtain ⟨hjx,hxj⟩ := Finset.mem_Ioo.mp hy
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    by_cases hlt : i.val < j.val
    · have hsep := ordered_component_bridges_separated p hcard i j hlt
      change (bridgeEndpoints p hcard i).1.val < x.val at hix
      change x.val < (bridgeEndpoints p hcard i).2.val at hxi
      change (bridgeEndpoints p hcard j).1.val < x.val at hjx
      omega
    · have hsep := ordered_component_bridges_separated p hcard j i (by omega)
      change (bridgeEndpoints p hcard i).1.val < x.val at hix
      change x.val < (bridgeEndpoints p hcard j).2.val at hxj
      omega
  have hsub : Finset.univ.biUnion gaps ⊆ isolatedVertices p := by
    intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hi
    exact (mem_isolated_vertices p x).mpr (ordered_bridge_gap_singleton p hcard i x hlo hhi)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hc
  have hwidth (i : Fin k) :
      (bridgeEndpoints p hcard i).2.val-(bridgeEndpoints p hcard i).1.val = (gaps i).card+1 := by
    have hlt := (ordered_component_bridge_valid p hcard i).1
    simp only [gaps,Fin.card_Ioo]
    omega
  have hb : bridgeBudget (componentBridges p hcard) = (∑ i, (gaps i).card)+k := by
    simp only [bridgeBudget,componentBridges,List.map_ofFn,List.sum_ofFn,Function.comp_def,hwidth,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega

theorem component_bridge_singleton_budget (p : State n) (hcard : (componentRoots p).card = k+1) :
    bridgeBudget (componentBridges p hcard) ≤ (singletonSuffixComponents p 0).card+k := by
  rw [← isolated_vertices_card]
  exact component_bridge_isolated_budget p hcard

#print axioms isolated_vertices_card
#print axioms component_bridge_singleton_budget
end LRX.FiniteCuts
