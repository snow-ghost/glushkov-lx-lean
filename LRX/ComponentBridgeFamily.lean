import LRX.BridgeSequence

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

noncomputable def componentBridges (p : State n) (hcard : (componentRoots p).card=k+1) :
    List (Fin n × Fin n) := List.ofFn (bridgeEndpoints p hcard)

noncomputable def joinedComponents (p : State n) (hcard : (componentRoots p).card=k+1) : State n :=
  bridgeSequence p (componentBridges p hcard)

theorem component_bridges_valid (p : State n) (hcard : (componentRoots p).card=k+1) :
    ∀ uv ∈ componentBridges p hcard, ValidBridge p uv := by
  intro uv hu
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hu
  exact ordered_component_bridge_valid p hcard i

theorem component_bridges_separated (p : State n) (hcard : (componentRoots p).card=k+1) :
    SeparatedBridges (componentBridges p hcard) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  exact ordered_component_bridges_separated p hcard i j hij

theorem joined_components_prices (p : State n) (hcard : (componentRoots p).card=k+1) :
    FiniteRankOrder.Below p (joinedComponents p hcard) ∧
    (∑ i, |displacement (joinedComponents p hcard).symm i|)=
      (∑ i, |displacement p.symm i|)+2*(bridgeBudget (componentBridges p hcard) : ℤ) ∧
    inversionNumber (joinedComponents p hcard)+k=
      inversionNumber p+2*bridgeBudget (componentBridges p hcard) := by
  have he := bridge_sequence_prices p (componentBridges p hcard)
    (component_bridges_valid p hcard) (component_bridges_separated p hcard)
  simpa only [joinedComponents,componentBridges,List.length_ofFn] using he

theorem component_bridge_budget (p : State n) (hcard : (componentRoots p).card=k+1) :
    bridgeBudget (componentBridges p hcard) ≤ n-p.support.card+k := by
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
  have hsub : Finset.univ.biUnion gaps ⊆ p.supportᶜ := by
    intro x hx
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hi
    have he := (ordered_component_bridge_valid p hcard i).2.2.2 x hlo hhi
    apply Finset.mem_compl.mpr
    simpa only [Equiv.Perm.mem_support,not_not] using he
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis,Finset.card_compl,Fintype.card_fin] at hc
  have hwidth (i : Fin k) :
      (bridgeEndpoints p hcard i).2.val-(bridgeEndpoints p hcard i).1.val=(gaps i).card+1 := by
    have hlt := (ordered_component_bridge_valid p hcard i).1
    simp only [gaps,Fin.card_Ioo]
    omega
  have hb : bridgeBudget (componentBridges p hcard)=(∑ i, (gaps i).card)+k := by
    simp only [bridgeBudget,componentBridges,List.map_ofFn,List.sum_ofFn,Function.comp_def,hwidth,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega

#print axioms joined_components_prices
#print axioms component_bridge_budget
end LRX.FiniteCuts
