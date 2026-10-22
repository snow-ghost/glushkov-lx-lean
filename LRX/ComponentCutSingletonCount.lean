import LRX.MaximalCutBridgeBudget
import LRX.PrefixComponentParameters
import LRX.ComponentCutExtraction

namespace LRX.FiniteCuts
open RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n k : ℕ} [NeZero n]

/-- Zero-cut recentering at a component boundary preserves the actual isolated count. -/
theorem component_cut_isolated_card (p : State n) (root : Fin n) :
    (isolatedVertices (localTarget p 0 (componentLeft p root))).card = (isolatedVertices p).card := by
  classical
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hcards := (component_recenter_cut p root).2
  change (isolatedVertices q).card = (isolatedVertices p).card
  apply Finset.card_bij (fun i _ => i+r)
  · intro i hi
    apply (mem_isolated_vertices p _).mpr
    have hh := (mem_isolated_vertices q i).mp hi
    have hc := hcards i
    change (componentSet q i).card = (componentSet p (i+r)).card at hc
    omega
  · intro i _ j _ hij
    exact add_right_cancel hij
  · intro j hj
    refine ⟨j-r,?_,by simp⟩
    apply (mem_isolated_vertices q _).mpr
    have hh := (mem_isolated_vertices p j).mp hj
    have hc := hcards (j-r)
    change (componentSet q (j-r)).card = (componentSet p (j-r+r)).card at hc
    rw [sub_add_cancel] at hc
    omega

/-- The C7 singleton count at the large-component cut equals the isolated count
at the original routed cut, even when only the latter is maximal. -/
theorem component_cut_singleton_count (p : State n) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    (singletonSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card = (isolatedVertices p).card := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  let L := (componentSet p root).card
  have hzero : (componentSet q 0).card = L := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    have he : componentSet p root = componentSet p r :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card = (componentSet p r).card at h
    rwa [← he] at h
  have hpref (i : Fin n) : i ∈ componentSet q 0 ↔ i.val < L := by
    rw [zero_component_prefix,hzero]
  have hs := prefix_singleton_components q L (by omega) hpref
  change (singletonSuffixComponents q L).card = (isolatedVertices p).card
  rw [← hs,← isolated_vertices_card]
  exact component_cut_isolated_card p root

/-- The two bridge premises of the 577 cutoff use the original maximal-cut
word and the actual singleton parameter at the normalized component cut. -/
theorem maximal_bridge_bounds_at_component_cut (hn : 2 ≤ n) (p : State n)
    (hmax : MaximalZeroCut p) (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (root : Fin n) (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let a : ℤ := (singletonSuffixComponents q (componentSet p root).card).card
    let B : ℤ := bridgeBudget (componentBridges p hc)
    (a=0 → B ≤ (k : ℤ)) ∧ (1 ≤ a → B ≤ a+(k : ℤ)-1) := by
  dsimp only
  rw [component_cut_singleton_count p root hsize]
  exact maximal_cut_bridge_unpaid_bounds hn p hmax hc hk

#print axioms component_cut_isolated_card
#print axioms component_cut_singleton_count
#print axioms maximal_bridge_bounds_at_component_cut
end LRX.FiniteCuts
