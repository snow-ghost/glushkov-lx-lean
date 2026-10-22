import LRX.PrefixComponentParameters
import LRX.LargeComponentNumericReserve

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- At the actual component cut, the bridge parameters are exactly C7's t and a. -/
theorem component_cut_bridge_parameters (p : State n) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let a := (singletonSuffixComponents q L).card
    ∃ hc : (componentRoots q).card = t+1,
      bridgeBudget (componentBridges q hc) ≤ a+t := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  let L := (componentSet p root).card
  have hcards := (component_recenter_cut p root).2
  have he : componentSet p root = componentSet p r :=
    CycleFootprint.component_eq_of_path _ (component_left_path p root)
  have hzero : (componentSet q 0).card = L := by
    have h := hcards 0
    simp only [zero_add] at h
    change (componentSet q 0).card = (componentSet p r).card at h
    rw [← he] at h
    exact h
  have hcsize : 2 ≤ (componentSet q 0).card := by rw [hzero]; exact hsize
  have hpref (i : Fin n) : i ∈ componentSet q 0 ↔ i.val < L := by
    rw [zero_component_prefix,hzero]
  have hc := prefix_component_root_count q L hcsize hpref
  have hs := prefix_singleton_components q L hcsize hpref
  refine ⟨hc,?_⟩
  have hb := component_bridge_singleton_budget q hc
  rw [hs] at hb
  exact hb

/-- The actual bridge price is paid along with all original filling deficits
when the exterior contains at least two nontrivial components. -/
theorem large_component_bridge_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    2 ≤ t → ∃ hc : (componentRoots q).card = t+1,
      ((positiveSourceFamily q n).map FillingWindow.deficit).sum+
        2*(bridgeBudget (componentBridges q hc) : ℤ)+1 ≤
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  dsimp only
  intro ht
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let a := (singletonSuffixComponents q L).card
  obtain ⟨hc,hB⟩ := component_cut_bridge_parameters p root (by omega)
  have hreserve := large_component_many_reserve hn p hmaj hm root hlarge ht
  refine ⟨hc,?_⟩
  have hB' : (bridgeBudget (componentBridges q hc) : ℤ) ≤ (a : ℤ)+(t : ℤ) := by
    exact_mod_cast hB
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+2*((a : ℤ)+(t : ℤ)) ≤ _ at hreserve
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+2*(bridgeBudget (componentBridges q hc) : ℤ)+1 ≤ _
  omega

#print axioms component_cut_bridge_parameters
#print axioms large_component_bridge_reserve
end LRX.FiniteCuts
