import LRX.LargeComponentBridgeReserve

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

theorem cross_minimum_pays_gap_width (t v a pairs M : ℤ)
    (ht : 2 ≤ t) (hv : 2*t ≤ v) (ha : 0 ≤ a) (hpairs : 0 ≤ pairs)
    (hM : 2*(t-1)*(v-t)+a*v+pairs ≤ M) : 3*a+2*t ≤ M := by
  have h1 := mul_nonneg (show 0 ≤ t-1 by omega) (show 0 ≤ v-2*t by omega)
  have h2 := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-2 by omega)
  have h3 := mul_nonneg ha (show 0 ≤ v-3 by omega)
  nlinarith

theorem component_cut_isolated_count (p : State n) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    (isolatedVertices q).card = (singletonSuffixComponents q (componentSet p root).card).card := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  let L := (componentSet p root).card
  have he : componentSet p root = componentSet p r :=
    CycleFootprint.component_eq_of_path _ (component_left_path p root)
  have hzero : (componentSet q 0).card = L := by
    have h := (component_recenter_cut p root).2 0
    simp only [zero_add] at h
    change (componentSet q 0).card = (componentSet p r).card at h
    rw [← he] at h
    exact h
  have hc : 2 ≤ (componentSet q 0).card := by rw [hzero]; exact hsize
  have hpref (i : Fin n) : i ∈ componentSet q 0 ↔ i.val < L := by rw [zero_component_prefix,hzero]
  have hs := prefix_singleton_components q L hc hpref
  change (isolatedVertices q).card = (singletonSuffixComponents q L).card
  rw [isolated_vertices_card,hs]

/-- The full C7 minimum pays the actual bridges and any gap width bounded
by the number of isolated vertices, without a maximal-cut premise. -/
theorem large_component_width_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    2 ≤ t → ∃ hc : (componentRoots q).card = t+1,
      2*(bridgeBudget (componentBridges q hc) : ℤ)+(isolatedVertices q).card+1 ≤
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  dsimp only
  intro ht
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let M : ℤ := ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ))
  have hLn : L ≤ n := (component_card_lt_of_multiple_roots p hm root).le
  have hcut := (component_recenter_cut p root).1
  have hcross : 2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤ M :=
    suffix_cross_numeric_lower q L hLn hcut
  have hv : 2*(t : ℤ) ≤ (v : ℤ) := by exact_mod_cast nontrivial_suffix_size_sum q L
  have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
  have hM := cross_minimum_pays_gap_width (t : ℤ) (v : ℤ) (a : ℤ) (a.choose 2 : ℤ) M
    ht' hv (by positivity) (by positivity) hcross
  have hnonneg : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,hA,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hbudget := large_component_reserve_by_sizes hn p hmaj hm root hlarge
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) ≤ _ at hbudget
  obtain ⟨hc,hB⟩ := component_cut_bridge_parameters p root (by omega)
  have hB' : (bridgeBudget (componentBridges q hc) : ℤ) ≤ (a : ℤ)+(t : ℤ) := by exact_mod_cast hB
  have hi : ((isolatedVertices q).card : ℤ) = (a : ℤ) := by
    exact_mod_cast component_cut_isolated_count p root (by omega)
  refine ⟨hc,?_⟩
  change 2*(bridgeBudget (componentBridges q hc) : ℤ)+(isolatedVertices q).card+1 ≤ _
  dsimp only [M] at hM
  omega

#print axioms large_component_width_reserve
end LRX.FiniteCuts
