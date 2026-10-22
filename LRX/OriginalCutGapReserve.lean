import LRX.ActualPeakCutoff
import LRX.LargeComponentWidthReserve

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- C7 pays fixed-gap widths in the original routed cut, not only in the
component-normalized cut. No maximality premise is needed here. -/
theorem original_cut_width_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) :
    2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let M : ℤ := 2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ)
  have hreserve := large_component_numeric_reserve hn p hmaj (by omega) root hlarge
  dsimp only at hreserve
  have hnonneg : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hv : 2*(t : ℤ) ≤ (v : ℤ) := by exact_mod_cast nontrivial_suffix_size_sum q L
  have hM := cross_minimum_pays_gap_width (t : ℤ) (v : ℤ) (a : ℤ) (a.choose 2 : ℤ) M
    (by exact_mod_cast ht) hv (by positivity) (by positivity) le_rfl
  have hcount := component_cut_external_count p root (by omega)
  change t+1=(componentRoots p).card at hcount
  have htk : t=k := by omega
  have hiso : a=(isolatedVertices p).card := component_cut_singleton_count p root (by omega)
  have hB := component_bridge_singleton_budget p hc
  rw [← isolated_vertices_card] at hB
  have hB' : (bridgeBudget (componentBridges p hc) : ℤ) ≤ (a : ℤ)+(t : ℤ) := by
    rw [hiso,htk]
    exact_mod_cast hB
  have hiso' : ((isolatedVertices p).card : ℤ)=(a : ℤ) := by exact_mod_cast hiso.symm
  rw [hiso']
  dsimp only [M] at hM
  linarith

#print axioms original_cut_width_reserve
end LRX.FiniteCuts
