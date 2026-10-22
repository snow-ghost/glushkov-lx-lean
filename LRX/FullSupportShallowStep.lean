import LRX.ShallowRankCompression
import LRX.ShallowCycleNeighbor

namespace LRX.FiniteCuts
variable {n : ℕ}

theorem full_carrier_neighbor_unit {x y : Fin n}
    (h : ZeroGap.RankAdjacent Finset.univ x y) : |(y : ℤ)-(x : ℤ)|=1 := by
  by_contra hunit
  have hne : x.val ≠ y.val := fun he => h.2.2.1 (Fin.ext he)
  have hgap : min x.val y.val+1 < max x.val y.val := by
    simp only [abs_eq_max_neg] at hunit
    omega
  let z : Fin n := ⟨min x.val y.val+1,by have := x.isLt; have := y.isLt; omega⟩
  apply h.2.2.2 z (Finset.mem_univ z)
  change min x.val y.val < min x.val y.val+1 ∧ min x.val y.val+1 < max x.val y.val
  exact ⟨by omega,hgap⟩

/-- Once standardized, a shallow cycle can be contracted repeatedly in rank
coordinates: one step preserves full support as well as cyclicity and defect. -/
theorem full_support_shallow_step {p : State (n+1)} (hp : p.IsCycle) (hs : Shallow p)
    (hfull : p.support=Finset.univ) (hn : 2 ≤ n) :
    ∃ a : Fin (n+1), |displacement p a|=1 ∧
      (contract p a).IsCycle ∧ Shallow (contract p a) ∧ (contract p a).support=Finset.univ := by
  classical
  obtain ⟨a,b,hab,harrow⟩ := ZeroGap.shallow_cycle_rank_neighbor hp hs
  rw [hfull] at hab
  have hunit : |displacement p a|=1 := by
    unfold displacement
    rw [harrow]
    exact full_carrier_neighbor_unit hab
  have hcard : p.support.card=n+1 := by simp [hfull]
  have hc : 3 ≤ p.support.card := by omega
  obtain ⟨hcycle,hshallow⟩ := contract_shallow_cycle hp hc hs a hunit
  have hdrop := contract_cycle_support_card hp hc a hunit
  have hnew : (contract p a).support.card=n := by omega
  refine ⟨a,hunit,hcycle,hshallow,?_⟩
  apply Finset.eq_univ_of_card
  simpa using hnew

#print axioms shallow_rank_compression
#print axioms full_support_shallow_step
end LRX.FiniteCuts
