import LRX.EventSublistRepair

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Exact factorization and deletion correction compare the ranks of two actual products. -/
theorem event_sublist_rank_bound {part events : List (Event n)}
    (hsub : part.Sublist events) (p q : State n)
    (hp : (events.map eventSwap).prod = p) (hq : (part.map eventSwap).prod = q) :
    q.support.card+p.cycleFactorsFinset.card+part.length ≤
      events.length+p.support.card+(q⁻¹).cycleFactorsFinset.card := by
  obtain ⟨repair,hlen,hrepair⟩ := event_sublist_repair hsub
  obtain ⟨hfactor,hrank⟩ := exact_event_word_spec p
  have hprod : ((repair++exactEventWord p).map eventSwap).prod = q := by
    rw [List.map_append,List.prod_append,hfactor]
    rw [hp,hq] at hrepair
    exact hrepair
  have hh := cycle_root_count hprod
  rw [List.length_append] at hh
  omega

/-- The numerical D2 bound once a spanning cyclic subsequence has been extracted.
Its extraction from the sorting event graph is a separate remaining obligation. -/
theorem spanning_cycle_event_bound {part events : List (Event n)}
    (hsub : part.Sublist events) (p q : State n)
    (hp : (events.map eventSwap).prod = p) (hq : (part.map eventSwap).prod = q)
    (hcycle : q.IsCycle) (hsupport : q.support = p.support)
    (hsize : part.length+1=p.support.card) :
    p.support.card+p.cycleFactorsFinset.card ≤ events.length+2 := by
  have hh := event_sublist_rank_bound hsub p q hp hq
  have hc : (q⁻¹).cycleFactorsFinset.card=1 := by
    rw [hcycle.inv.cycleFactorsFinset_eq_singleton,Finset.card_singleton]
  rw [hsupport,hc] at hh
  omega

/-- Written in the defect convention of D2, for the same supplied spanning subsequence. -/
theorem spanning_cycle_event_defect {part events : List (Event n)}
    (hsub : part.Sublist events) (p q : State n)
    (hp : (events.map eventSwap).prod = p) (hq : (part.map eventSwap).prod = q)
    (hcycle : q.IsCycle) (hsupport : q.support = p.support)
    (hsize : part.length+1=p.support.card) :
    2*((p.cycleFactorsFinset.card : ℤ)-1) ≤
      (events.length : ℤ)-(p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ) := by
  have h := spanning_cycle_event_bound hsub p q hp hq hcycle hsupport hsize
  omega

#print axioms event_sublist_rank_bound
#print axioms spanning_cycle_event_bound
#print axioms spanning_cycle_event_defect
end LRX.ZeroGap
