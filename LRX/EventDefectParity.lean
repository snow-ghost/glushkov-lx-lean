import LRX.PaddedSortingEvents

namespace LRX.ZeroGap
variable {n : ℕ}

/-- The defect of any factorization by genuine transpositions is even. -/
theorem event_defect_even (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (hneq : ∀ e ∈ events, e.1 ≠ e.2) :
    Even ((events.length : ℤ)-(p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)) := by
  classical
  have hs := Equiv.Perm.sign_prod_list_swap (l := events.map eventSwap) (by
    intro g hg
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hg
    exact ⟨e.1,e.2,hneq e he,rfl⟩)
  rw [hprod,List.length_map] at hs
  have hc := Equiv.Perm.sign_of_cycleType p
  rw [Equiv.Perm.sum_cycleType] at hc
  simp only [Equiv.Perm.cycleType,Multiset.card_map,Finset.card_val] at hc
  have hh := congrArg (fun u : ℤˣ => (u : ℤ)) (hs.symm.trans hc)
  simp only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one] at hh
  rw [neg_one_pow_eq_pow_mod_two events.length,
    neg_one_pow_eq_pow_mod_two (p.support.card+p.cycleFactorsFinset.card)] at hh
  have hpar : events.length%2=(p.support.card+p.cycleFactorsFinset.card)%2 := by
    have ha : events.length%2=0 ∨ events.length%2=1 := by omega
    have hb : (p.support.card+p.cycleFactorsFinset.card)%2=0 ∨
      (p.support.card+p.cycleFactorsFinset.card)%2=1 := by omega
    rcases ha with ha | ha
    · rcases hb with hb | hb
      · omega
      · norm_num [ha,hb] at hh
    · rcases hb with hb | hb
      · norm_num [ha,hb] at hh
      · omega
  rw [Int.even_iff]
  omega

end LRX.ZeroGap

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Cycle defect parity for every finite permutation, with the actual sorting
trace supplied internally and no shortness assumption. -/
theorem finite_cycle_defect_even (p : State n) :
    Even ((∑ i, |displacement p i|)-(inversionNumber p : ℤ)-
      (p.support.card : ℤ)+(p.cycleFactorsFinset.card : ℤ)) := by
  classical
  let W : FiniteWindow.Window (2*n+1) n := ⟨0,by omega⟩
  let q := FiniteWindow.permutation W p
  obtain ⟨events,hprod,hlen,hneq,_,_,_⟩ := padded_sorting_events p
  have hh := ZeroGap.event_defect_even events q hprod hneq
  have hs : q.support.card=p.support.card := FiniteWindow.permutation_support_card W p
  have hk : q.cycleFactorsFinset.card=p.cycleFactorsFinset.card := FiniteWindow.permutation_cycle_count W p
  rw [hlen,hs,hk] at hh
  exact hh

#print axioms ZeroGap.event_defect_even
#print axioms finite_cycle_defect_even
end LRX.FiniteCuts
