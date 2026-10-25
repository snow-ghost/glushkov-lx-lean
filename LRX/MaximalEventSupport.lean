import LRX.ZeroGapComponentCounting
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

theorem event_product_support_subset_endpoints (events : List (Event n)) :
    (events.map eventSwap).prod.support ⊆ endpoints events := by
  intro i hi
  by_contra hn
  exact (Equiv.Perm.mem_support.mp hi) (event_product_fixed events i hn)

/-- If every swap contributes two moved vertices, no endpoint can be repeated. -/
theorem maximal_event_support_nodup (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length) :
    (events.flatMap (fun e => [e.1,e.2])).Nodup := by
  have hlo := Finset.card_le_card (event_product_support_subset_endpoints events)
  have hhi := endpoints_card events
  have hlen : (events.flatMap (fun e => [e.1,e.2])).length=2*events.length := by
    induction events with
    | nil => simp
    | cons e rest ih => simp [ih]; omega
  apply List.nodup_iff_length_dedup_eq.mpr
  change (events.flatMap (fun e => [e.1,e.2])).toFinset.card=
    (events.flatMap (fun e => [e.1,e.2])).length
  change (endpoints events).card=_
  omega

theorem maximal_event_support_disjoint (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length) :
    (events.map eventSwap).Pairwise Equiv.Perm.Disjoint := by
  have hp := (List.nodup_flatMap.mp (maximal_event_support_nodup events hcard)).2
  apply List.pairwise_map.mpr
  apply hp.imp
  intro e f hef i
  change List.Disjoint [e.1,e.2] [f.1,f.2] at hef
  by_cases hi : i ∈ [e.1,e.2]
  · have hf : i ∉ [f.1,f.2] := List.disjoint_left.mp hef hi
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
    exact Or.inr (Equiv.swap_apply_of_ne_of_ne hf.1 hf.2)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
    exact Or.inl (Equiv.swap_apply_of_ne_of_ne hi.1 hi.2)

/-- Every event is an actual pair of the product permutation in the maximal-support case. -/
theorem maximal_event_support_pair (events : List (Event n))
    (hcard : (events.map eventSwap).prod.support.card=2*events.length)
    (e : Event n) (he : e ∈ events) :
    e.1 ≠ e.2 ∧ (events.map eventSwap).prod e.1=e.2 ∧
      (events.map eventSwap).prod e.2=e.1 := by
  have hn := (List.nodup_flatMap.mp (maximal_event_support_nodup events hcard)).1 e he
  have hne : e.1 ≠ e.2 := by simpa using hn
  have hd := maximal_event_support_disjoint events hcard
  have hm : eventSwap e ∈ events.map eventSwap := List.mem_map.mpr ⟨e,he,rfl⟩
  have hleft : e.1 ∈ (eventSwap e).support := by
    apply Equiv.Perm.mem_support.mpr
    simpa [eventSwap] using hne.symm
  have hright : e.2 ∈ (eventSwap e).support := by
    apply Equiv.Perm.mem_support.mpr
    simpa [eventSwap] using hne
  have hl := Equiv.Perm.eq_on_support_mem_disjoint hm hd e.1 hleft
  have hr := Equiv.Perm.eq_on_support_mem_disjoint hm hd e.2 hright
  exact ⟨hne, by simpa [eventSwap] using hl.symm, by simpa [eventSwap] using hr.symm⟩

#print axioms maximal_event_support_nodup
#print axioms maximal_event_support_pair
end LRX.ZeroGap
