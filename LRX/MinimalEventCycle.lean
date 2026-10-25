import LRX.EventComponentRestriction
import LRX.MinimalEventCarrier
import LRX.SwapOrbitMerge
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Cyclic connections in a selected event component are preserved in the whole product. -/
theorem selected_same_cycle (events : List (Event n)) (root i : Fin n)
    (hi : ((componentEvents events root).map eventSwap).prod.SameCycle root i) :
    (events.map eventSwap).prod.SameCycle root i := by
  let p := (events.map eventSwap).prod
  let q := ((componentEvents events root).map eventSwap).prod
  have hiter (k : ℕ) : (p^k) root=(q^k) root ∧ EventReaches events root ((q^k) root) := by
    induction k with
    | zero => exact ⟨rfl,Relation.ReflTransGen.refl⟩
    | succ k ih =>
      have he := selected_product_agrees events root ((q^k) root) ih.2
      have hp := event_product_reaches events (componentEvents events root)
        (fun e he => (List.mem_filter.mp he).1) ((q^k) root)
      constructor
      · rw [pow_succ',pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.mul_apply,ih.1]
        exact he.symm
      · simpa only [pow_succ',Equiv.Perm.mul_apply] using ih.2.trans hp
  obtain ⟨k,hk⟩ := hi.exists_nat_pow_eq
  have he : (p^k) root=i := (hiter k).1.trans hk
  have hc : p.SameCycle root ((p^k) root) := (Equiv.Perm.SameCycle.refl p root).pow_right
  exact he ▸ hc

/-- A minimal connected list of transpositions has one orbit on its entire carrier. -/
theorem minimal_event_same_cycle (events : List (Event n)) (root : Fin n)
    (hmin : events.length+1=(eventComponent events root).card) :
    ∀ i ∈ eventComponent events root, (events.map eventSwap).prod.SameCycle root i := by
  classical
  have main : ∀ m : ℕ, ∀ (xs : List (Event n)) (r : Fin n), xs.length=m →
      xs.length+1=(eventComponent xs r).card →
      ∀ i ∈ eventComponent xs r, (xs.map eventSwap).prod.SameCycle r i := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro xs r hlen hm
      cases xs with
      | nil =>
        intro i hi
        have hr : r ∈ eventComponent [] r := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
        have hc : (eventComponent [] r).card ≤ 1 := by simpa using hm.symm.le
        have he : r=i := Finset.card_le_one.mp hc r hr i hi
        subst i
        exact Equiv.Perm.SameCycle.refl _ _
      | cons e rest =>
        have hrhead := minimal_events_reachable (e::rest) r hm e (by simp)
        have hcarrier := event_component_reroot (e::rest) hrhead
        have hm' : (e::rest).length+1=(eventComponent (e::rest) e.1).card := by rwa [← hcarrier]
        have branches := head_branch_minimal e rest hm'
        have hnot := head_endpoints_disconnected e rest hm'
        let q := (rest.map eventSwap).prod
        have hnq : ¬q.SameCycle e.1 e.2 := by
          intro hs
          exact hnot (cycle_event_reachable rest q rfl hs.inv)
        have hbranch (b : Fin n)
            (hb : (componentEvents rest b).length+1=(eventComponent rest b).card)
            (i : Fin n) (hi : i ∈ eventComponent rest b) : q.SameCycle b i := by
          have hle := List.length_filter_le (fun e => decide (EventReaches rest b e.1)) rest
          have hlt : (componentEvents rest b).length < m := by
            change (componentEvents rest b).length ≤ rest.length at hle
            simp only [List.length_cons] at hlen
            omega
          have hh := ih (componentEvents rest b).length hlt (componentEvents rest b) b rfl
            (by rwa [selected_component_eq]) i (by rwa [selected_component_eq])
          exact selected_same_cycle rest b i hh
        have hall (i : Fin n) (hi : i ∈ eventComponent (e::rest) e.1) :
            (eventSwap e*q).SameCycle e.1 i := by
          have hp := head_components_cover e rest ((mem_eventComponent _ _ _).mp hi)
          rcases hp with hp | hp
          · exact same_cycle_after_orbit_merge q e.1 e.2 hnq
              (hbranch e.1 branches.1 i ((mem_eventComponent _ _ _).mpr hp))
          · exact (swap_distinct_orbits_same_cycle q e.1 e.2 hnq).trans
              (same_cycle_after_orbit_merge q e.1 e.2 hnq
                (hbranch e.2 branches.2 i ((mem_eventComponent _ _ _).mpr hp)))
        intro i hi
        have hr : r ∈ eventComponent (e::rest) e.1 :=
          (mem_eventComponent _ _ _).mpr (event_reaches_symm _ hrhead)
        rw [hcarrier] at hi
        exact (hall r hr).symm.trans (hall i hi)
  exact main events.length events root rfl hmin


#print axioms selected_same_cycle
#print axioms minimal_event_same_cycle
end LRX.ZeroGap
