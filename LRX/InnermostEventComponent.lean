import LRX.EventCoverEquality
import LRX.EventTreeRankNeighbor
import LRX.FiniteCutLoad
import LRX.FullSupportShallowStep
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- In a linear separated trace with interval support, a moving component
of minimum physical width has no holes. -/
theorem exists_interval_event_component (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hne : p.support.Nonempty) (hinterval : CarrierInterval p.support Finset.univ) :
    ∃ root : Fin n, root ∈ p.support ∧ 2 ≤ (eventComponent events root).card ∧
      CarrierInterval (eventComponent events root) Finset.univ := by
  classical
  let C := eventComponent events
  have hroot (r : Fin n) : r ∈ C r := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  let lo (r : Fin n) := (C r).min' ⟨r,hroot r⟩
  let hi (r : Fin n) := (C r).max' ⟨r,hroot r⟩
  have hlo (r : Fin n) : lo r ∈ C r := Finset.min'_mem _ _
  have hhi (r : Fin n) : hi r ∈ C r := Finset.max'_mem _ _
  have hbounds (r i : Fin n) (h : i ∈ C r) : (lo r).val ≤ i.val ∧ i.val ≤ (hi r).val :=
    ⟨Finset.min'_le _ _ h,Finset.le_max' _ _ h⟩
  have hsub (r : Fin n) (hr : r ∈ p.support) : C r ⊆ p.support := by
    intro i hi
    have hp := (mem_eventComponent _ _ _).mp hi
    induction hp with
    | refl => exact hr
    | @tail a b hp he ih =>
      obtain ⟨e,he,hor⟩ := he
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact (hactive e he).2
      · exact (hactive e he).1
  obtain ⟨r,hr,hmin⟩ := p.support.exists_min_image (fun r => (hi r).val-(lo r).val) hne
  have hclosed (z : Fin n) (hzlo : (lo r).val < z.val) (hzhi : z.val < (hi r).val) : z ∈ C r := by
    by_contra hz
    have hzmove : z ∈ p.support := hinterval.2 (lo r) (hsub r hr (hlo r))
      (hi r) (hsub r hr (hhi r)) z (Finset.mem_univ _) (by omega) (by omega)
    have hrl := (mem_eventComponent _ _ _).mp (hlo r)
    have hrh := (mem_eventComponent _ _ _).mp (hhi r)
    have hlh := (event_reaches_symm events hrl).trans hrh
    have hav : ¬ EventReaches events (lo r) z := by
      intro hh
      exact hz ((mem_eventComponent _ _ _).mpr (hrl.trans hh))
    have hb (i : Fin n) (hh : EventReaches events (lo r) i) :
        (lo r).val ≤ i.val ∧ i.val ≤ (hi r).val :=
      hbounds r i ((mem_eventComponent _ _ _).mpr (hrl.trans hh))
    have inner (j : Fin n) (hj : j ∈ C z) : (lo r).val < j.val ∧ j.val < (hi r).val :=
      component_inside_hull events hlinear hsep (lo r) z (hi r) hzlo hzhi hlh hav
        (lo r).val (hi r).val hb j ((mem_eventComponent _ _ _).mp hj)
    have hlz := inner (lo z) (hlo z)
    have hhz := inner (hi z) (hhi z)
    have hzz := hbounds z (lo z) (hlo z)
    have hrr := hbounds r (lo r) (hlo r)
    have hminimal := hmin z hzmove
    omega
  refine ⟨r,hr,?_,Finset.subset_univ _,?_⟩
  · have hpr : p r ∈ C r := by
      apply (mem_eventComponent _ _ _).mpr
      have hh := event_product_reaches events events (fun _ h => h) r
      rwa [hprod] at hh
    exact Finset.one_lt_card.mpr ⟨r,hroot r,p r,hpr,(Equiv.Perm.mem_support.mp hr).symm⟩
  · intro x hx y hy z _ hz1 hz2
    have hx' := hbounds r x hx
    have hy' := hbounds r y hy
    exact hclosed z (by omega) (by omega)

/-- A minimal separated factorization on a nonempty interval support has
an actual unit arrow. The carrier is extracted, not assumed to be a cycle. -/
theorem minimal_interval_event_unit_arrow (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hactive : ∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) (hsep : events.Pairwise LaterOutside)
    (hne : p.support.Nonempty) (hinterval : CarrierInterval p.support Finset.univ)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card) :
    ∃ i : Fin n, |FiniteCuts.displacement p i|=1 := by
  classical
  obtain ⟨root,_,hc,hint⟩ := exists_interval_event_component events p hprod hactive hlinear hsep hne hinterval
  have hmin := minimal_factorization_component_minimal events p hprod hminimal root
  have hsub : (componentEvents events root).Sublist events := List.filter_sublist
  obtain ⟨x,y,hxy,harrow⟩ := minimal_tree_rank_neighbor (componentEvents events root) root
    (fun e he => hlinear e (hsub.subset he)) (hsep.sublist hsub)
    (by rwa [selected_component_eq]) (by rwa [selected_component_eq])
  rw [selected_component_eq] at hxy
  have hagree := selected_product_agrees events root x ((mem_eventComponent _ _ _).mp hxy.1)
  rw [hprod] at hagree
  have hp : p x=y := hagree.symm.trans harrow
  refine ⟨x,?_⟩
  unfold FiniteCuts.displacement
  rw [hp]
  exact FiniteCuts.full_carrier_neighbor_unit (rank_adjacent_of_interval hint hxy)

#print axioms exists_interval_event_component
#print axioms minimal_interval_event_unit_arrow
end LRX.ZeroGap
