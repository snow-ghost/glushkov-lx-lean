import LRX.SpanningEventSublist
import LRX.ZeroGapCycleRoots
import Mathlib

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Replacing one event component by a spanning subsequence preserves every
original graph connection. No assertion about the permutation product is needed. -/
theorem spanning_replacement_reaches (events part : List (Event n)) (root : Fin n)
    (hcomp : eventComponent part root=eventComponent events root)
    {a b : Fin n} (hab : EventReaches events a b) :
    EventReaches (part++outsideEvents events root) a b := by
  classical
  have hstep {i j : Fin n} (he : EventEdge events i j) :
      EventReaches (part++outsideEvents events root) i j := by
    obtain ⟨e,he,hor⟩ := he
    by_cases hs : EventReaches events root e.1
    · have ht : EventReaches events root e.2 := hs.tail ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
      have hpart (x : Fin n) (hx : EventReaches events root x) : EventReaches part root x := by
        apply (mem_eventComponent _ _ _).mp
        rw [hcomp]
        exact (mem_eventComponent _ _ _).mpr hx
      have hedge := (event_reaches_symm part (hpart e.1 hs)).trans (hpart e.2 ht)
      have hnew : EventReaches (part++outsideEvents events root) e.1 e.2 :=
        event_reaches_mono (fun _ h => List.mem_append_left _ h) hedge
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hnew
      · exact event_reaches_symm _ hnew
    · have hout : e ∈ outsideEvents events root := by simp [outsideEvents,he,hs]
      exact Relation.ReflTransGen.single ⟨e,List.mem_append_right _ hout,hor⟩
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact ih.trans (hstep he)

/-- Equality in the root-cover count forces every actual selected event
component to have exactly the number of edges of a tree. -/
theorem root_cover_equality_component_minimal (events : List (Event n))
    (roots : List (Fin n)) (hcover : ∀ i : Fin n, ∃ r ∈ roots, EventReaches events r i)
    (heq : events.length+roots.length=n) (root : Fin n) :
    (componentEvents events root).length+1=(eventComponent events root).card := by
  obtain ⟨part,_,hcomp,hlen,_,_⟩ := component_spanning_event_sublist events root
  have hcover' : ∀ i : Fin n, ∃ r ∈ roots,
      EventReaches (part++outsideEvents events root) r i := by
    intro i
    obtain ⟨r,hr,hi⟩ := hcover i
    exact ⟨r,hr,spanning_replacement_reaches events part root hcomp hi⟩
  have hbound := root_cover_count (part++outsideEvents events root) roots hcover'
  rw [List.length_append] at hbound
  have hsplit := component_events_length events root
  have hsize := component_selected_size events root
  omega

/-- A minimal transposition factorization is a forest on its actual event
carriers. The cycle representatives supply the cover, including fixed points. -/
theorem minimal_factorization_component_minimal (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card) (root : Fin n) :
    (componentEvents events root).length+1=(eventComponent events root).card := by
  classical
  apply root_cover_equality_component_minimal events (cycleRoots p) (cycle_roots_cover hprod) _ root
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  simp only [cycleRoots,List.length_append,List.length_map,Finset.length_toList,
    Finset.card_compl,Finset.card_univ,Fintype.card_fin,Equiv.Perm.support_inv]
  omega

#print axioms spanning_replacement_reaches
#print axioms root_cover_equality_component_minimal
#print axioms minimal_factorization_component_minimal
end LRX.ZeroGap
