import LX.SingletonNeighborStep
import Mathlib

namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem component_card_one_eq (events : List (Event n)) (b : Fin n)
    (hb : (eventComponent events b).card=1) : eventComponent events b={b} := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hb
  have hm : b ∈ eventComponent events b := (mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl
  rw [hi,Finset.mem_singleton] at hm
  simpa only [hm] using hi

theorem event_neighbor_induction_step (e : Event n) (events : List (Event n))
    (hlinear : ∀ f ∈ e::events, f.1.val < f.2.val)
    (hsep : (e::events).Pairwise LaterOutside)
    (hmin : (e::events).length+1=(eventComponent (e::events) e.1).card)
    (hcard : 3 ≤ (eventComponent (e::events) e.1).card)
    (ih : ∀ b ∈ [e.1,e.2], 3 ≤ (eventComponent events b).card →
      IsExtreme (eventComponent events b) b → NeighborAway (componentEvents events b) b b)
    (r : Fin n) (hr : r ∈ eventComponent (e::events) e.1)
    (hext : IsExtreme (eventComponent (e::events) e.1) r) :
    NeighborAway (e::events) e.1 r := by
  classical
  have hab := head_endpoints_disconnected e events hmin
  have hba : ¬EventReaches events e.2 e.1 := fun h => hab (event_reaches_symm events h)
  have hdis := head_component_disjoint e events hmin
  have hm := head_branch_minimal e events hmin
  have ha1 : 1 ≤ (eventComponent events e.1).card := Finset.card_pos.mpr
    ⟨e.1,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hb1 : 1 ≤ (eventComponent events e.2).card := Finset.card_pos.mpr
    ⟨e.2,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hsum : 3 ≤ (eventComponent events e.1).card+(eventComponent events e.2).card := by
    rwa [head_component_union,Finset.card_union_of_disjoint hdis] at hcard
  have hl : ∀ f ∈ events, f.1.val < f.2.val := fun f hf => hlinear f (List.mem_cons_of_mem e hf)
  have hgap := head_rank_adjacent e events (hlinear e (by simp)) hsep
  rcases head_components_cover e events ((mem_eventComponent _ _ _).mp hr) with har | hbr
  · by_cases hb2 : 2 ≤ (eventComponent events e.2).card
    · apply opposite_moving_neighbor_step e events hlinear hsep hmin r
        (fun h => False.elim (hab (har.trans (event_reaches_symm events h))))
        (fun _ => hb2) ih hr hext
    · have hb : (eventComponent events e.2).card=1 := by omega
      have heqB := component_card_one_eq events e.2 hb
      have hS : eventComponent (e::events) e.1=insert e.2 (eventComponent events e.1) := by
        rw [head_component_union,heqB,Finset.union_singleton]
      have hnot : e.2 ∉ eventComponent events e.1 := fun h => hab ((mem_eventComponent _ _ _).mp h)
      obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := singleton_neighbor_step events e.1 e.2 r hl hm.1 (by omega)
        hnot (singleton_component_product_fixed events e.2 hb) ((mem_eventComponent _ _ _).mpr har)
        (by rwa [← hS]) (by rwa [← hS]) (ih e.1 (by simp))
      refine ⟨x,y,?_,?_,hxr,hyr⟩
      · rwa [hS]
      · simpa only [List.map_cons,List.prod_cons,eventSwap] using hp
  · by_cases ha2 : 2 ≤ (eventComponent events e.1).card
    · apply opposite_moving_neighbor_step e events hlinear hsep hmin r (fun _ => ha2)
        (fun h => False.elim (hba (hbr.trans (event_reaches_symm events h)))) ih hr hext
    · have ha : (eventComponent events e.1).card=1 := by omega
      have heqA := component_card_one_eq events e.1 ha
      have hS : eventComponent (e::events) e.1=insert e.1 (eventComponent events e.2) := by
        rw [head_component_union,heqA,Finset.singleton_union]
      have hnot : e.1 ∉ eventComponent events e.2 := fun h => hba ((mem_eventComponent _ _ _).mp h)
      obtain ⟨x,y,hxy,hp,hxr,hyr⟩ := singleton_neighbor_step events e.2 e.1 r hl hm.2 (by omega)
        hnot (singleton_component_product_fixed events e.1 ha) ((mem_eventComponent _ _ _).mpr hbr)
        (by rw [← hS]; exact rank_adjacent_symm hgap) (by rwa [← hS]) (ih e.2 (by simp))
      refine ⟨x,y,?_,?_,hxr,hyr⟩
      · rwa [hS]
      · simpa only [List.map_cons,List.prod_cons,eventSwap,Equiv.swap_comm e.2 e.1] using hp

#print axioms event_neighbor_induction_step
end LX.Core.ZeroGap
