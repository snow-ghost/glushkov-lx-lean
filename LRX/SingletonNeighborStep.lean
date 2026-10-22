import LRX.ExtremeNeighborInsertion

namespace LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Adding a singleton next to an extreme preserves an inductive neighbor;
the three-vertex case is constructed directly. -/
theorem singleton_neighbor_step (events : List (Event n)) (a b r : Fin n)
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val)
    (hmin : (componentEvents events a).length+1=(eventComponent events a).card)
    (hcard : 2 ≤ (eventComponent events a).card)
    (hb : b ∉ eventComponent events a)
    (hfixed : (events.map eventSwap).prod b=b)
    (hr : r ∈ eventComponent events a)
    (hgap : RankAdjacent (insert b (eventComponent events a)) a b)
    (hext : IsExtreme (insert b (eventComponent events a)) r)
    (ih : 3 ≤ (eventComponent events a).card → IsExtreme (eventComponent events a) a →
      NeighborAway (componentEvents events a) a a) :
    ∃ x y, RankAdjacent (insert b (eventComponent events a)) x y ∧
      (Equiv.swap a b*(events.map eventSwap).prod) x=y ∧ x ≠ r ∧ y ≠ r := by
  classical
  by_cases hra : r=a
  · subst r
    have hextA : IsExtreme (eventComponent events a) a := by
      rcases hext with h | h
      · exact Or.inl (fun i hi => h i (Finset.mem_insert_of_mem hi))
      · exact Or.inr (fun i hi => h i (Finset.mem_insert_of_mem hi))
    by_cases hc3 : 3 ≤ (eventComponent events a).card
    · obtain ⟨x,y,hxy,hp,hxa,hya⟩ := ih hc3 hextA
      rw [selected_component_eq] at hxy
      have hxp := (mem_eventComponent events a x).mp hxy.1
      have hq : (events.map eventSwap).prod x=y := (selected_product_agrees events a x hxp).symm.trans hp
      have hyb : y ≠ b := fun h => hb (h ▸ hxy.2.1)
      refine ⟨x,y,rank_adjacent_after_extreme_insertion _ a b hext hgap hxy hxa hya,?_,hxa,hya⟩
      rw [Equiv.Perm.mul_apply,hq,Equiv.swap_apply_of_ne_of_ne hya hyb]
    · have hc2 : (eventComponent events a).card=2 := by omega
      let q : State n := ((componentEvents events a).map eventSwap).prod
      have hlin : ∀ e ∈ componentEvents events a, e.1.val < e.2.val :=
        fun e he => hlinear e (List.mem_filter.mp he).1
      have hs : q.support=eventComponent events a := by
        have h := minimal_two_vertex_support (componentEvents events a) a
          (by rwa [selected_component_eq]) hlin (by rwa [selected_component_eq])
        simpa only [selected_component_eq] using h
      have ha : a ∈ q.support := by rwa [hs]
      have hne : q a ≠ a := Equiv.Perm.mem_support.mp ha
      have hqa : q a ∈ q.support := by
        apply Equiv.Perm.mem_support.mpr
        intro h
        exact hne (q.injective h)
      have hreturn : q (q a)=a := by
        have hswap : q.IsSwap := Equiv.Perm.card_support_eq_two.mp (by rwa [hs])
        obtain ⟨u,v,_,heq⟩ := hswap
        rw [heq]
        simp
      have hpair : ({a,q a} : Finset (Fin n))=eventComponent events a := by
        apply Finset.eq_of_subset_of_card_le
        · intro i hi
          simp only [Finset.mem_insert,Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact hr
          · rwa [← hs]
        · simp [hc2,Ne.symm hne]
      have hab : a ≠ b := fun h => hb (h ▸ hr)
      have hbc : b ≠ q a := by intro h; apply hb; rw [h]; rwa [← hs]
      have hS : insert b (eventComponent events a)=({a,b,q a} : Finset (Fin n)) := by
        rw [← hpair,Finset.insert_comm b a]
      have hex : IsExtreme ({a,b,q a} : Finset (Fin n)) a := by rwa [hS] at hext
      have hneighbor := remaining_pair_adjacent a b (q a) hab (Ne.symm hne) hbc hex
      have htail : (events.map eventSwap).prod (q a)=a := by
        have hm : q a ∈ eventComponent events a := by rwa [← hs]
        exact (selected_product_agrees events a (q a) ((mem_eventComponent _ _ _).mp hm)).symm.trans hreturn
      refine ⟨q a,b,?_,?_,hne,Ne.symm hab⟩
      · rwa [hS]
      · rw [Equiv.Perm.mul_apply,htail,Equiv.swap_apply_left]
  · have hbr : b ≠ r := fun h => hb (h.symm ▸ hr)
    refine ⟨b,a,rank_adjacent_symm hgap,?_,hbr,Ne.symm hra⟩
    rw [Equiv.Perm.mul_apply,hfixed,Equiv.swap_apply_right]

#print axioms singleton_neighbor_step
end LRX.ZeroGap
