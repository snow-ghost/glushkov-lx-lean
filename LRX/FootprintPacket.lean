import LRX.MaximalFootprintRoot

/-! Every reachable footprint is directly covered by the source strong
component. This is the graph form of the root-packet service contract. -/
namespace LRX.FootprintGeometry
variable {V C : Type*} [DecidableEq V]

theorem direct_from_core (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a) (hnonempty : ∀ a, (support a).Nonempty)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b)
    (root : C) {b : C} (hpath : PassPath E support root b) :
    ∃ a, PassPath E support root a ∧ PassPath E support a root ∧
      E b ⊆ E a ∧ Passes E support a b := by
  have hself (a : C) : Passes E support a a := by
    obtain ⟨x,hx⟩ := hnonempty a
    exact ⟨x,hs a hx,hx⟩
  induction hpath with
  | refl => exact ⟨root,Relation.ReflTransGen.refl,Relation.ReflTransGen.refl,le_rfl,hself root⟩
  | @tail b c hpath hedge ih =>
    by_cases hback : PassPath E support c root
    · exact ⟨c,hpath.tail hedge,hback,le_rfl,hself c⟩
    · obtain ⟨a,hra,har,hsub,_⟩ := ih
      obtain ⟨x,hxb,hxc⟩ := hedge
      have hmeet : Overlap E c a := ⟨x,Finset.mem_inter.mpr ⟨hs c hxc,hsub hxb⟩⟩
      have hnot : ¬Passes E support c a := fun he => hback ((Relation.ReflTransGen.single he).trans har)
      have hstrict := hdom c a hmeet hnot
      have hpass : Passes E support a c := by
        by_contra h
        have hother := hdom a c (overlap_symm E hmeet) h
        have h1 := Finset.card_lt_card hstrict
        have h2 := Finset.card_lt_card hother
        omega
      exact ⟨a,hra,har,(Finset.ssubset_iff_subset_ne.mp hstrict).1,hpass⟩

theorem exists_component_packet [Fintype C] (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a) (hnonempty : ∀ a, (support a).Nonempty)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b) (initial : C) :
    ∃ root, OverlapPath E initial root ∧
      (∀ a, PassPath E support a root → PassPath E support root a) ∧
      (∀ b, OverlapPath E initial b → ∃ a,
        PassPath E support root a ∧ PassPath E support a root ∧ Passes E support a b) := by
  obtain ⟨root,hr,hcover⟩ := exists_component_root E support hs hdom initial
  refine ⟨root,hr,?_,?_⟩
  · intro a ha
    exact component_root_is_source E support hs root (fun b hb => hcover b (hr.trans hb)) ha
  · intro b hb
    obtain ⟨a,hra,har,_,he⟩ := direct_from_core E support hs hnonempty hdom root (hcover b hb)
    exact ⟨a,hra,har,he⟩

theorem exists_packet_from_geometry [Fintype C] (E support : C → Finset V) (adj : V → V → Prop)
    (hs : ∀ a, support a ⊆ E a) (hnonempty : ∀ a, (support a).Nonempty)
    (hconnected : ∀ a x, x ∈ E a → ∀ y, y ∈ E a → Relation.ReflTransGen (Inside (E a) adj) x y)
    (hboundary : ∀ a x, x ∈ E a → x ∉ support a → ∀ y, adj x y → y ∈ E a) (initial : C) :
    ∃ root, OverlapPath E initial root ∧
      (∀ a, PassPath E support a root → PassPath E support root a) ∧
      (∀ b, OverlapPath E initial b → ∃ a,
        PassPath E support root a ∧ PassPath E support a root ∧ Passes E support a b) := by
  exact exists_component_packet E support hs hnonempty
    (fun a b he hp => avoiding_intersection_strict_subset E support adj hs hnonempty hconnected hboundary he hp) initial

#print axioms direct_from_core
#print axioms exists_component_packet
#print axioms exists_packet_from_geometry
end LRX.FootprintGeometry
