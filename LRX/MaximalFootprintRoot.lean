import LRX.FootprintGeometry

/-! A footprint maximal in its overlap component reaches every footprint in
that component. The argument follows directed paths backwards through strict
containment and uses finiteness only to choose the maximal footprint. -/
namespace LRX.FootprintGeometry
variable {V C : Type*} [DecidableEq V]

abbrev PassPath (E support : C → Finset V) := Relation.ReflTransGen (Passes E support)
abbrev OverlapPath (E : C → Finset V) := Relation.ReflTransGen (Overlap E)

theorem overlap_path_symm (E : C → Finset V) {a b : C} (h : OverlapPath E a b) : OverlapPath E b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath he ih => exact (Relation.ReflTransGen.single (overlap_symm E he)).trans ih

theorem pass_path_overlap (E support : C → Finset V) (hs : ∀ a, support a ⊆ E a)
    {a b : C} (h : PassPath E support a b) : OverlapPath E a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath he ih => exact ih.tail (passes_overlap E support hs he)

theorem backward_strict_containment (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b)
    (root target : C) (hnot : ¬PassPath E support root target)
    {last : C} (hpath : PassPath E support root last) : E last ⊂ E target → E root ⊂ E target := by
  induction hpath with
  | refl => exact id
  | @tail a b hpath hedge ih =>
    intro hb
    obtain ⟨x,hxa,hxb⟩ := hedge
    have hm : Overlap E a target := ⟨x,Finset.mem_inter.mpr ⟨hxa,(Finset.ssubset_iff_subset_ne.mp hb).1 (hs b hxb)⟩⟩
    have hn : ¬Passes E support a target := fun he => hnot (hpath.tail he)
    exact ih (hdom a target hm hn)

theorem reachable_overlap_closed (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b)
    (root a b : C) (hmax : (E b).card ≤ (E root).card)
    (ha : PassPath E support root a) (hab : Overlap E a b) : PassPath E support root b := by
  by_contra hb
  have hnot : ¬Passes E support a b := fun h => hb (ha.tail h)
  have hstrict := backward_strict_containment E support hs hdom root b hb ha (hdom a b hab hnot)
  have := Finset.card_lt_card hstrict
  omega

theorem maximal_reaches_component (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b)
    (root : C) (hmax : ∀ b, OverlapPath E root b → (E b).card ≤ (E root).card)
    {b : C} (hpath : OverlapPath E root b) : PassPath E support root b := by
  induction hpath with
  | refl => exact Relation.ReflTransGen.refl
  | @tail a b hpath he ih =>
    exact reachable_overlap_closed E support hs hdom root a b (hmax b (hpath.tail he)) ih he

theorem exists_component_root [Fintype C] (E support : C → Finset V)
    (hs : ∀ a, support a ⊆ E a)
    (hdom : ∀ a b, Overlap E a b → ¬Passes E support a b → E a ⊂ E b)
    (initial : C) :
    ∃ root, OverlapPath E initial root ∧
      ∀ b, OverlapPath E initial b → PassPath E support root b := by
  classical
  let component := Finset.univ.filter (fun a => OverlapPath E initial a)
  have hnon : component.Nonempty := ⟨initial,by simp [component,Relation.ReflTransGen.refl]⟩
  obtain ⟨root,hroot,hmax⟩ := component.exists_max_image (fun a => (E a).card) hnon
  have hr : OverlapPath E initial root := (Finset.mem_filter.mp hroot).2
  refine ⟨root,hr,?_⟩
  intro b hb
  apply maximal_reaches_component E support hs hdom root
    (fun c hc => hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr.trans hc⟩))
  exact (overlap_path_symm E hr).trans hb

theorem component_root_is_source (E support : C → Finset V) (hs : ∀ a, support a ⊆ E a)
    (root : C) (hroot : ∀ b, OverlapPath E root b → PassPath E support root b)
    {a : C} (ha : PassPath E support a root) : PassPath E support root a := by
  exact hroot a (overlap_path_symm E (pass_path_overlap E support hs ha))

#print axioms exists_component_root
#print axioms component_root_is_source
end LRX.FootprintGeometry
