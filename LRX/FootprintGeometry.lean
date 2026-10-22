import LRX.Graph

/-! Connected footprints with boundaries in their cycle supports. Avoiding
another cycle's support at an intersection forces strict footprint inclusion. -/
namespace LRX.FootprintGeometry
variable {V C : Type*} [DecidableEq V]

def Inside (E : Finset V) (adj : V → V → Prop) (x y : V) : Prop :=
  x ∈ E ∧ y ∈ E ∧ adj x y

def Overlap (E : C → Finset V) (a b : C) : Prop := (E a ∩ E b).Nonempty

def Passes (E support : C → Finset V) (a b : C) : Prop := ∃ x ∈ E a, x ∈ support b

theorem overlap_symm (E : C → Finset V) {a b : C} (h : Overlap E a b) : Overlap E b a := by
  simpa only [Overlap,Finset.inter_comm] using h

theorem passes_overlap (E support : C → Finset V) (hs : ∀ a, support a ⊆ E a)
    {a b : C} (h : Passes E support a b) : Overlap E a b := by
  obtain ⟨x,hx,hsx⟩ := h
  exact ⟨x,Finset.mem_inter.mpr ⟨hx,hs b hsx⟩⟩

theorem avoiding_intersection_strict_subset
    (E support : C → Finset V) (adj : V → V → Prop)
    (hsupport : ∀ a, support a ⊆ E a) (hnonempty : ∀ a, (support a).Nonempty)
    (hconnected : ∀ a x, x ∈ E a → ∀ y, y ∈ E a → Relation.ReflTransGen (Inside (E a) adj) x y)
    (hboundary : ∀ a x, x ∈ E a → x ∉ support a → ∀ y, adj x y → y ∈ E a)
    {a b : C} (hmeet : Overlap E a b) (havoid : ¬Passes E support a b) : E a ⊂ E b := by
  obtain ⟨x,hx⟩ := hmeet
  obtain ⟨hxa,hxb⟩ := Finset.mem_inter.mp hx
  have hsub : E a ⊆ E b := by
    intro y hy
    have hpath := hconnected a x hxa y hy
    induction hpath with
    | refl => exact hxb
    | @tail u v hpath hedge ih =>
      exact hboundary b u (ih hedge.1) (fun hu => havoid ⟨u,hedge.1,hu⟩) v hedge.2.2
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro heq
  obtain ⟨y,hy⟩ := hnonempty b
  exact havoid ⟨y,by rw [heq]; exact hsupport b hy,hy⟩

#print axioms avoiding_intersection_strict_subset
end LRX.FootprintGeometry
