import LRX.FootprintPacket

/-! A path whose edges lie in footprints induces an overlap path. -/
namespace LRX.FootprintGeometry
variable {V C : Type*} [DecidableEq V]

theorem path_covered (E : C → Finset V) (step : V → V → Prop)
    (hcover : ∀ x y, step x y → ∃ c, x ∈ E c ∧ y ∈ E c)
    (a : C) {x y : V} (hx : x ∈ E a) (hpath : Relation.ReflTransGen step x y) :
    ∃ b, OverlapPath E a b ∧ y ∈ E b := by
  induction hpath with
  | refl => exact ⟨a,Relation.ReflTransGen.refl,hx⟩
  | @tail u v hp he ih =>
    obtain ⟨b,hab,hu⟩ := ih
    obtain ⟨c,huc,hvc⟩ := hcover u v he
    exact ⟨c,hab.tail ⟨u,Finset.mem_inter.mpr ⟨hu,huc⟩⟩,hvc⟩

theorem overlap_path_of_covered_path (E : C → Finset V) (step : V → V → Prop)
    (hcover : ∀ x y, step x y → ∃ c, x ∈ E c ∧ y ∈ E c)
    (a b : C) {x y : V} (hx : x ∈ E a) (hy : y ∈ E b)
    (hpath : Relation.ReflTransGen step x y) : OverlapPath E a b := by
  obtain ⟨c,hac,hyc⟩ := path_covered E step hcover a hx hpath
  exact hac.tail ⟨y,Finset.mem_inter.mpr ⟨hyc,hy⟩⟩

#print axioms overlap_path_of_covered_path
end LRX.FootprintGeometry
