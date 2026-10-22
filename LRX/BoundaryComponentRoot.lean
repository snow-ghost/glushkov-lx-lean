import LRX.LoadComponents
import LRX.MaximalFootprintRoot

namespace LRX.CycleFootprint
variable {n : ℕ} [NeZero n]

theorem boundary_component_reaches {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (root : Active p) (outside : Fin n)
    (hadj : Adjacent root.val outside) (hout : ¬LoadPath d root.val outside)
    {b : Active p} (hb : FootprintGeometry.OverlapPath (activeFootprint p d) root b) :
    PrunedLift.Reaches p d root.val b.val := by
  classical
  let E := activeFootprint p d
  let S := activeSupport p
  have hs : ∀ a : Active p, S a ⊆ E a := fun a => support_subset p d a.val
  have hdom : ∀ a b : Active p, FootprintGeometry.Overlap E a b →
      ¬FootprintGeometry.Passes E S a b → E a ⊂ E b := by
    intro a b hmeet havoid
    exact FootprintGeometry.avoiding_intersection_strict_subset E S Adjacent hs
      (fun a => ⟨a.val,BufferProgram.mem_own_orbit p a.val a.property⟩)
      (fun a => connected hd a.val a.property)
      (fun a => boundary_in_support hd a.val) hmeet havoid
  have hroot : root.val ∈ E root := hs root (BufferProgram.mem_own_orbit p root.val root.property)
  have hp : FootprintGeometry.PassPath E S root b := by
    induction hb with
    | refl => exact Relation.ReflTransGen.refl
    | @tail a b hpath hedge ih =>
      by_contra hn
      have hno : ¬FootprintGeometry.Passes E S a b := fun he => hn (ih.tail he)
      have hstrict := FootprintGeometry.backward_strict_containment E S hs hdom root b hn ih
        (hdom a b hedge hno)
      have hx : root.val ∈ E b := (Finset.ssubset_iff_subset_ne.mp hstrict).1 hroot
      have hsupport : root.val ∈ S b := by
        by_contra hnot
        have hy := boundary_in_support hd b.val root.val hx hnot outside hadj
        have hrb := load_path_of_overlap_path hd (hpath.tail hedge)
        exact hout (hrb.trans (footprint_load_path hd b.val outside hy))
      exact hn (Relation.ReflTransGen.single ⟨root.val,hroot,hsupport⟩)
  exact pass_path_reaches p d hp

#print axioms boundary_component_reaches
theorem boundary_load_reaches {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (root : Active p) (outside : Fin n)
    (hadj : Adjacent root.val outside) (hout : ¬LoadPath d root.val outside)
    (b : Active p) (hb : LoadPath d root.val b.val) :
    PrunedLift.Reaches p d root.val b.val :=
  boundary_component_reaches hd root outside hadj hout
    ((load_component_iff_overlap_component hd hshort root b).mp hb)

#print axioms boundary_load_reaches
end LRX.CycleFootprint
