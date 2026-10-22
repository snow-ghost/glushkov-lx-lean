import LRX.SuffixComponentParameters

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The left endpoint of every nontrivial canonical load component is moving. -/
theorem nontrivial_component_left_moved (p : State n) (a : Fin n)
    (hc : 2 ≤ (componentSet p a).card) : p.symm (componentLeft p a) ≠ componentLeft p a := by
  let l := componentLeft p a
  have hw := component_card_eq_width p a
  have hlr : l.val < (componentRight p a).val := by dsimp [l]; omega
  have hp := (CycleFootprint.load_path_symm _ (component_left_path p a)).trans (component_right_path p a)
  have hpos := load_path_crossed_port_positive p hp l (by rfl) hlr
  rw [port_load_eq_twice_half] at hpos
  have hhalf : 0 < halfLoad p.symm (l.val+1) := by omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hhalf
  obtain ⟨hjlo,hjhi⟩ := (mem_forward p.symm (l.val+1) j).mp hj
  have hjpath : CycleFootprint.LoadPath (displacement p.symm) j l := by
    have hh := CycleFootprint.arrow_load_path (displacement p.symm) j (l : ℤ)
      (by unfold displacement; constructor <;> omega)
    simpa only [Int.cast_natCast,Fin.cast_val_eq_self] using hh
  have hal := component_left_path p a
  have hlow := component_left_bound p a j (hal.trans (CycleFootprint.load_path_symm _ hjpath))
  have hje : j = l := by apply Fin.ext; change l.val ≤ j.val at hlow; omega
  subst j
  intro he
  rw [he] at hjhi
  omega

/-- A nontrivial component's geometric left endpoint is its routing root. -/
theorem nontrivial_component_left_root (p : State n) (a : Fin n)
    (hc : 2 ≤ (componentSet p a).card) : componentLeft p a ∈ componentRoots p := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨(mem_support_inverse p _).mpr (nontrivial_component_left_moved p a hc),?_⟩
  intro b hb hp
  exact component_left_bound p a b ((component_left_path p a).trans hp)

theorem component_root_card_ge_two (p : State n) (a : Fin n)
    (ha : a ∈ componentRoots p) : 2 ≤ (componentSet p a).card := by
  have hw := component_nontrivial_width p a (component_root_moved p a ha)
  rw [component_card_eq_width]
  omega

/-- The image of routing roots is precisely the set of nontrivial load components. -/
theorem component_roots_image (p : State n) :
    (componentRoots p).image (componentSet p) = nontrivialSuffixComponents p 0 := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC
    apply Finset.mem_filter.mpr
    refine ⟨?_,component_root_card_ge_two p a ha⟩
    exact Finset.mem_image.mpr ⟨a,by simp,rfl⟩
  · intro hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hC
    refine Finset.mem_image.mpr ⟨componentLeft p a,nontrivial_component_left_root p a hsize,?_⟩
    exact (CycleFootprint.component_eq_of_path _ (component_left_path p a)).symm

/-- There is exactly one routing root per nontrivial component. -/
theorem component_roots_card_eq_blocks (p : State n) :
    (componentRoots p).card = (nontrivialSuffixComponents p 0).card := by
  classical
  rw [← component_roots_image]
  symm
  apply Finset.card_image_iff.mpr
  intro a ha b hb he
  apply component_roots_unique p ha hb
  apply (CycleFootprint.mem_component _ _ _).mp
  change b ∈ componentSet p a
  rw [he]
  exact (CycleFootprint.mem_component _ _ _).mpr Relation.ReflTransGen.refl

#print axioms nontrivial_component_left_moved
#print axioms component_roots_card_eq_blocks
end LRX.FiniteCuts
