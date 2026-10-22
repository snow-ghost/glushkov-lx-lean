import LRX.BoundaryComponentRoot

namespace LRX.CycleFootprint
variable {n : ℕ} [NeZero n]

theorem load_component_footprint_cover {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (a : Active p) {x : Fin n} (hp : LoadPath d a.val x) :
    ∃ b : Active p, x ∈ activeFootprint p d b := by
  induction hp with
  | refl => exact ⟨a,support_subset p d a.val (BufferProgram.mem_own_orbit p a.val a.property)⟩
  | tail hp he ih =>
    obtain ⟨b,_,hb⟩ := loaded_step_footprint hd hshort he
    exact ⟨b,hb⟩

theorem load_boundary_active {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (a : Active p) (x y : Fin n) (hx : LoadPath d a.val x)
    (hadj : Adjacent x y) (hout : ¬LoadPath d x y) : p⁻¹ x ≠ x := by
  obtain ⟨b,hb⟩ := load_component_footprint_cover hd hshort a hx
  have hxorb : x ∈ BufferProgram.orbitLabels p b.val := by
    by_contra hnot
    have hy := boundary_in_support hd b.val x hb hnot y hadj
    exact hout ((load_path_symm d (footprint_load_path hd b.val x hb)).trans
      (footprint_load_path hd b.val y hy))
  have hc := ((BufferProgram.mem_orbitLabels p b.val x).mp hxorb).1
  intro he
  exact b.property (hc.apply_eq_self_iff.mpr he)

#print axioms load_boundary_active
end LRX.CycleFootprint
