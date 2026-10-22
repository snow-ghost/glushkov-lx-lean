import LRX.RightRootLoad
import LRX.SelectedPartService

/-! The retained periodic root can be served from the right boundary after
removing finite children lying strictly to the left of its root vertex. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem periodic_remaining_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hstar : RootStar p d r) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i, i ∉ S → i.val < r.val) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad d (r-1) := by
  have hkeep : r ∈ S := by by_contra h; have := hleft r h; omega
  have hroot' : displacement S d r ≠ 0 := by simpa [displacement,hkeep] using hroot
  have hlift := is_lift hd S hS (balance_of_finite_removal hd S hS hfinite)
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := WordReflection.root_star_exact_left_service hn hlift
    (short hshort S) r hroot' (root_star_pruned p d r hstar S hS hkeep)
  rw [pruned_left_port_load p d S hS r hr hfinite hleft] at hprice
  exact ⟨a,ha,ht,hdisp,hprice⟩

end LRX.PrunedLift
namespace LRX.CyclePart
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem selected_part_right_root_service (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hstar : PrunedLift.RootStar p d r)
    (hpart : IsPart selected p)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i ∈ selected.support, i.val < r.val) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=remaining selected p hpart ∧
      a.displacement=PrunedLift.displacement selected.supportᶜ d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d (r-1) := by
  have hS := PrunedLift.complement_invariant p selected.support (support_invariant selected p hpart)
  apply PrunedLift.periodic_remaining_left_service hn hd hshort r hr hroot hstar selected.supportᶜ hS
  · intro i hi
    have hm : i ∈ selected.support := by simpa using hi
    rw [inverse_on_support selected p hpart i hm]
    exact hfinite i hm
  · intro i hi
    exact hleft i (by simpa using hi)

#print axioms selected_part_right_root_service
end LRX.CyclePart
