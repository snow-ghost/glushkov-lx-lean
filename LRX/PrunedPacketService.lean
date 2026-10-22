import LRX.PacketExactService
import LRX.PeriodicRemainingService
import LRX.RightSelectedPartService

/-! Remove finite children while retaining every vertex of the root strong
component. Both boundary services preserve the original root discount. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem periodic_packet_remaining_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PacketCover p d 0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hcore : KeepsCore p d 0 S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ)) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad d 0 := by
  have hkeep := hcore 0 Relation.ReflTransGen.refl Relation.ReflTransGen.refl
  have hr : displacement S d 0 ≠ 0 := by simpa [displacement,hkeep] using hroot
  obtain ⟨a,hp,ht,hdisp,hprice⟩ := packet_exact_service hn
    (is_lift hd S hS (balance_of_finite_removal hd S hS hfinite)) (short hshort S) 0 hr
    (packet_cover_pruned p d 0 hcover S hS hcore)
  rw [port_load_of_finite_removal p d S hS hkeep hfinite] at hprice
  exact ⟨a,hp,ht,hdisp,hprice⟩

theorem periodic_packet_remaining_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hcover : PacketCover p d r) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hcore : KeepsCore p d r S)
    (hfinite : ∀ i, i ∉ S → d i=(p.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i, i ∉ S → i.val < r.val) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad d (r-1) := by
  have hkeep := hcore r Relation.ReflTransGen.refl Relation.ReflTransGen.refl
  have hr' : displacement S d r ≠ 0 := by simpa [displacement,hkeep] using hroot
  obtain ⟨a,ha,ht,hdisp,hprice⟩ := WordReflection.packet_exact_left_service hn
    (is_lift hd S hS (balance_of_finite_removal hd S hS hfinite)) (short hshort S) r hr'
    (packet_cover_pruned p d r hcover S hS hcore)
  rw [pruned_left_port_load p d S hS r hr hfinite hleft] at hprice
  exact ⟨a,ha,ht,hdisp,hprice⟩

end LRX.PrunedLift
namespace LRX.CyclePart
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem packet_part_root_service (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PrunedLift.PacketCover p d 0) (hpart : IsPart selected p)
    (hcore : PrunedLift.KeepsCore p d 0 selected.supportᶜ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ)) :
    ∃ a : ExactService n, a.service.port=0 ∧ a.service.target=remaining selected p hpart ∧
      a.displacement=PrunedLift.displacement selected.supportᶜ d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d 0 := by
  have hS := PrunedLift.complement_invariant p selected.support (support_invariant selected p hpart)
  apply PrunedLift.periodic_packet_remaining_service hn hd hshort hroot hcover selected.supportᶜ hS hcore
  intro i hi
  have hm : i ∈ selected.support := by simpa using hi
  rw [inverse_on_support selected p hpart i hm]
  exact hfinite i hm

theorem packet_part_right_root_service (hn : 2 ≤ n) {p selected : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hr : r ≠ 0) (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r)
    (hpart : IsPart selected p) (hcore : PrunedLift.KeepsCore p d r selected.supportᶜ)
    (hfinite : ∀ i ∈ selected.support, d i=(selected.symm i : ℤ)-(i : ℤ))
    (hleft : ∀ i ∈ selected.support, i.val < r.val) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=remaining selected p hpart ∧
      a.displacement=PrunedLift.displacement selected.supportᶜ d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |PrunedLift.displacement selected.supportᶜ d i|)-portLoad d (r-1) := by
  have hS := PrunedLift.complement_invariant p selected.support (support_invariant selected p hpart)
  apply PrunedLift.periodic_packet_remaining_left_service hn hd hshort r hr hroot hcover selected.supportᶜ hS hcore
  · intro i hi
    have hm : i ∈ selected.support := by simpa using hi
    rw [inverse_on_support selected p hpart i hm]
    exact hfinite i hm
  · intro i hi
    exact hleft i (by simpa using hi)

#print axioms packet_part_root_service
#print axioms packet_part_right_root_service
end LRX.CyclePart
