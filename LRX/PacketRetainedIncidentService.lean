import LRX.PacketIncidentLoad
import LRX.PacketExactService
import LRX.FiniteRemovalBalance

/-! Any invariant retained set containing the whole packet has an exact
service at either incident port of any packet vertex, with the original load. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem retained_incident_packet_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d 0 ≠ 0)
    (hcover : PacketCover p d 0) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hkeep : KeepsCore p d 0 S)
    (r port : Fin n) (hr : InCore p d 0 r) (hp : port=r ∨ port+1=r) :
    ∃ a : ExactService n, a.service.port=port ∧ a.service.target=permutation p S hS ∧
      a.displacement=displacement S d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |displacement S d i|)-portLoad d port := by
  have hmov : p⁻¹ 0 ≠ 0 := fun h => hroot (BufferProgram.fixed_short_displacement hd 0 (hshort 0) h)
  have hfinite (i : Fin n) (hi : i ∉ S) : d i=(p.symm i : ℤ)-(i : ℤ) :=
    outside_core_canonical hd hcover hmov i (fun hc => hi (hkeep i hc.1 hc.2))
  have hdS := is_lift hd S hS (balance_of_finite_removal hd S hS hfinite)
  have hshortS := short hshort S
  have hrS : r ∈ S := hkeep r hr.1 hr.2
  have hnonzero : displacement S d r ≠ 0 := by
    simpa [displacement,hrS] using nonzero_reachable hd hshort 0 r hroot hr.1
  have hcoverR := packet_cover_reroot p d 0 r hcover hr.1 hr.2
  have hkeepR : KeepsCore p d r S := fun i hri hir => hkeep i (hr.1.trans hri) (hir.trans hr.2)
  have hcoverS := packet_cover_pruned p d r hcoverR S hS hkeepR
  have hload := port_load_keeps_core hcover hmov S hkeep r port hr hp
  rcases hp with hp | hp
  · subst port
    obtain ⟨a,ha,ht,hdisp,hprice⟩ := packet_exact_service hn hdS hshortS r hnonzero hcoverS
    rw [hload] at hprice
    exact ⟨a,ha,ht,hdisp,hprice⟩
  · have hport : port=r-1 := by linear_combination hp
    obtain ⟨a,ha,ht,hdisp,hprice⟩ := WordReflection.packet_exact_left_service hn hdS hshortS r hnonzero hcoverS
    rw [← hport,hload] at hprice
    exact ⟨a,ha.trans hport.symm,ht,hdisp,hprice⟩

#print axioms retained_incident_packet_service
end LRX.PrunedLift
