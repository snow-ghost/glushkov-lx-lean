import LRX.RecenteredLift
import LRX.AffineReducedPrice

/-! Reachable service at an arbitrary chosen port and final phase, with both
external cursor moves paid by actual words. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def portLoad (d : Fin n → ℤ) (r : Fin n) : ℤ :=
  ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ)
    ((i : ℤ)+localDisplacement d r i)

/-- The local service theorem yields an actual word for the original target,
with exact entry/exit costs. Reachability is stated in the recentered lift. -/
theorem paid_root_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (c r : Fin n) (hd : AffineLift.IsLift p (c : ℤ) d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p c r)
        (localDisplacement d r)) 0 i) :
    ∃ w : List Letter,
      eval w=p ∧
      BufferProgram.exchanges w=LiftedModel.inversionCount
        (fun i : Fin n => (i : ℤ)+localDisplacement d r i) ∧
      (w.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+localDisplacement d r i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d r+
        (min r.val (n-r.val) : ℕ)+(min (c-r).val (n-(c-r).val) : ℕ) := by
  have hlift := recentered_lift c r hd
  have hne : localDisplacement d r 0 ≠ 0 := by
    simpa only [local_displacement_zero] using hroot
  have hlocalroot : (localTarget p c r)⁻¹ 0 ≠ 0 := by
    intro h
    apply hne
    exact BufferProgram.fixed_short_displacement hlift 0 (hshort _) h
  obtain ⟨raw, heval, _, _, hx, hprice⟩ :=
    BufferProgram.reachable_service_price hn hlift hlocalroot hreach
  refine ⟨wrap c r raw, wrap_eval p c r raw heval, ?_, ?_⟩
  · simpa only [wrap, BufferProgram.exchanges_append, toPort, spin_exchanges,
      zero_add, add_zero] using hx
  · rw [wrap_length, Nat.cast_add, Nat.cast_add, hprice, local_displacement_mass]
    rfl

#print axioms paid_root_service
end LRX.RotationWords
