import LRX.PacketPortSymmetry
import LRX.RootCyclePorts

/-! Any mutually reachable packet vertex is an admissible root of the same
packet. Reachability from a moving root preserves nonzero displacement. -/
namespace LRX.PrunedLift
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ}

theorem packet_cover_reroot (p : State n) (d : Fin n → ℤ) (a b : Fin n)
    (hcover : PacketCover p d a) (hab : Reaches p d a b) (hba : Reaches p d b a) :
    PacketCover p d b := by
  intro i hi
  obtain ⟨s,j,has,hsa,he,hj⟩ := hcover i hi
  exact ⟨s,j,hba.trans has,hsa.trans hab,he,hj⟩

theorem moving_reachable (p : State n) (d : Fin n → ℤ) {a b : Fin n}
    (ha : p⁻¹ a ≠ a) (hpath : Reaches p d a b) : p⁻¹ b ≠ b := by
  induction hpath with
  | refl => exact ha
  | tail hpath he ih =>
    rcases he with hc | ⟨hm,_⟩
    · exact fun h => ih (hc.apply_eq_self_iff.mpr h)
    · exact hm

variable [NeZero n]

theorem nonzero_reachable {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (a b : Fin n)
    (ha : d a ≠ 0) (hab : Reaches p d a b) : d b ≠ 0 := by
  have hma : p⁻¹ a ≠ a := fun h => ha (BufferProgram.fixed_short_displacement hd a (hshort a) h)
  have hmb := moving_reachable p d hma hab
  intro hb
  have h := AffineLift.lift_residue hd b
  simp only [hb,Int.cast_zero,add_zero] at h
  exact hmb h.symm

#print axioms packet_cover_reroot
#print axioms nonzero_reachable
end LRX.PrunedLift
