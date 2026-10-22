import LRX.LiftedTranslation
import LRX.ClosedReachableService

/-! Exact integer endpoints survive recentering a service at a physical port. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def atPort (r : Fin n) (z : ℤ) : Configuration n :=
  ⟨⟨1,r⟩, fun i => (i : ℤ), z⟩

def portOffset (r : Fin n) (z : ℤ) (i : Fin n) : ℤ :=
  (i : ℤ)-((i-r : Fin n) : ℤ)-z

theorem at_port_eq (r : Fin n) (z : ℤ) :
    atPort r z=rename (Equiv.addRight r).symm (portOffset r z)
      (translate r z (initial (n := n))) := by
  simp only [atPort, rename, translate, initial, PhysicalModel.initial]
  congr 1
  · simp
    ext i
    simp
  · funext i
    simp [portOffset, sub_eq_add_neg]
    ring
  · simp

theorem port_run_positions (w : List Letter) (r : Fin n) (z : ℤ) (d : Fin n → ℤ)
    (hend : ∀ i, (run w (initial (n := n))).position i=
      (i : ℤ)+RotationWords.localDisplacement d r i) :
    ∀ i, (run w (atPort r z)).position i=(i : ℤ)+d i := by
  intro i
  rw [at_port_eq, ← rename_run, ← translate_run]
  change (run w initial).position ((Equiv.addRight r).symm i)+z+portOffset r z i= _
  rw [hend]
  have he : RotationWords.localDisplacement d r ((Equiv.addRight r).symm i)=d i := by
    simp [RotationWords.localDisplacement, AffineLift.rotation_power_apply]
  rw [he]
  simp [portOffset, sub_eq_add_neg]
  ring

#print axioms port_run_positions
end LRX.LiftedModel
