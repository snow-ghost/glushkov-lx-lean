import LRX.PortEndpoints

/-! Read exact endpoints back in coordinates centered at the initial cursor. -/
namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem run_at_port_position (w : List Letter) (r : Fin n) (z : ℤ) (i : Fin n) :
    (run w (atPort r z)).position i=
      (run w (initial (n := n))).position (i-r)+(i : ℤ)-((i-r : Fin n) : ℤ) := by
  rw [at_port_eq,← rename_run,← translate_run]
  change (run w initial).position ((Equiv.addRight r).symm i)+z+portOffset r z i= _
  simp [portOffset,sub_eq_add_neg]
  ring

theorem initial_endpoints_of_port (w : List Letter) (r : Fin n) (z : ℤ) (d : Fin n → ℤ)
    (hend : ∀ i, (run w (atPort r z)).position i=(i : ℤ)+d i) :
    ∀ i, (run w (initial (n := n))).position i=
      (i : ℤ)+RotationWords.localDisplacement d r i := by
  intro i
  let j := RotationWords.rotation r i
  have hj : j-r=i := by simp [j,RotationWords.rotation,AffineLift.rotation_power_apply]
  have h := hend j
  rw [run_at_port_position,hj] at h
  change (run w initial).position i=(i : ℤ)+d j
  omega

#print axioms initial_endpoints_of_port
end LRX.LiftedModel
