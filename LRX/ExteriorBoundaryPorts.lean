import LRX.GapBoundaryLoad
import LRX.ArrowLoadPaths
import LRX.PortLoadBalance

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem moving_incident_load (d : Fin n → ℤ) (r : Fin n) (hr : d r ≠ 0) :
    0 < portLoad d r ∨ 0 < portLoad d (r-1) := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · right
    have h := CycleFootprint.arrow_edge_positive d r ((r : ℤ)-1) (by omega) (by omega)
    simpa only [Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,Int.cast_one] using h
  · left
    have h := CycleFootprint.arrow_edge_positive d r (r : ℤ) (by omega) (by omega)
    simpa only [Int.cast_natCast,Fin.cast_val_eq_self] using h

theorem zero_right_load_left_discount {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hr : d r ≠ 0) (hz : portLoad d r=0) :
    2 ≤ portLoad d (r-1) := by
  rcases moving_incident_load d r hr with h | h
  · omega
  · exact positive_port_load_ge_two hd _ h

theorem zero_left_load_right_discount {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (r : Fin n) (hr : d r ≠ 0) (hz : portLoad d (r-1)=0) :
    2 ≤ portLoad d r := by
  rcases moving_incident_load d r hr with h | h
  · exact positive_port_load_ge_two hd _ h
  · omega
end LRX.RotationWords

namespace LRX.FiniteWindow
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem fixed_window_boundary_load {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (W : Window n b) (hoff : W.offset=1)
    (r : Fin n) (hedge : W.offset+b=r.val) (hz : ∀ i, Contains W i → d i=0) :
    portLoad d 0=portLoad d (r-1) := by
  apply gap_boundary_port_load hd W hoff r hedge (1 : State b)
  · intro i
    have h := AffineLift.lift_residue hd (embed W i)
    simpa only [hz _ (contains_embed W i),Int.cast_zero,add_zero,Equiv.Perm.one_apply] using h.symm
  · intro i
    simp [hz _ (contains_embed W i),FiniteCuts.displacement]

#print axioms fixed_window_boundary_load
end LRX.FiniteWindow
