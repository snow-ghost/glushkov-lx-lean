import LRX.FinitePeakPorts
import LRX.SingleCycleServices

/-! A single finite cycle has actual closed services attaining the left/right
peak discounts in their allowed regions. No reachability premise is required. -/
namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {b : ℕ} [NeZero b]

omit [NeZero b] in
theorem displacement_short (p : State b) (i : Fin b) : |displacement p i| < (b : ℤ) := by
  have hi := i.isLt
  have hp := (p i).isLt
  rw [abs_lt]
  unfold displacement
  omega

omit [NeZero b] in
theorem displacement_ne_of_moved (p : State b) (i : Fin b) (hi : p i ≠ i) : displacement p i ≠ 0 := by
  intro h
  apply hi
  apply Fin.ext
  unfold displacement at h
  omega

omit [NeZero b] in
theorem displacement_endpoint (p : State b) :
    (fun i : Fin b => (i : ℤ)+displacement p i)=(fun i => (p i : ℤ)) := by
  funext i
  simp [displacement]

theorem left_peak_service (hb : 2 ≤ b) (p : State b) (hp : p.IsCycle)
    (y : ℕ) (hy : y ≤ b) (hpos : 0 < leftPeak p y) :
    ∃ service : ClosedService b, service.port.val+1 ≤ y ∧ service.target=p⁻¹ ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) : ℤ)+
        (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)-2*(leftPeak p y : ℤ) := by
  obtain ⟨i, hi, hiy, hload⟩ := left_peak_port p y hy hpos
  obtain ⟨s, hs, ht, hx, hl⟩ := single_cycle_right_service (p := p⁻¹) hb hp.inv
    (canonical_lift p) (displacement_short p) i (displacement_ne_of_moved p i hi)
  rw [displacement_endpoint] at hx hl
  rw [port_load_eq_twice_half, hload] at hl
  refine ⟨s, ?_, ht, hx, ?_⟩
  · rw [hs]; exact hiy
  · exact hl

theorem right_peak_service (hb : 2 ≤ b) (p : State b) (hp : p.IsCycle)
    (x : ℕ) (hx : x ≤ b) (hpos : 0 < rightPeak p x) :
    ∃ service : ClosedService b, x ≤ service.port.val+1 ∧ service.target=p⁻¹ ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) : ℤ)+
        (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)-2*(rightPeak p x : ℤ) := by
  obtain ⟨i, hi, hxi, hload⟩ := right_peak_port p x hx hpos
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    simp only [Fin.val_zero, half_load_zero] at hload
    omega
  have hv : (i-1 : Fin b).val+1=i.val := by
    rw [Fin.val_sub_one_of_ne_zero hi0]
    have hne := Fin.val_ne_zero_iff.mpr hi0
    omega
  obtain ⟨s, hs, ht, he, hl⟩ := single_cycle_left_service (p := p⁻¹) hb hp.inv
    (canonical_lift p) (displacement_short p) i (displacement_ne_of_moved p i hi)
  rw [displacement_endpoint] at he hl
  rw [port_load_eq_twice_half, hv, hload] at hl
  refine ⟨s, ?_, ht, he, ?_⟩
  · rw [hs, hv]; exact hxi
  · exact hl

#print axioms left_peak_service
#print axioms right_peak_service
end LRX.FiniteCuts
