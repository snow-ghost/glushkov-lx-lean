import LRX.FiniteCycleAvailability
import LRX.ReflectedExactService

/-! Both finite peak discounts are attained by services with exact integer endpoints. -/
namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {b : ℕ} [NeZero b]

theorem left_peak_exact_service (hb : 2 ≤ b) (p : State b) (hp : p.IsCycle)
    (y : ℕ) (hy : y ≤ b) (hpos : 0 < leftPeak p y) :
    ∃ a : ExactService b, a.service.port.val+1 ≤ y ∧ a.service.target=p⁻¹ ∧
      a.displacement=displacement p ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)-2*(leftPeak p y : ℤ) := by
  obtain ⟨i, hi, hiy, hload⟩ := left_peak_port p y hy hpos
  obtain ⟨s, hs, ht, hx, hl⟩ := single_cycle_exact_service (p := p⁻¹) hb hp.inv
    (canonical_lift p) (displacement_short p) i (displacement_ne_of_moved p i hi)
  rw [port_load_eq_twice_half, hload] at hl
  refine ⟨s, ?_, ht, hx, ?_⟩
  · rw [hs]; exact hiy
  · exact hl

theorem right_peak_exact_service (hb : 2 ≤ b) (p : State b) (hp : p.IsCycle)
    (x : ℕ) (hx : x ≤ b) (hpos : 0 < rightPeak p x) :
    ∃ a : ExactService b, x ≤ a.service.port.val+1 ∧ a.service.target=p⁻¹ ∧
      a.displacement=displacement p ∧
      (BufferProgram.rotations a.service.word : ℤ)=
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
  obtain ⟨s, hs, ht, he, hl⟩ := WordReflection.single_cycle_exact_left_service (p := p⁻¹) hb hp.inv
    (canonical_lift p) (displacement_short p) i (displacement_ne_of_moved p i hi)
  rw [port_load_eq_twice_half, hv, hload] at hl
  refine ⟨s, ?_, ht, he, ?_⟩
  · rw [hs, hv]; exact hxi
  · exact hl

#print axioms left_peak_exact_service
#print axioms right_peak_exact_service
end LRX.FiniteCuts
