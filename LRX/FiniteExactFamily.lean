import LRX.FiniteExactAvailability

/-! Simultaneously choose exact peak services for a finite list of cycles. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ} [NeZero b]

theorem assemble_exact_services (l : List (State b)) (allowed : Fin b → Prop)
    (price : State b → ℤ)
    (havail : ∀ q ∈ l, ∃ a : ExactService b,
      allowed a.service.port ∧ a.service.target=q⁻¹ ∧ a.displacement=displacement q ∧
      (BufferProgram.rotations a.service.word : ℤ)=price q) :
    ∃ services : List (ExactService b),
      services.map (fun a => a.service.target)=l.map (fun q => q⁻¹) ∧
      services.map ExactService.displacement=l.map displacement ∧
      (∀ a ∈ services, allowed a.service.port) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=(l.map price).sum := by
  induction l with
  | nil => exact ⟨[], rfl, rfl, by simp, rfl⟩
  | cons q l ih =>
    obtain ⟨a, ha, ht, hd, hc⟩ := havail q (by simp)
    obtain ⟨ss, htarget, hdisp, hports, hprice⟩ := ih (fun r hr => havail r (by simp [hr]))
    refine ⟨a::ss, ?_, ?_, ?_, ?_⟩
    · simp [ht, htarget]
    · simp [hd, hdisp]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ha
      · exact hports t ht
    · simp [hc, hprice]

theorem left_peak_exact_family (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (y : ℕ) (hy : y ≤ b)
    (hpos : ∀ q ∈ l, 0 < leftPeak q y) :
    ∃ services : List (ExactService b),
      services.map (fun a => a.service.target)=l.map (fun q => q⁻¹) ∧
      services.map ExactService.displacement=l.map displacement ∧
      (∀ a ∈ services, a.service.port.val+1 ≤ y) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
        (l.map (fun q => (∑ i : Fin b, |displacement q i|)-2*(leftPeak q y : ℤ))).sum := by
  apply assemble_exact_services l (fun r => r.val+1 ≤ y)
    (fun q => (∑ i : Fin b, |displacement q i|)-2*(leftPeak q y : ℤ))
  intro q hq
  exact left_peak_exact_service hb q (hcycles q hq) y hy (hpos q hq)

theorem right_peak_exact_family (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (x : ℕ) (hx : x ≤ b)
    (hpos : ∀ q ∈ l, 0 < rightPeak q x) :
    ∃ services : List (ExactService b),
      services.map (fun a => a.service.target)=l.map (fun q => q⁻¹) ∧
      services.map ExactService.displacement=l.map displacement ∧
      (∀ a ∈ services, x ≤ a.service.port.val+1) ∧
      (services.map (fun a => (BufferProgram.rotations a.service.word : ℤ))).sum=
        (l.map (fun q => (∑ i : Fin b, |displacement q i|)-2*(rightPeak q x : ℤ))).sum := by
  apply assemble_exact_services l (fun r => x ≤ r.val+1)
    (fun q => (∑ i : Fin b, |displacement q i|)-2*(rightPeak q x : ℤ))
  intro q hq
  exact right_peak_exact_service hb q (hcycles q hq) x hx (hpos q hq)

#print axioms left_peak_exact_family
#print axioms right_peak_exact_family
end LRX.FiniteCuts
