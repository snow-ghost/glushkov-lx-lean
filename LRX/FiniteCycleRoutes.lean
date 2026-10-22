import LRX.FiniteCycleProfile

/-! Literal routes through finite-cycle peak services. The cursor walk remains
explicit in the price; no geometric bound on that walk is assumed or claimed. -/
namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {b : ℕ} [NeZero b]

def cycleBasePrice (p : State b) : ℤ :=
  (LiftedModel.inversionCount (fun i : Fin b => (p i : ℤ)) : ℤ)+
    ∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|

/-- Assemble available services without losing their target order or prices. -/
theorem assemble_services (l : List (State b)) (allowed : Fin b → Prop)
    (price : State b → ℤ)
    (havail : ∀ q ∈ l, ∃ s : ClosedService b,
      allowed s.port ∧ s.target=q⁻¹ ∧ (s.word.length : ℤ)=price q) :
    ∃ services : List (ClosedService b),
      services.map ClosedService.target=l.map (fun q => q⁻¹) ∧
      (∀ s ∈ services, allowed s.port) ∧
      (services.map (fun s => (s.word.length : ℤ))).sum=(l.map price).sum := by
  induction l with
  | nil => exact ⟨[], rfl, by simp, rfl⟩
  | cons q l ih =>
    obtain ⟨s, ha, ht, hc⟩ := havail q (by simp)
    obtain ⟨ss, htarget, hports, hprice⟩ := ih (fun r hr => havail r (by simp [hr]))
    refine ⟨s::ss, ?_, ?_, ?_⟩
    · simp [ht, htarget]
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ha
      · exact hports t ht
    · simp [hc, hprice]

theorem left_peak_services (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (y : ℕ) (hy : y ≤ b)
    (hpos : ∀ q ∈ l, 0 < leftPeak q y) :
    ∃ services : List (ClosedService b),
      services.map ClosedService.target=l.map (fun q => q⁻¹) ∧
      (∀ s ∈ services, s.port.val+1 ≤ y) ∧
      (services.map (fun s => (s.word.length : ℤ))).sum=
        (l.map (fun q => cycleBasePrice q-2*(leftPeak q y : ℤ))).sum := by
  apply assemble_services l (fun r => r.val+1 ≤ y) (fun q => cycleBasePrice q-2*(leftPeak q y : ℤ))
  intro q hq
  obtain ⟨s, hp, ht, _, hc⟩ := left_peak_service hb q (hcycles q hq) y hy (hpos q hq)
  exact ⟨s, hp, ht, hc⟩

theorem right_peak_services (hb : 2 ≤ b) (l : List (State b))
    (hcycles : ∀ q ∈ l, q.IsCycle) (x : ℕ) (hx : x ≤ b)
    (hpos : ∀ q ∈ l, 0 < rightPeak q x) :
    ∃ services : List (ClosedService b),
      services.map ClosedService.target=l.map (fun q => q⁻¹) ∧
      (∀ s ∈ services, x ≤ s.port.val+1) ∧
      (services.map (fun s => (s.word.length : ℤ))).sum=
        (l.map (fun q => cycleBasePrice q-2*(rightPeak q x : ℤ))).sum := by
  apply assemble_services l (fun r => x ≤ r.val+1) (fun q => cycleBasePrice q-2*(rightPeak q x : ℤ))
  intro q hq
  obtain ⟨s, hp, ht, _, hc⟩ := right_peak_service hb q (hcycles q hq) x hx (hpos q hq)
  exact ⟨s, hp, ht, hc⟩

theorem assembled_route_price (l : List (State b)) (services : List (ClosedService b))
    (price : State b → ℤ)
    (ht : services.map ClosedService.target=l.map (fun q => q⁻¹))
    (hc : (services.map (fun s => (s.word.length : ℤ))).sum=(l.map price).sum)
    (start finish : Fin b) :
    eval (route start finish services)=
      (RotationWords.rotation start)⁻¹*(l.map (fun q => q⁻¹)).prod*RotationWords.rotation finish ∧
    ((route start finish services).length : ℤ)=
      (l.map price).sum+(walkCost start finish services : ℤ) := by
  constructor
  · rw [route_eval, ht]
  · rw [route_length, Nat.cast_add]
    have hcast : (((services.map (fun s => s.word.length)).sum : ℕ) : ℤ)=
        (services.map (fun s => (s.word.length : ℤ))).sum := by simp [Function.comp_def]
    rw [hcast, hc]

#print axioms left_peak_services
#print axioms right_peak_services
#print axioms assembled_route_price
end LRX.FiniteCuts
