import LRX.TwoBlockReflectionBarrier
import LRX.LoadComponentCardRecenter

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- A strictly short lift of the equality reflection has no large load component. -/
theorem reflection_component_card (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (href : ∀ i : Fin n, p.symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n))
    (a : Fin n) : (CycleFootprint.component d a).card ≤ n-n/2 := by
  have hcan := reflection_recenter_one_canonical hn hd hshort href
  have hb := two_block_reflection_component_card hn (localTarget p 0 1)
    (reflection_recenter_one_two_blocks hn p href) (a-1)
  rw [← hcan,load_component_card_recenter,sub_add_cancel] at hb
  exact hb

/-- Equality in the inversion capacity restricts every actual component to ceil(n/2). -/
theorem capacity_equality_component_card (hn : 2 ≤ n)
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ))
    (a : Fin n) : (CycleFootprint.component d a).card ≤ n-n/2 := by
  obtain ⟨r,href⟩ := strict_capacity_equality_reflection horiginal hmaj hd hshort
    hinheritNeg hinheritPos heq
  have hdlocal := recentered_lift (0 : Fin n) r (by simpa using hd)
  have hb := reflection_component_card hn hdlocal
    (fun i => hshort ((L n^r.val) i)) href (a-r)
  rw [load_component_card_recenter,sub_add_cancel] at hb
  exact hb

/-- The strict part of Lemma 12 for a real completed lift with an actual large component. -/
theorem strict_capacity_of_large_component (hn : 2 ≤ n)
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component d a).card) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-1 := by
  have hcap := strict_band_inversion_capacity hd hshort
  by_contra hnot
  have heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by omega
  have hsmall := capacity_equality_component_card hn horiginal hmaj hd hshort
    hinheritNeg hinheritPos heq a
  omega

/-- In particular the original majorized lift itself has a strict reserve when a component is large. -/
theorem majorized_large_component_capacity (hn : 2 ≤ n)
    {p : State n} {d : Fin n → ℤ} (hd : AffineLift.IsLift p 0 d)
    (hmaj : AffineLift.Majorized d) (a : Fin n)
    (hlarge : n-n/2 < (CycleFootprint.component d a).card) :
    (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-1 :=
  strict_capacity_of_large_component hn hd.1 hmaj hd (FiniteWindow.majorized_short hd hmaj)
    (fun _ hi => hi) (fun _ hi => hi) a hlarge

/-- Direct strict inversion reserve for a canonical input of the remaining routing theorem. -/
theorem majorized_canonical_large_component_capacity (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (a : Fin n)
    (hlarge : n-n/2 < (componentSet p a).card) :
    (inversionNumber p : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-1 := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by
    simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have h := majorized_large_component_capacity hn hd hmaj a hlarge
  have hf : (fun i : Fin n => (i : ℤ)+displacement p.symm i)=(fun i => (p.symm i : ℤ)) := by
    funext i
    unfold displacement
    omega
  rw [hf,canonical_inversion_count] at h
  change (inversionNumber p⁻¹ : ℤ) ≤ _ at h
  rwa [inversion_number_inverse] at h

#print axioms reflection_component_card
#print axioms capacity_equality_component_card
#print axioms strict_capacity_of_large_component
#print axioms majorized_canonical_large_component_capacity
end LRX.FiniteCuts
