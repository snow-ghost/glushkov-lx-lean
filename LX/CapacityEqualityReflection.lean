import LX.CapacityEqualityReflectionAtZero
import LX.PacketCoordinateSymmetry
import Mathlib

namespace LX.Core.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

/-- The fixed-point cut is selected from the equality case itself. -/
theorem inherited_capacity_equality_reflection
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (h : ℤ)
    (hparity : (n : ℤ)=2*h+1 ∨ (n : ℤ)=2*h+2)
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ)) (hupper : ∀ i, d i ≤ h)
    (hinheritNeg : ∀ i, d i= -h → original i= -h)
    (hinheritPos : ∀ i, d i=h → original i=h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    ∃ r : Fin n, ∀ i : Fin n, (localTarget p 0 r).symm i= -i-(h : Fin n) := by
  classical
  have hh : 2*h ≤ (n : ℤ) := by omega
  obtain ⟨hs,_,_,_⟩ := inherited_capacity_equality_pairs horiginal hmaj hd h hh hband hinheritNeg heq
  let q := shiftedLiftPermutation p 0 h
  have hf := fixed_positions_card q
  change (q.support.card : ℤ)=2*h at hs
  have hpos : 0 < (fixedPositions q).card := by omega
  obtain ⟨r,hr⟩ := Finset.card_pos.mp hpos
  have hrfix : q r=r := (mem_fixedPositions q r).mp hr
  have hdr : d r= -h := (shifted_fixed_iff_negative_extreme hd h hband r).mp hrfix
  have hdlocal : AffineLift.IsLift (localTarget p 0 r) 0 (localDisplacement d r) :=
    recentered_lift (0 : Fin n) r (by simpa using hd)
  have hbalance : (∑ i, localDisplacement original r i)=0 := by
    unfold localDisplacement
    rw [Equiv.sum_comp (L n^r.val)]
    exact horiginal
  have hmajor := majorized_recenter hmaj r
  have hbandlocal : ∀ i, 0 ≤ localDisplacement d r i+h ∧
      localDisplacement d r i+h < (n : ℤ) := fun i => hband ((L n^r.val) i)
  have heqlocal : (LiftedModel.inversionCount
      (fun i : Fin n => (i : ℤ)+localDisplacement d r i) : ℤ)=h*((n : ℤ)-h-1) := by
    rw [inversion_count_recentered (0 : Fin n) r (by simpa using hd)]
    exact heq
  have hzero : shiftedLiftPermutation (localTarget p 0 r) 0 h 0=0 := by
    apply (shifted_fixed_iff_negative_extreme hdlocal h hbandlocal 0).mpr
    rw [local_displacement_zero]
    exact hdr
  have href := inherited_capacity_equality_reflection_at_zero hbalance hmajor hdlocal h hparity
    hbandlocal (fun i => hupper ((L n^r.val) i))
    (fun i hi => hinheritNeg ((L n^r.val) i) hi)
    (fun i hi => hinheritPos ((L n^r.val) i) hi) heqlocal hzero
  refine ⟨r,?_⟩
  intro i
  have hi := href i
  change (localTarget p 0 r).symm i+((0+h : ℤ) : Fin n)= -i at hi
  simp only [zero_add] at hi
  exact eq_sub_of_add_eq hi

/-- Arithmetic conversion between the strip parameter and the research budget Q-m. -/
theorem strict_band_budget_identity :
    ((((n-1)/2 : ℕ) : ℤ)*((n : ℤ)-((n-1)/2 : ℕ)-1))=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hparity : n=2*(n/2) ∨ n=2*(n/2)+1 := by omega
  rcases hparity with he | ho
  · have hh : (((n-1)/2 : ℕ) : ℤ)=((n/2 : ℕ) : ℤ)-1 := by omega
    have hnint : (n : ℤ)=2*((n/2 : ℕ) : ℤ) := by exact_mod_cast he
    rw [hh]
    nlinarith
  · have hh : (n-1)/2=n/2 := by omega
    rw [hh]
    ring

/-- Equality in the actual strict-band budget forces circular reflection after
an internally chosen cut, provided the completion inherits both extremes. -/
theorem strict_capacity_equality_reflection
    {p : State n} {original d : Fin n → ℤ}
    (horiginal : ∑ i, original i=0) (hmaj : AffineLift.Majorized original)
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (hinheritNeg : ∀ i, d i= -(((n-1)/2 : ℕ) : ℤ) → original i= -(((n-1)/2 : ℕ) : ℤ))
    (hinheritPos : ∀ i, d i= (((n-1)/2 : ℕ) : ℤ) → original i= (((n-1)/2 : ℕ) : ℤ))
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)) :
    ∃ r : Fin n, ∀ i : Fin n,
      (localTarget p 0 r).symm i= -i-((((n-1)/2 : ℕ) : ℤ) : Fin n) := by
  have hn : 0<n := Nat.pos_of_ne_zero (NeZero.ne n)
  apply inherited_capacity_equality_reflection horiginal hmaj hd (((n-1)/2 : ℕ) : ℤ)
    (by omega) (strict_short_strip d hshort) (strict_short_upper d hshort)
    hinheritNeg hinheritPos
  rw [strict_band_budget_identity]
  exact heq

#print axioms inherited_capacity_equality_reflection
#print axioms strict_capacity_equality_reflection
end LX.Core.FiniteCuts
