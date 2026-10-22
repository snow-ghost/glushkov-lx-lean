import LX.PhaseExchangePrice
import LX.MinimumHeightRanks

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem displacement_offset (p : State n) (a i : Fin n) :
    displacement p a i=(cyclicOffset p a i : ℤ)-height p a := by
  unfold displacement
  rw [clockwise_difference_value]
  have he : permutation p a i-i=cyclicOffset p a i := by
    change p i+(a-p a)-i=p i-i-(p a-a)
    abel
  rw [he]

/-- The exact top set wrapped when moving from anchor a to anchor b. -/
def reanchorSet (p : State n) (a b : Fin n) : Finset (Fin n) :=
  (Finset.univ.filter (fun i => (cyclicOffset p a i).val < (cyclicOffset p a b).val))ᶜ

theorem reanchor_set_card (p : State n) (a b : Fin n) :
    (reanchorSet p a b).card=n-belowCount p a (cyclicOffset p a b).val := by
  rw [reanchorSet,Finset.card_compl]
  simp only [Fintype.card_fin,belowCount]

theorem reanchor_displacement (p : State n) (a b : Fin n) :
    displacement p b=phaseShift (displacement p a) (reanchorSet p a b) := by
  funext i
  rw [displacement_offset,cyclic_offset_reanchor p a b i,cyclic_subtraction_value,reanchor_height]
  unfold phaseShift
  rw [displacement_offset,reanchor_set_card]
  have hc : belowCount p a (cyclicOffset p a b).val ≤ n := by
    unfold belowCount
    exact (Finset.card_filter_le _ _).trans (by simp)
  rw [Nat.cast_sub hc]
  have hi : i ∈ reanchorSet p a b ↔ ¬ (cyclicOffset p a i).val < (cyclicOffset p a b).val := by
    simp [reanchorSet]
  simp only [hi]
  by_cases h : (cyclicOffset p a i).val < (cyclicOffset p a b).val <;> simp [h] <;> ring

theorem displacement_strict_width (p : State n) (a i j : Fin n) :
    displacement p a i-displacement p a j < (n : ℤ) := by
  have hi := displacement_band p a i
  have hj := displacement_band p a j
  omega

theorem reanchor_set_top (p : State n) (a b : Fin n) :
    ∀ i ∈ reanchorSet p a b, ∀ j ∉ reanchorSet p a b,
      displacement p a j ≤ displacement p a i := by
  intro i hi j hj
  simp only [reanchorSet,Finset.mem_compl,Finset.mem_filter,Finset.mem_univ,true_and,not_not] at hi hj
  rw [displacement_offset,displacement_offset]
  omega

/-- All anchored phases of the same input have exactly the same value of
energy minus n times the number of exchanges. -/
theorem anchor_energy_inversion_invariant (p : State n) (a b : Fin n) :
    (energy (displacement p b) : ℤ)-(n : ℤ)*inversions (displacement p b)=
      (energy (displacement p a) : ℤ)-(n : ℤ)*inversions (displacement p a) := by
  have hh := top_phase_energy_inversions (is_lift p a) (reanchorSet p a b)
    (displacement_strict_width p a) (reanchor_set_top p a b)
  rwa [← reanchor_displacement] at hh

/-- Exchange differences across arbitrary actual phases, with every selected
coordinate determined by the original permutation. -/
theorem reanchor_inversion_difference (p : State n) (a b : Fin n) :
    (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
      ((reanchorSet p a b).card : ℤ)*((n : ℤ)-(reanchorSet p a b).card)-
        2*∑ i ∈ reanchorSet p a b,displacement p a i := by
  have hh := top_phase_inversions (is_lift p a) (reanchorSet p a b)
    (displacement_strict_width p a) (reanchor_set_top p a b)
  rwa [← reanchor_displacement] at hh

/-- Minimizing energy and minimizing the exchange price select the same
anchor phases. This does not assert that they minimize the total LX price. -/
theorem minimum_energy_iff_minimum_exchanges (p : State n) (a : Fin n) :
    (∀ b,energy (displacement p a) ≤ energy (displacement p b)) ↔
      ∀ b,inversions (displacement p a) ≤ inversions (displacement p b) := by
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  constructor
  · intro hmin b
    have hh := anchor_energy_inversion_invariant p a b
    have he : (energy (displacement p a) : ℤ) ≤ energy (displacement p b) := by exact_mod_cast hmin b
    by_contra hnot
    have hp : (0 : ℤ) < inversions (displacement p a)-inversions (displacement p b) := by omega
    have hprod := mul_pos hn hp
    nlinarith
  · intro hmin b
    have hh := anchor_energy_inversion_invariant p a b
    have hx : (inversions (displacement p a) : ℤ) ≤ inversions (displacement p b) := by exact_mod_cast hmin b
    have hprod := mul_le_mul_of_nonneg_left hx (le_of_lt hn)
    omega

#print axioms anchor_energy_inversion_invariant
#print axioms reanchor_inversion_difference
#print axioms minimum_energy_iff_minimum_exchanges
end LX.AnchoredPhases
