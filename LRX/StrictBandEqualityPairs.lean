import LRX.MajorizedExtremeCount
import LRX.FinitePairCycles

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Equality for a completion with inherited negative extremes forces a shallow
matching. The original majorization is used only to derive the extreme count. -/
theorem inherited_capacity_equality_pairs {p : State n} {c : ℤ}
    {original d : Fin n → ℤ} (horiginal : ∑ i, original i=0)
    (hmaj : AffineLift.Majorized original) (hd : AffineLift.IsLift p c d)
    (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hband : ∀ i, 0 ≤ d i+h ∧ d i+h < (n : ℤ))
    (hinherit : ∀ i, d i= -h → original i= -h)
    (heq : (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=
      h*((n : ℤ)-h-1)) :
    let q := shiftedLiftPermutation p c h
    (q.support.card : ℤ)=2*h ∧ (q.cycleFactorsFinset.card : ℤ)=h ∧
      (∑ i, |displacement q i|)-(inversionNumber q : ℤ)=h ∧
      (∀ r ∈ q.cycleFactorsFinset, r.IsSwap) := by
  have hext := AffineLift.inherited_negative_level_count horiginal hmaj h hh hinherit
  obtain ⟨hs,hc,hdef⟩ := shifted_capacity_equality_support hd h hband heq hext
  dsimp only
  refine ⟨hs,hc,hdef,?_⟩
  apply cycles_are_swaps_of_support_eq_twice_count
  have he : ((shiftedLiftPermutation p c h).support.card : ℤ)=
      2*((shiftedLiftPermutation p c h).cycleFactorsFinset.card : ℤ) := by omega
  exact_mod_cast he

#print axioms inherited_capacity_equality_pairs
end LRX.FiniteCuts
