import LRX.ComponentTailCapacity
import Research.CayleyPy.ManyComponentTailBudget

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- C11 for actual original component arrows. All selections and sign counts
are derived; only the original displacement is majorized. -/
theorem component_short_arrow_energy_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (L : ℕ)
    (ht : 2 ≤ (nontrivialSuffixComponents p L).card) :
    let t := (nontrivialSuffixComponents p L).card
    let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
    2*((n-p.support.card : ℕ) : ℤ)+(t : ℤ)^2-2*((v : ℤ)-(t : ℤ)) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|) := by
  let t := (nontrivialSuffixComponents p L).card
  let v := ∑ C ∈ nontrivialSuffixComponents p L, C.card
  let x (k : ℕ) := n/2-k
  let ε : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  obtain ⟨k,hkt,hkm,hf,hcap⟩ := suffix_component_tail_capacity p hmaj L
  change t ≤ k at hkt
  change (∑ i, |displacement p.symm i|) ≤ 2*((v : ℤ)-(t : ℤ))+
    ((k-t : ℕ) : ℤ)*((n : ℤ)-((k-t : ℕ) : ℤ)) at hcap
  have hcast : ((k-t : ℕ) : ℤ) = (k : ℤ)-(t : ℤ) := by omega
  have hkx : (k : ℤ) = ((n/2 : ℕ) : ℤ)-(x k : ℤ) := by dsimp [x]; omega
  have hn : (n : ℤ) = 2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have htail : ((x k : ℤ)+(t : ℤ))*((x k : ℤ)+(t : ℤ)+(n%2 : ℕ))-
      2*((v : ℤ)-(t : ℤ)) ≤ ε := by
    dsimp only [ε]
    rw [hcast,hkx,hn] at hcap
    rw [hn]
    nlinarith
  have hfixed : ((n-p.support.card : ℕ) : ℤ) ≤ 2*(x k : ℤ)+(n%2 : ℕ) := by
    dsimp [x]
    omega
  have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
  have h := CayleyPy.ManyComponentTailBudget.tail_pays_fixed_positions
    (t : ℤ) ((n%2 : ℕ) : ℤ) (x k : ℤ) ((n-p.support.card : ℕ) : ℤ)
    ((v : ℤ)-(t : ℤ)) ε ht' (by positivity) (by positivity) hfixed htail
  simpa only [pow_two] using h

#print axioms component_short_arrow_energy_deficit
end LRX.FiniteCuts
