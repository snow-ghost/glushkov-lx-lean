import LRX.PeakReserveBound
import LRX.ComponentCutPeakInvariant

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The original routed word has the second C8 bound with exactly the
normalized U and epsilon used in the actual area and density inequalities. -/
theorem normalized_peak_reserve_bound (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-
      (∑ i, |displacement q.symm i|)
    peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
      (sourceHalfPeak q : ℤ)-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
      (a : ℤ)*(v : ℤ)-eps := by
  dsimp only
  rw [component_cut_source_half_peak,component_cut_displacement_mass]
  exact large_component_peak_reserve_bound hn p hmaj hc hk root hlarge

/-- The necessary unpaid inequality now uses normalized geometry, while B
and the literal target still belong to the original maximal-cut route. -/
theorem normalized_peak_sharp_or_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : JoinedPositiveArcs p hc start finish) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧
      w.length ≤ n.choose 2) ∨
    (let q := localTarget p 0 (componentLeft p root)
     let L := (componentSet p root).card
     let t := (nontrivialSuffixComponents q L).card
     let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
     let a := (singletonSuffixComponents q L).card
     let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-
       (∑ i, |displacement q.symm i|)
     1 ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
       (sourceHalfPeak q : ℤ)-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
       (a : ℤ)*(v : ℤ)-eps) := by
  dsimp only
  rw [component_cut_source_half_peak,component_cut_displacement_mass]
  exact large_component_peak_sharp_or_reserve hn p hmaj hc hk root hlarge start finish hne hboth

#print axioms normalized_peak_reserve_bound
#print axioms normalized_peak_sharp_or_reserve
end LRX.FiniteCuts
