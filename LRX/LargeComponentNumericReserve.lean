import LRX.SuffixComponentParameters
import Research.CayleyPy.ManyComponentTailBudget

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

/-- The inversion-reserve inequality C7 with actual extracted parameters. -/
theorem large_component_numeric_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
      2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  have hcut := (component_recenter_cut p root).1
  have hLn : L ≤ n := (component_card_lt_of_multiple_roots p hm root).le
  have hcross := suffix_cross_numeric_lower q L hLn hcut
  have hbudget := large_component_reserve_by_sizes hn p hmaj hm root hlarge
  dsimp only at hcross hbudget ⊢
  change _ ≤ ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) at hcross
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) ≤ _ at hbudget
  dsimp only [q,L] at hcross hbudget
  linarith

/-- For at least two external nontrivial components, the reserve pays 2(a+t)
in addition to every original filling deficit and the strict unit. -/
theorem large_component_many_reserve (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let a := (singletonSuffixComponents q L).card
    2 ≤ t → ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
      2*((a : ℤ)+(t : ℤ)) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  dsimp only
  intro ht
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let a := (singletonSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let M : ℤ := ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ))
  have hcut := (component_recenter_cut p root).1
  have hLn : L ≤ n := (component_card_lt_of_multiple_roots p hm root).le
  have hcross : 2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤ M :=
    suffix_cross_numeric_lower q L hLn hcut
  have hv : 2*(t : ℤ) ≤ (v : ℤ) := by exact_mod_cast nontrivial_suffix_size_sum q L
  have ht' : (2 : ℤ) ≤ t := by exact_mod_cast ht
  have hM := CayleyPy.ManyComponentTailBudget.external_cross_minimum
    (t : ℤ) (v : ℤ) (a : ℤ) (a.choose 2 : ℤ) M ht' hv (by positivity) (by positivity) hcross
  have hbudget := large_component_reserve_by_sizes hn p hmaj hm root hlarge
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) ≤ _ at hbudget
  dsimp only [M] at hM
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+2*((a : ℤ)+(t : ℤ)) ≤ _
  omega

#print axioms large_component_numeric_reserve
#print axioms large_component_many_reserve
end LRX.FiniteCuts
