import LRX.LargeComponentNumericReserve
import LRX.SourceGapSharpPayment
import LRX.JoinedTwoArcBound

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The excess of the actual two-arc word bound over choose(n,2). -/
noncomputable def peakExcess (p : State n) (hc : (componentRoots p).card=k+1) : ℤ :=
  (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
    2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
    (sourceHalfPeak p : ℤ)-fillingHalfPeakSum p-1-(n.choose 2 : ℤ)

theorem filling_half_peak_sum_nonneg (p : State n) : 0 ≤ fillingHalfPeakSum p := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  positivity

/-- C8's reserve bound for the actual original-map peak price. All component
parameters come from the selected component; no inversion reserve is supplied. -/
theorem large_component_peak_reserve_bound (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
    let a := (singletonSuffixComponents q L).card
    let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
      (sourceHalfPeak p : ℤ)-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-(a : ℤ)*(v : ℤ)-eps := by
  let q := localTarget p 0 (componentLeft p root)
  let L := (componentSet p root).card
  let t := (nontrivialSuffixComponents q L).card
  let v := ∑ C ∈ nontrivialSuffixComponents q L, C.card
  let a := (singletonSuffixComponents q L).card
  have hreserve := large_component_numeric_reserve hn p hmaj (by omega) root hlarge
  have hnonneg : 0 ≤ ((positiveSourceFamily q n).map FillingWindow.deficit).sum := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨A,_,rfl⟩ := List.mem_map.mp hx
    exact inversion_deficit_nonneg A.filling
  have hS := filling_half_peak_sum_nonneg p
  have hN := choose_two_half_identity n
  have ha : (0 : ℤ) ≤ (a.choose 2 : ℤ) := by positivity
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))+(a : ℤ)*(v : ℤ)+(a.choose 2 : ℤ) ≤ _ at hreserve
  dsimp only at ⊢
  change peakExcess p hc ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
    (sourceHalfPeak p : ℤ)-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-(a : ℤ)*(v : ℤ)-
      (((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|))
  unfold peakExcess
  linarith

/-- Nonpositive excess pays a literal original-target word in the two-arc case. -/
theorem joined_peak_word_of_nonpositive_excess (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : JoinedPositiveArcs p hc start finish) (hpay : peakExcess p hc ≤ 0) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := joined_two_arc_word_bound hn p hc hk start finish hne hboth
  refine ⟨w,he,?_⟩
  unfold peakExcess at hpay
  omega

/-- Either the actual two-arc route is paid, or the second C8 inequality
holds necessarily. The peak and bridge budget belong to the original map. -/
theorem large_component_peak_sharp_or_reserve (hn : 2 ≤ n) (p : State n)
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
       (∑ i, |displacement p.symm i|)
     1 ≤ 2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
       (sourceHalfPeak p : ℤ)-2-2*((t : ℤ)-1)*((v : ℤ)-(t : ℤ))-
       (a : ℤ)*(v : ℤ)-eps) := by
  by_cases hpay : peakExcess p hc ≤ 0
  · exact Or.inl (joined_peak_word_of_nonpositive_excess hn p hc hk start finish hne hboth hpay)
  · right
    have hb := large_component_peak_reserve_bound hn p hmaj hc hk root hlarge
    dsimp only at hb ⊢
    omega

#print axioms large_component_peak_reserve_bound
#print axioms joined_peak_word_of_nonpositive_excess
#print axioms large_component_peak_sharp_or_reserve
end LRX.FiniteCuts
