import LRX.PeakActivityBound

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n k : ℕ} [NeZero n]

/-- The actual original maximal-cut peak can be unpaid only below 578.
Both C8 estimates and all geometric cutoff hypotheses are derived. -/
theorem original_unpaid_peak_cutoff (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (hpos : 1 ≤ peakExcess p hc) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577 := by
  apply original_peak_cutoff_of_first_C8 hn p hmaj hmax hc hk root hlarge ht hpos
  dsimp only
  rw [component_cut_source_half_peak,component_cut_displacement_mass]
  have hs : (localTarget p 0 (componentLeft p root)).support.card=p.support.card := by
    rw [local_target_zero]
    simpa only [inv_inv] using Equiv.Perm.card_support_conj
      (σ := (rotation (componentLeft p root))⁻¹) (τ := p)
  rw [hs]
  have hsize : 2 ≤ (componentSet p root).card := by omega
  have hcount := component_cut_external_count p root hsize
  have htcount : (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card=k := by omega
  rw [htcount]
  exact peak_activity_bound hn p hmaj hc hk

/-- Above the proved cutoff the original two-arc word is sharp, with no
unproved arithmetic or geometric budget premise. -/
theorem large_size_two_arc_sharp_word (hn : 578 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : JoinedPositiveArcs p hc start finish) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  apply joined_peak_word_of_nonpositive_excess (by omega) p hc hk start finish hne hboth
  by_contra h
  have hsmall := original_unpaid_peak_cutoff (by omega) p hmaj hmax hc hk root hlarge ht (by omega)
  omega

/-- Every actual two-arc case in this branch has a sharp original-target
word or belongs to the fully proved finite range. -/
theorem actual_two_arc_sharp_or_finite (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card)
    (start finish : Fin n) (hne : start ≠ finish)
    (hboth : JoinedPositiveArcs p hc start finish) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      ((nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577) := by
  by_cases hpay : peakExcess p hc ≤ 0
  · exact Or.inl (joined_peak_word_of_nonpositive_excess hn p hc hk start finish hne hboth hpay)
  · exact Or.inr (original_unpaid_peak_cutoff hn p hmaj hmax hc hk root hlarge ht (by omega))

#print axioms original_unpaid_peak_cutoff
#print axioms large_size_two_arc_sharp_word
#print axioms actual_two_arc_sharp_or_finite
end LRX.FiniteCuts
