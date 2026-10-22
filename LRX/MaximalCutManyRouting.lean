import LRX.PositiveGapRecenter
import LRX.OriginalCutGapReserve

namespace LRX.FiniteCuts
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- All cursor cases are classified and paid in the original cut. Positive
gaps use transferred literal words; zero and exterior gaps use original B. -/
theorem original_cut_sharp_or_two_arc (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      (start ≠ finish ∧ JoinedPositiveArcs p hc start finish) := by
  have hwidth := original_cut_width_reserve (by omega) p hmaj hc hk root hlarge ht
  rcases joined_cursor_cases (by omega) p hc hk start finish with h | h | h
  · exact Or.inr h
  · obtain ⟨u,hu,v,hv,huv,hgap,hsu,hsv,hfu,hfv⟩ := h
    by_cases hpos : 0 < portLoad (displacement p.symm) u
    · exact Or.inl (original_positive_source_gap_sharp_word hn p hmaj (by omega) root
        hlarge ht u v hu hv huv hgap hpos start finish ⟨hsu,hsv⟩ ⟨hfu,hfv⟩)
    · have hz : portLoad (displacement p.symm) u=0 := by
        have := port_load_nonneg (displacement p.symm) u
        omega
      exact Or.inl (joined_zero_source_gap_sharp_word (by omega) p hmaj hc hk hwidth
        u v huv hu hv hgap hz start finish hsu hsv hfu hfv)
  · exact Or.inl (joined_exterior_gap_sharp_word (by omega) p hmaj hc hk hwidth
      start finish h.1 h.2)

/-- Sharp routing for all cursor positions in the actual large-component
branch with at least two exterior components, above the proved cutoff. -/
theorem large_size_many_component_sharp_word (hn : 578 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  rcases original_cut_sharp_or_two_arc (by omega) p hmaj hc hk root hlarge ht start finish with h | h
  · exact h
  · exact large_size_two_arc_sharp_word hn p hmaj hmax hc hk root hlarge ht start finish h.1 h.2

/-- The whole many-component branch, with arbitrary cursors, reduces to the
same finite range. Maximality and all routes refer to the original cut. -/
theorem original_many_component_sharp_or_finite (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (ht : 2 ≤ (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      ((nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
        (componentSet p root).card).card ≤ 7 ∧ n/2 ≤ 288 ∧ n ≤ 577) := by
  rcases original_cut_sharp_or_two_arc hn p hmaj hc hk root hlarge ht start finish with h | h
  · exact Or.inl h
  · exact actual_two_arc_sharp_or_finite (by omega) p hmaj hmax hc hk root hlarge ht start finish h.1 h.2

#print axioms original_cut_sharp_or_two_arc
#print axioms large_size_many_component_sharp_word
#print axioms original_many_component_sharp_or_finite
end LRX.FiniteCuts
