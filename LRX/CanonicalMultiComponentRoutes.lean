import LRX.JoinedSourceGapMinimum

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- Concrete route data for the remaining numerical payment. Every constructor
records an actual bound on the word for the original permutation. -/
inductive CanonicalRouteCertificate (p : State n) (hc : (componentRoots p).card=k+1)
    (start finish : Fin n) (w : List Letter) : Prop
  | twoArc (hne : start ≠ finish) (hboth : JoinedPositiveArcs p hc start finish)
      (bound : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+((n/2 : ℕ) : ℤ)-
        (sourceHalfPeak p : ℤ)-fillingHalfPeakSum p-1) : CanonicalRouteCertificate p hc start finish w
  | gap (u v : Fin n) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p) (huv : u.val < v.val)
      (hgap : ∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p)
      (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
      (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val)
      (filling : State (v.val-u.val-1))
      (hmatch : ∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i))
      (bound : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        min ((gapCost filling : ℤ)-portLoad (displacement p.symm) u) ((v.val : ℤ)-(u.val : ℤ)-3)) :
      CanonicalRouteCertificate p hc start finish w
  | outer (hpositions : OuterCursorPair p hc start finish)
      (bound : (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+(n : ℤ)+
        ((outerLeft p hc).val : ℤ)-((outerRight p hc).val : ℤ)-1) :
      CanonicalRouteCertificate p hc start finish w

/-- All physical cursor pairs are covered, without a residual geometric route
hypothesis. Sharp numerical payment and the maximum-cut choice are not claimed. -/
theorem canonical_multi_component_routes (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k) (start finish : Fin n) :
    ∃ w : List Letter, eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      CanonicalRouteCertificate p hc start finish w := by
  rcases joined_cursor_cases hn p hc hk start finish with h | h | h
  · obtain ⟨w,he,hl⟩ := joined_two_arc_word_bound hn p hc hk start finish h.1 h.2
    exact ⟨w,he,CanonicalRouteCertificate.twoArc h.1 h.2 hl⟩
  · obtain ⟨u,hu,v,hv,huv,hgap,hsu,hsv,hfu,hfv⟩ := h
    obtain ⟨filling,w,hmatch,he,hl⟩ := joined_source_gap_min_word hn p hc hk u v huv hu hv hgap start finish hsu hsv hfu hfv
    exact ⟨w,he,CanonicalRouteCertificate.gap u v hu hv huv hgap hsu hsv hfu hfv filling hmatch hl⟩
  · obtain ⟨w,he,hl⟩ := joined_exterior_gap_word hn p hc hk start finish h.1 h.2
    exact ⟨w,he,CanonicalRouteCertificate.outer h hl⟩

#print axioms canonical_multi_component_routes
end LRX.FiniteCuts
