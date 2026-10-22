import LRX.ZeroSourceGapSharpWord

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

/-- Both possible original loads of a source gap are paid. -/
theorem source_gap_sharp_word_of_reserves (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (hdef : ((positiveSourceFamily p n).map FillingWindow.deficit).sum+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (hwidth : 2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → x ∉ sourcePackets p)
    (start finish : Fin n)
    (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  by_cases hpos : 0 < portLoad (displacement p.symm) u
  · obtain ⟨hnext,hu'⟩ := consecutive_positive_gap_selected p n u v hu hv huv hgap hpos v.isLt.le
    exact selected_source_gap_sharp_word hn p hmaj hc hk hdef ⟨u,hu'⟩ start finish
      hsu (by simpa only [hnext] using hsv) hfu (by simpa only [hnext] using hfv)
  · have hnon := port_load_nonneg (displacement p.symm) u
    have hz : portLoad (displacement p.symm) u = 0 := by omega
    exact joined_zero_source_gap_sharp_word hn p hmaj hc hk hwidth u v huv hu hv hgap hz
      start finish hsu hsv hfu hfv

/-- All cursor pairs have a sharp word except possibly the two-positive-arc case. -/
theorem canonical_sharp_or_two_arc (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (hdef : ((positiveSourceFamily p n).map FillingWindow.deficit).sum+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (hwidth : 2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (start finish : Fin n) :
    (∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
      (start ≠ finish ∧ JoinedPositiveArcs p hc start finish) := by
  rcases joined_cursor_cases hn p hc hk start finish with h | h | h
  · exact Or.inr h
  · obtain ⟨u,hu,v,hv,huv,hgap,hsu,hsv,hfu,hfv⟩ := h
    exact Or.inl (source_gap_sharp_word_of_reserves hn p hmaj hc hk hdef hwidth u v huv hu hv hgap
      start finish hsu hsv hfu hfv)
  · exact Or.inl (joined_exterior_gap_sharp_word hn p hmaj hc hk hwidth start finish h.1 h.2)

#print axioms canonical_sharp_or_two_arc
end LRX.FiniteCuts
