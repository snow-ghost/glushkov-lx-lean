import LRX.JoinedSourceSpanWord

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

theorem joined_source_gap_min_word (hn : 2 ≤ n) (p : State n)
    (hc : (componentRoots p).card=k+1) (hk : 0 < k)
    (u v : Fin n) (huv : u.val < v.val) (hu : u ∈ sourcePackets p) (hv : v ∈ sourcePackets p)
    (hgap : ∀ z : Fin n, u.val < z.val → z.val < v.val → z ∉ sourcePackets p)
    (start finish : Fin n) (hsu : u.val ≤ start.val) (hsv : start.val < v.val)
    (hfu : u.val ≤ finish.val) (hfv : finish.val < v.val) :
    ∃ (filling : State (v.val-u.val-1)) (w : List Letter),
      (∀ i, p.symm (FiniteWindow.embed (sourceGapWindow u v huv) i)=
        FiniteWindow.embed (sourceGapWindow u v huv) (filling i)) ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*(bridgeBudget (componentBridges p hc) : ℤ)+
        min ((gapCost filling : ℤ)-portLoad (displacement p.symm) u)
          ((v.val : ℤ)-(u.val : ℤ)-3) := by
  obtain ⟨filling,w,hmatch,he,hl⟩ := joined_internal_gap_word hn p hc hk u v huv hu hv hgap start finish hsu hsv hfu hfv
  obtain ⟨w',he',hl'⟩ := joined_source_span_word hn p hc hk u v huv hu hv start finish hsu hsv hfu hfv
  by_cases hh : (gapCost filling : ℤ)-portLoad (displacement p.symm) u ≤ (v.val : ℤ)-(u.val : ℤ)-3
  · refine ⟨filling,w,hmatch,he,?_⟩
    rw [min_eq_left hh]
    omega
  · refine ⟨filling,w',hmatch,he',?_⟩
    rw [min_eq_right (by omega)]
    omega

#print axioms joined_source_gap_min_word
end LRX.FiniteCuts
