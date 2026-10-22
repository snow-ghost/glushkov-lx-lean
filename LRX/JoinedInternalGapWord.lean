import LRX.JoinedSourceGapWord
import LRX.FiniteQuadraticGap

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The old-gap route of (21), using the actual extracted filling and its
already verified maximum two-boundary charge. No cursor order is assumed. -/
theorem joined_internal_gap_word (hn : 2 ≤ n) (p : State n)
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
        2*(bridgeBudget (componentBridges p hc) : ℤ)+(gapCost filling : ℤ)-
        portLoad (displacement p.symm) u := by
  let x := min (start.val-u.val) (finish.val-u.val)
  let y := max (start.val-u.val) (finish.val-u.val)
  have hxy : x ≤ y := by dsimp [x,y]; omega
  have hy : y ≤ v.val-u.val-1 := by dsimp [y]; omega
  have hpositions : (start.val=u.val+x ∧ finish.val=u.val+y) ∨
      (start.val=u.val+y ∧ finish.val=u.val+x) := by
    dsimp [x,y]
    by_cases h : start.val ≤ finish.val
    · left; constructor <;> omega
    · right; constructor <;> omega
  obtain ⟨filling,w,hmatch,he,hl⟩ := joined_source_gap_word hn p hc hk u v huv hu hv hgap x y hxy hy start finish hpositions
  have hK := charge_le_gapCost filling x y hxy hy
  unfold cycleCharge at hK
  exact ⟨filling,w,hmatch,he,by omega⟩

#print axioms joined_internal_gap_word
end LRX.FiniteCuts
