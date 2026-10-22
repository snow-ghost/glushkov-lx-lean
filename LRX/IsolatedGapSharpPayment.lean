import LRX.IsolatedGapWidths
import LRX.SourceGapSharpPayment

namespace LRX.FiniteCuts
open scoped BigOperators
open RotationWords
variable {n k : ℕ} [NeZero n]

/-- The isolated-width reserve pays the literal word for a new bridge gap. -/
theorem joined_bridge_gap_sharp_word (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1)
    (hreserve : 2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (i : Fin k) (start finish : Fin n)
    (hxs : (bridgeEndpoints p hc i).1.val ≤ start.val)
    (hxv : start.val < (bridgeEndpoints p hc i).2.val)
    (hys : (bridgeEndpoints p hc i).1.val ≤ finish.val)
    (hyv : finish.val < (bridgeEndpoints p hc i).2.val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := joined_bridge_gap_word hn p hc i start finish hxs hxv hys hyv
  have hw := bridge_gap_isolated_width p hc i
  have hwidth : ((bridgeEndpoints p hc i).2.val : ℤ)-((bridgeEndpoints p hc i).1.val : ℤ) ≤
      ((isolatedVertices p).card : ℤ)+1 := by omega
  have hmass := majorized_canonical_energy p hmaj
  have hchoose := choose_two_half_identity n
  have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
  exact ⟨w,he,by exact_mod_cast hlen⟩

/-- The same reserve pays the literal exterior-gap word at the current cut. -/
theorem joined_exterior_gap_sharp_word (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (hreserve : 2*(bridgeBudget (componentBridges p hc) : ℤ)+(isolatedVertices p).card+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (start finish : Fin n)
    (hx : (outerRight p hc).val ≤ start.val ∨ start.val < (outerLeft p hc).val)
    (hy : (outerRight p hc).val ≤ finish.val ∨ finish.val < (outerLeft p hc).val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := joined_exterior_gap_word hn p hc hk start finish hx hy
  have hw := outer_gap_isolated_budget hn p hc hk
  have hwidth : (n : ℤ)+((outerLeft p hc).val : ℤ)-((outerRight p hc).val : ℤ)-1 ≤
      ((isolatedVertices p).card : ℤ) := by have := (outerRight p hc).isLt; omega
  have hmass := majorized_canonical_energy p hmaj
  have hchoose := choose_two_half_identity n
  have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
  exact ⟨w,he,by exact_mod_cast hlen⟩

#print axioms joined_bridge_gap_sharp_word
#print axioms joined_exterior_gap_sharp_word
end LRX.FiniteCuts
