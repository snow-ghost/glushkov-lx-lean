import LRX.TwoComponentGapRouting

namespace LRX.FiniteCuts
open FiniteWindow RotationWords
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The exterior word is sharp unless the actual map has no isolated vertex,
unit inversion reserve, and zero energy reserve. These are derived conditions. -/
theorem two_component_outer_sharp_or_unit_reserve (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card)
    (start finish : Fin n) (hout : OuterCursorPair p hc start finish) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    ((isolatedVertices p).card=0 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)=1 ∧
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0) := by
  let delta := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)
  let eps := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
  let a := (isolatedVertices p).card
  let B : ℤ := bridgeBudget (componentBridges p hc)
  have hres := two_component_isolated_reserve (by omega) p hmaj hc root hlarge
  change 1 ≤ delta ∧ 3*(a : ℤ) ≤ delta at hres
  have hmass := majorized_canonical_energy p hmaj
  have heps : 0 ≤ eps := by dsimp only [eps]; linarith
  by_cases hpay : 2*B+(a : ℤ) ≤ delta+eps
  · left
    obtain ⟨w,he,hl⟩ := joined_exterior_gap_word (by omega) p hc (by omega) start finish hout.1 hout.2
    have hw := outer_gap_isolated_budget (by omega) p hc (by omega)
    have hwidth : (n : ℤ)+((outerLeft p hc).val : ℤ)-((outerRight p hc).val : ℤ)-1 ≤ (a : ℤ) := by
      dsimp [a]
      have := (outerRight p hc).isLt
      omega
    have hchoose := choose_two_half_identity n
    have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by
      dsimp only [B,delta,eps] at hpay
      linarith
    exact ⟨w,he,by exact_mod_cast hlen⟩
  · right
    have ha : a=0 := by
      by_contra hh
      have hB := maximal_cut_bridge_strict_budget (by omega) p hmax hc (by omega) (by
        change 0 < a
        omega)
      have hB' : B ≤ (a : ℤ) := by dsimp [B,a]; exact_mod_cast (by simpa using hB)
      omega
    have hB := component_bridge_isolated_budget p hc
    change bridgeBudget (componentBridges p hc) ≤ a+1 at hB
    have hB' : B ≤ 1 := by dsimp [B]; omega
    change a=0 ∧ delta=1 ∧ eps=0
    refine ⟨ha,?_,?_⟩ <;> rw [ha] at hpay <;> norm_num only [Nat.cast_zero,add_zero] at hpay <;> omega

/-- The two-component branch has only its true peak case and the explicit
unit-reserve exterior exception left. All internal gaps are paid. -/
theorem two_component_sharp_or_peak_or_unit_reserve (hn : 4 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (root : Fin n)
    (hlarge : (n+1)/2 < (componentSet p root).card) (start finish : Fin n) :
    (∃ w : List Letter, eval w=(rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2) ∨
    ((start ≠ finish ∧ JoinedPositiveArcs p hc start finish) ∨
      (OuterCursorPair p hc start finish ∧ (isolatedVertices p).card=0 ∧
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ)=1 ∧
        ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=0)) := by
  rcases two_component_sharp_or_peak_or_outer hn p hmaj hc root hlarge start finish with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases two_component_outer_sharp_or_unit_reserve hn p hmaj hmax hc root hlarge start finish h with hw | he
    · exact Or.inl hw
    · exact Or.inr (Or.inr ⟨h,he⟩)

#print axioms two_component_outer_sharp_or_unit_reserve
#print axioms two_component_sharp_or_peak_or_unit_reserve
end LRX.FiniteCuts
