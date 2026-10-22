import LRX.RankGapCut

namespace LRX.ZeroGap
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Moving the cut into one neighbor gap forces the next linear neighbor
to use a different gap. A returned original extreme arrow is excluded. -/
theorem second_neighbor_after_cut {p : State n} (hp : p.IsCycle) (hsh : FiniteCuts.Shallow p)
    (hno : ∀ x y, ExtremePair p.support x y → p x ≠ y)
    (hcard : 3 ≤ p.support.card) (a b : Fin n) (hab : a.val < b.val)
    (hgap : RankAdjacent p.support a b) :
    ∃ x y, RankAdjacent p.support x y ∧ p x=y ∧
      ¬((x=a ∧ y=b) ∨ (x=b ∧ y=a)) := by
  classical
  let q := FiniteCuts.shiftConjugate p b.val
  have hq : q.IsCycle := FiniteCuts.shift_conjugate_cycle hp b.val
  have hqs : FiniteCuts.Shallow q := FiniteCuts.shallow_shift p hsh b.val
  obtain ⟨u,v,huv,hqv⟩ := shallow_cycle_rank_neighbor hq hqs
  let x : Fin n := u+b
  let y : Fin n := v+b
  have hpv : p x=y := by
    change FiniteCuts.shiftConjugate p b.val u=v at hqv
    rw [FiniteCuts.shift_conjugate_apply] at hqv
    have h := congrArg (fun i : Fin n => i+b) hqv
    simpa only [sub_add_cancel] using h
  have hshift : RankAdjacent (shiftCarrier p.support b) (x-b) (y-b) := by
    change RankAdjacent (FiniteCuts.shiftConjugate p b.val).support u v at huv
    rw [shift_support_carrier] at huv
    simpa only [x,y,add_sub_cancel_right] using huv
  have hxy : RankAdjacent p.support x y := by
    rcases shift_neighbor_cases p.support b x y hshift with h | h
    · exact h
    · exact False.elim (hno x y h hpv)
  refine ⟨x,y,hxy,hpv,?_⟩
  intro hdup
  have he := ordered_gap_becomes_extreme p.support a b hab hgap
  have hc := shift_carrier_card p.support b
  have hsmall : (shiftCarrier p.support b).card ≤ 2 := by
    rcases hdup with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · rw [hx,hy] at hshift
      exact adjacent_extremes_card_le_two _ _ _ hshift he
    · rw [hx,hy] at hshift
      exact adjacent_extremes_card_le_two _ _ _ (rank_adjacent_symm hshift) he
  omega

/-- The two rank-neighbor gaps needed in the large shallow-shell argument.
The proof uses the event-tree neighbor theorem and invariance under a cut
shift, without invoking separable-permutation theory. -/
theorem shallow_cycle_two_rank_neighbors {p : State n} (hp : p.IsCycle)
    (hsh : FiniteCuts.Shallow p)
    (hno : ∀ x y, ExtremePair p.support x y → p x ≠ y) :
    ∃ a b x y, RankAdjacent p.support a b ∧ p a=b ∧
      RankAdjacent p.support x y ∧ p x=y ∧
      ¬((x=a ∧ y=b) ∨ (x=b ∧ y=a)) := by
  obtain ⟨a,b,hab,hpab⟩ := shallow_cycle_rank_neighbor hp hsh
  have hcard : 3 ≤ p.support.card := by
    by_contra h
    have he := adjacent_small_is_extreme p.support a b hab (by omega)
    exact hno a b he hpab
  by_cases hlt : a.val < b.val
  · obtain ⟨x,y,hxy,hp,hneq⟩ := second_neighbor_after_cut hp hsh hno hcard a b hlt hab
    exact ⟨a,b,x,y,hab,hpab,hxy,hp,hneq⟩
  · have hne : a.val ≠ b.val := fun h => hab.2.2.1 (Fin.ext h)
    obtain ⟨x,y,hxy,hp,hneq⟩ := second_neighbor_after_cut hp hsh hno hcard b a (by omega) (rank_adjacent_symm hab)
    exact ⟨a,b,x,y,hab,hpab,hxy,hp,fun h => hneq h.symm⟩

#print axioms second_neighbor_after_cut
#print axioms shallow_cycle_two_rank_neighbors
end LRX.ZeroGap
