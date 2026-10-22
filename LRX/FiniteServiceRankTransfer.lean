import LRX.ReducedWindowNormal

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Rank transfer from an arbitrary finite-window sorting execution. The
service may have seam exchanges: affine pair reduction removes them, and
comparison normalization supplies the descending lower sorting word. -/
theorem finite_service_rank_transfer (hn : 2 ≤ n) (w : List Letter)
    (s q : Configuration n) (H : ℤ)
    (hpq : FiniteRankOrder.Below s.physical.tokens q.physical.tokens)
    (hc : s.physical.cursor=q.physical.cursor) (hz : s.cursor=q.cursor)
    (ha : Aligned q) (hstart : FiniteWindowState q H)
    (hend : FiniteWindowState (run w q) H)
    (hq : (run w q).physical.tokens=1) (hs : FiniteWindowState s H) :
    ∃ v : List Letter, rotationLetters v=rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧
      (∀ i, (run v s).position i=H+(i : ℤ)) ∧
      (run v s).physical.tokens=1 ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber s.physical.tokens ∧
      v.length=FiniteCuts.inversionNumber s.physical.tokens+BufferProgram.rotations w := by
  obtain ⟨u,hu,hr,hnd,_,_⟩ := affine_pair_reduction hn w q
  have huend : FiniteWindowState (run u q) H := by rwa [hu]
  have hnon := reduced_window_nonwrapping hn u q H ha hstart huend hnd
  have husort : (PhysicalModel.run u q.physical).tokens=1 := by
    rw [← run_physical,hu]
    exact hq
  obtain ⟨v,hvr,hcursor,hpos,htokens,hx,hlen⟩ :=
    nonwrapping_rank_transfer_integer_window u s q H hpq hc hz hnon husort hs
  have hrot : BufferProgram.rotations u=BufferProgram.rotations w := congrArg List.length hr
  rw [hrot] at hlen
  rw [hu] at hcursor
  exact ⟨v,hvr.trans hr,hcursor,hpos,htokens,hx,hlen⟩

#print axioms finite_service_rank_transfer
end LRX.LiftedModel
