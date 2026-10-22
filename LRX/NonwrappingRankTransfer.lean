import LRX.DescendingIntegerWindow

namespace LRX.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteRankOrder
variable {n : ℕ} [NeZero n]

/-- Exchanges stay inside the finite coordinate window; the original word
may contain both increasing and decreasing exchanges. -/
def NonwrappingWord : List Letter → Configuration n → Prop
  | [], _ => True
  | .l::w, s => NonwrappingWord w (step .l s)
  | .r::w, s => NonwrappingWord w (step .r s)
  | .x::w, s => (s.cursor+1).val=s.cursor.val+1 ∧ NonwrappingWord w (step .x s)

theorem rank_transfer_nonwrapping_word (w : List Letter) (s q : Configuration n)
    (hpq : Below s.tokens q.tokens) (hc : s.cursor=q.cursor)
    (hw : NonwrappingWord w q) :
    ∃ v : List Letter, v.length ≤ w.length ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧
      Below (run v s).tokens (run w q).tokens ∧ DescendingWord v s := by
  induction w generalizing s q with
  | nil => exact ⟨[],by simp, rfl,hc,hpq,trivial⟩
  | cons a w ih =>
    cases a with
    | l =>
      obtain ⟨v,hv,hr,hc',hp',hvdesc⟩ := ih (step .l s) (step .l q) hpq (by simp [step,hc]) hw
      refine ⟨.l::v,by simpa using hv,?_,hc',hp',hvdesc⟩
      simpa [LiftedModel.rotationLetters] using congrArg (List.cons Letter.l) hr
    | r =>
      obtain ⟨v,hv,hr,hc',hp',hvdesc⟩ := ih (step .r s) (step .r q) hpq (by simp [step,hc]) hw
      refine ⟨.r::v,by simpa using hv,?_,hc',hp',hvdesc⟩
      simpa [LiftedModel.rotationLetters] using congrArg (List.cons Letter.r) hr
    | x =>
      obtain ⟨hadj,htail⟩ := hw
      have hcompare := below_compare s.tokens q.tokens hpq q.cursor (q.cursor+1) hadj
      have hq : Below (compareAt q.tokens q.cursor (q.cursor+1)) (step .x q).tokens := by
        by_cases hval : (q.tokens q.cursor).val ≤ (q.tokens (q.cursor+1)).val
        · simp only [compareAt,if_pos hval,step]
          exact below_raising_swap q.tokens q.cursor (q.cursor+1) (by omega) hval
        · simp only [compareAt,if_neg hval,step]
          exact below_refl _
      have hcompare := below_trans hcompare hq
      by_cases hs : (s.tokens s.cursor).val ≤ (s.tokens (s.cursor+1)).val
      · have hsp : compareAt s.tokens q.cursor (q.cursor+1)=s.tokens := by
          simp only [← hc,compareAt,if_pos hs]
        rw [hsp] at hcompare
        obtain ⟨v,hv,hr,hc',hp',hvdesc⟩ := ih s (step .x q) hcompare hc htail
        exact ⟨v,by simpa using Nat.le_trans hv (Nat.le_succ w.length),
          by simpa [LiftedModel.rotationLetters] using hr,hc',hp',hvdesc⟩
      · have hsp : compareAt s.tokens q.cursor (q.cursor+1)=(step .x s).tokens := by
          simp only [← hc,compareAt,if_neg hs,step]
        rw [hsp] at hcompare
        obtain ⟨v,hv,hr,hc',hp',hvdesc⟩ := ih (step .x s) (step .x q) hcompare hc htail
        refine ⟨.x::v,by simpa using hv,
          by simpa [LiftedModel.rotationLetters] using hr,hc',hp',?_,not_le.mp hs,hvdesc⟩
        simpa only [hc] using hadj



#print axioms rank_transfer_nonwrapping_word
end LRX.PhysicalModel

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- An arbitrary nonwrapping sorting word supplies its own descending
normalization; exact finite-window rank transfer does not require the service
word to descend at every exchange. -/
theorem nonwrapping_rank_transfer_integer_window (w : List Letter)
    (s q : Configuration n) (H : ℤ)
    (hpq : FiniteRankOrder.Below s.physical.tokens q.physical.tokens)
    (hc : s.physical.cursor=q.physical.cursor) (hz : s.cursor=q.cursor)
    (hw : PhysicalModel.NonwrappingWord w q.physical)
    (hq : (PhysicalModel.run w q.physical).tokens=1) (hs : FiniteWindowState s H) :
    ∃ v : List Letter, rotationLetters v=rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧
      (∀ i, (run v s).position i=H+(i : ℤ)) ∧
      (run v s).physical.tokens=1 ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber s.physical.tokens ∧
      v.length=FiniteCuts.inversionNumber s.physical.tokens+BufferProgram.rotations w := by
  obtain ⟨u,_,hur,_,hu,hdesc⟩ := PhysicalModel.rank_transfer_nonwrapping_word w
    q.physical q.physical (FiniteRankOrder.below_refl _) rfl hw
  rw [hq] at hu
  have hsort := FiniteRankOrder.eq_one_of_below_one _ hu
  obtain ⟨v,hvr,hcursor,hpos,htokens,hx,hlen⟩ :=
    rank_transfer_integer_window u s q H hpq hc hz hdesc hsort hs
  have hrot : BufferProgram.rotations u=BufferProgram.rotations w := congrArg List.length hur
  have hcur : (run u q).cursor=(run w q).cursor := by
    rw [cursor_run,cursor_run]
    have he := congrArg (fun z : List Letter => (z.map increment).sum) hur
    rw [rotation_letters_increment,rotation_letters_increment] at he
    rw [he]
  rw [hrot] at hlen
  exact ⟨v,hvr.trans hur,hcursor.trans hcur,hpos,htokens,hx,hlen⟩

#print axioms nonwrapping_rank_transfer_integer_window
end LRX.LiftedModel
