import LRX.FiniteRankInverse
import LRX.PhysicalModel
import LRX.AffineDeletion

namespace LRX.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteRankOrder
variable {n : ℕ} [NeZero n]

/-- A finite sorting word: every X is an adjacent descent inside the
coordinate window. L/R may cross the coordinate cut. -/
def DescendingWord : List Letter → Configuration n → Prop
  | [], _ => True
  | .l::w, s => DescendingWord w (step .l s)
  | .r::w, s => DescendingWord w (step .r s)
  | .x::w, s =>
      (s.cursor+1).val=s.cursor.val+1 ∧
      (s.tokens (s.cursor+1)).val < (s.tokens s.cursor).val ∧
      DescendingWord w (step .x s)

/-- Delete ordered comparisons, preserving the physical rotation subsequence
and cursor. The surviving target stays below the original target. -/
theorem rank_transfer_word (w : List Letter) (s q : Configuration n)
    (hpq : Below s.tokens q.tokens) (hc : s.cursor=q.cursor)
    (hw : DescendingWord w q) :
    ∃ v : List Letter, v.length ≤ w.length ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧
      Below (run v s).tokens (run w q).tokens := by
  induction w generalizing s q with
  | nil => exact ⟨[],by simp, rfl,hc,hpq⟩
  | cons a w ih =>
    cases a with
    | l =>
      obtain ⟨v,hv,hr,hc',hp'⟩ := ih (step .l s) (step .l q) hpq (by simp [step,hc]) hw
      refine ⟨.l::v,by simpa using hv,?_,hc',hp'⟩
      simpa [LiftedModel.rotationLetters] using congrArg (List.cons Letter.l) hr
    | r =>
      obtain ⟨v,hv,hr,hc',hp'⟩ := ih (step .r s) (step .r q) hpq (by simp [step,hc]) hw
      refine ⟨.r::v,by simpa using hv,?_,hc',hp'⟩
      simpa [LiftedModel.rotationLetters] using congrArg (List.cons Letter.r) hr
    | x =>
      obtain ⟨hadj,hdesc,htail⟩ := hw
      have hcompare := below_compare s.tokens q.tokens hpq q.cursor (q.cursor+1) hadj
      have hq : compareAt q.tokens q.cursor (q.cursor+1)=(step .x q).tokens := by
        simp [compareAt,step,not_le.mpr hdesc]
      rw [hq] at hcompare
      by_cases hs : (s.tokens s.cursor).val ≤ (s.tokens (s.cursor+1)).val
      · have hsp : compareAt s.tokens q.cursor (q.cursor+1)=s.tokens := by
          simp only [← hc,compareAt,if_pos hs]
        rw [hsp] at hcompare
        obtain ⟨v,hv,hr,hc',hp'⟩ := ih s (step .x q) hcompare hc htail
        exact ⟨v,by simpa using Nat.le_trans hv (Nat.le_succ w.length),
          by simpa [LiftedModel.rotationLetters] using hr,hc',hp'⟩
      · have hsp : compareAt s.tokens q.cursor (q.cursor+1)=(step .x s).tokens := by
          simp only [← hc,compareAt,if_neg hs,step]
        rw [hsp] at hcompare
        obtain ⟨v,hv,hr,hc',hp'⟩ := ih (step .x s) (step .x q) hcompare hc htail
        exact ⟨.x::v,by simpa using hv,
          by simpa [LiftedModel.rotationLetters] using hr,hc',hp'⟩

/-- A sorting LRX-word for q transfers to p, with all L/R letters retained. -/
theorem rank_transfer_sorting_word (w : List Letter) (s q : Configuration n)
    (hpq : Below s.tokens q.tokens) (hc : s.cursor=q.cursor)
    (hw : DescendingWord w q) (hq : (run w q).tokens=1) :
    ∃ v : List Letter, v.length ≤ w.length ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧ (run v s).tokens=1 := by
  obtain ⟨v,hv,hr,hc',hp'⟩ := rank_transfer_word w s q hpq hc hw
  rw [hq] at hp'
  exact ⟨v,hv,hr,hc',eq_one_of_below_one _ hp'⟩

#print axioms rank_transfer_word
#print axioms rank_transfer_sorting_word
end LRX.PhysicalModel
