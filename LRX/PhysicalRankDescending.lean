import LRX.PhysicalRankTransfer

namespace LRX.PhysicalModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open FiniteRankOrder
variable {n : ℕ} [NeZero n]

theorem rank_transfer_descending_word (w : List Letter) (s q : Configuration n)
    (hpq : Below s.tokens q.tokens) (hc : s.cursor=q.cursor)
    (hw : DescendingWord w q) :
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
      obtain ⟨hadj,hdesc,htail⟩ := hw
      have hcompare := below_compare s.tokens q.tokens hpq q.cursor (q.cursor+1) hadj
      have hq : compareAt q.tokens q.cursor (q.cursor+1)=(step .x q).tokens := by
        simp [compareAt,step,not_le.mpr hdesc]
      rw [hq] at hcompare
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


#print axioms rank_transfer_descending_word
end LRX.PhysicalModel
