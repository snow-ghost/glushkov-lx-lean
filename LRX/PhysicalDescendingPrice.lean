import LRX.PhysicalRankDescending
import LRX.FiniteAdjacentInversions

namespace LRX.PhysicalModel
variable {n : ℕ} [NeZero n]

theorem descending_exchange_price (w : List Letter) (s : Configuration n)
    (hw : DescendingWord w s) :
    BufferProgram.exchanges w+FiniteCuts.inversionNumber (run w s).tokens=
      FiniteCuts.inversionNumber s.tokens := by
  induction w generalizing s with
  | nil => simp [BufferProgram.exchanges,run]
  | cons a w ih =>
    cases a with
    | l =>
      have ht := ih (step .l s) hw
      simpa [BufferProgram.exchanges,run,step] using ht
    | r =>
      have ht := ih (step .r s) hw
      simpa [BufferProgram.exchanges,run,step] using ht
    | x =>
      obtain ⟨hadj,hdesc,htail⟩ := hw
      have ht := ih (step .x s) htail
      have hx := FiniteCuts.adjacent_swap_inversion_price s.tokens s.cursor (s.cursor+1) hadj hdesc
      change FiniteCuts.inversionNumber (step .x s).tokens+1=_ at hx
      have hex : BufferProgram.exchanges (.x::w)=BufferProgram.exchanges w+1 := by
        simp [BufferProgram.exchanges]
      change BufferProgram.exchanges (.x::w)+FiniteCuts.inversionNumber (run w (step .x s)).tokens=_
      rw [hex]
      omega

theorem descending_sorting_price (w : List Letter) (s : Configuration n)
    (hw : DescendingWord w s) (hs : (run w s).tokens=1) :
    BufferProgram.exchanges w=FiniteCuts.inversionNumber s.tokens := by
  have he := descending_exchange_price w s hw
  rw [hs] at he
  have hzero : FiniteCuts.inversionNumber (1 : State n)=0 := by
    simp only [FiniteCuts.inversionNumber,Equiv.Perm.one_apply]
    have hnot : ∀ i j : Fin n, ¬(i.val < j.val ∧ j.val < i.val) := by
      intro i j h; omega
    simp only [hnot,ite_false,Finset.sum_const_zero]
  simpa only [hzero,Nat.add_zero] using he

#print axioms descending_exchange_price
#print axioms descending_sorting_price

theorem rank_transfer_sorting_exact_price (w : List Letter) (s q : Configuration n)
    (hpq : FiniteRankOrder.Below s.tokens q.tokens) (hc : s.cursor=q.cursor)
    (hw : DescendingWord w q) (hq : (run w q).tokens=1) :
    ∃ v : List Letter, v.length ≤ w.length ∧
      LiftedModel.rotationLetters v=LiftedModel.rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧ (run v s).tokens=1 ∧ DescendingWord v s ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber s.tokens ∧
      v.length=FiniteCuts.inversionNumber s.tokens+BufferProgram.rotations w := by
  obtain ⟨v,hv,hr,hc',hp',hdesc⟩ := rank_transfer_descending_word w s q hpq hc hw
  rw [hq] at hp'
  have hsort := FiniteRankOrder.eq_one_of_below_one _ hp'
  have hx := descending_sorting_price v s hdesc hsort
  have hlen := LiftedModel.length_eq_event_rotation v (LiftedModel.initial (n:=n))
  rw [LiftedModel.event_count_length,hx] at hlen
  have hrot : BufferProgram.rotations v=BufferProgram.rotations w := congrArg List.length hr
  rw [hrot] at hlen
  exact ⟨v,hv,hr,hc',hsort,hdesc,hx,hlen⟩

#print axioms rank_transfer_sorting_exact_price
end LRX.PhysicalModel
