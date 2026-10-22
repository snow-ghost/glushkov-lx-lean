import LRX.PhysicalDescendingPrice

namespace LRX.LiftedModel
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def FiniteWindowState (s : Configuration n) (H : ℤ) : Prop :=
  ∀ i, s.position i=H+(s.physical.tokens.symm i : ℤ)

theorem finite_window_step (a : Letter) (s : Configuration n) (H : ℤ)
    (hs : FiniteWindowState s H)
    (hadj : a=.x → (s.physical.cursor+1).val=s.physical.cursor.val+1) :
    FiniteWindowState (step a s) H := by
  intro i
  cases a with
  | l => exact hs i
  | r => exact hs i
  | x =>
    have hc := hadj rfl
    let p := s.physical.tokens
    let c := s.physical.cursor
    have hne : p c ≠ p (c+1) := by
      intro he
      have h := congrArg Fin.val (p.injective he)
      change c.val=(c+1).val at h
      change (c+1).val=c.val+1 at hc
      omega
    change s.position i+(if i=p c then 1 else 0)-(if i=p (c+1) then 1 else 0)=
      H+(Equiv.swap c (c+1) (p.symm i) : ℤ)
    by_cases hi : i=p c
    · subst i
      simp only [ite_true,ite_eq_right hne,sub_zero,Equiv.symm_apply_apply,Equiv.swap_apply_left]
      rw [hs]
      change H+(p.symm (p c) : ℤ)+1=H+((c+1).val : ℤ)
      rw [Equiv.symm_apply_apply]
      change (c+1).val=c.val+1 at hc
      omega
    · by_cases hj : i=p (c+1)
      · subst i
        simp only [ite_eq_right hi,ite_true,add_zero,Equiv.symm_apply_apply,Equiv.swap_apply_right]
        rw [hs]
        change H+(p.symm (p (c+1)) : ℤ)-1=H+(c : ℤ)
        rw [Equiv.symm_apply_apply]
        change (c+1).val=c.val+1 at hc
        omega
      · simp only [ite_eq_right hi,ite_eq_right hj,add_zero,sub_zero]
        have h0 : p.symm i ≠ c := by intro he; exact hi (by simpa using congrArg p he)
        have h1 : p.symm i ≠ c+1 := by intro he; exact hj (by simpa using congrArg p he)
        rw [Equiv.swap_apply_of_ne_of_ne h0 h1]
        exact hs i

theorem descending_preserves_integer_window (w : List Letter) (s : Configuration n) (H : ℤ)
    (hw : PhysicalModel.DescendingWord w s.physical) (hs : FiniteWindowState s H) :
    FiniteWindowState (run w s) H := by
  induction w generalizing s with
  | nil => exact hs
  | cons a w ih =>
    cases a with
    | l => exact ih (step .l s) hw (finite_window_step .l s H hs (by simp))
    | r => exact ih (step .r s) hw (finite_window_step .r s H hs (by simp))
    | x => exact ih (step .x s) hw.2.2 (finite_window_step .x s H hs (fun _ => hw.1))

theorem rotation_letters_increment (w : List Letter) :
    ((rotationLetters w).map increment).sum=(w.map increment).sum := by
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp_all [rotationLetters,increment]

/-- Finite rank transfer retains every integer token endpoint and the integer
cursor, and has the exact original inversion-plus-rotation price. -/
theorem rank_transfer_integer_window (w : List Letter) (s q : Configuration n) (H : ℤ)
    (hpq : FiniteRankOrder.Below s.physical.tokens q.physical.tokens)
    (hc : s.physical.cursor=q.physical.cursor) (hz : s.cursor=q.cursor)
    (hw : PhysicalModel.DescendingWord w q.physical)
    (hq : (PhysicalModel.run w q.physical).tokens=1) (hs : FiniteWindowState s H) :
    ∃ v : List Letter, rotationLetters v=rotationLetters w ∧
      (run v s).cursor=(run w q).cursor ∧
      (∀ i, (run v s).position i=H+(i : ℤ)) ∧
      (run v s).physical.tokens=1 ∧
      BufferProgram.exchanges v=FiniteCuts.inversionNumber s.physical.tokens ∧
      v.length=FiniteCuts.inversionNumber s.physical.tokens+BufferProgram.rotations w := by
  obtain ⟨v,_,hr,_,hsort,hdesc,hx,hlen⟩ :=
    PhysicalModel.rank_transfer_sorting_exact_price w s.physical q.physical hpq hc hw hq
  have hwindow := descending_preserves_integer_window v s H hdesc hs
  have htokens : (run v s).physical.tokens=1 := by rw [run_physical]; exact hsort
  refine ⟨v,hr,?_,?_,htokens,hx,hlen⟩
  · rw [cursor_run,cursor_run,hz]
    have he := congrArg (fun z : List Letter => (z.map increment).sum) hr
    rw [rotation_letters_increment,rotation_letters_increment] at he
    rw [he]
  · intro i
    have he := hwindow i
    rw [htokens] at he
    simpa only [← Equiv.Perm.inv_def,inv_one,Equiv.Perm.one_apply] using he

#print axioms descending_preserves_integer_window
#print axioms rank_transfer_integer_window
end LRX.LiftedModel
