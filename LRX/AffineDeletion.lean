import LRX.BufferProgram
import LRX.EventTrace
import Mathlib

/-! Repeated lifted pairs can be eliminated from every finite LRX word. The
integer endpoint configuration and the entire L/R subsequence are preserved.
Identifying the remaining number of X with affine inversion length is separate. -/
namespace LRX.LiftedModel
variable {n : ℕ} [NeZero n]

def rotationLetters (w : List Letter) : List Letter := w.filter (fun a => a ≠ .x)

omit [NeZero n] in
theorem rotation_letters_delete (u middle v : List Letter) :
    rotationLetters (u++middle++v)=rotationLetters (u++[.x]++middle++[.x]++v) := by
  simp [rotationLetters, List.filter_append]

/-- Finite descent on literal word length removes every repeated lifted pair.
No permutation or winding information is lost, and no L/R letter is changed. -/
theorem affine_pair_reduction (hn : 2 ≤ n) (w : List Letter) (s : Configuration n) :
    ∃ v : List Letter, run v s=run w s ∧ rotationLetters v=rotationLetters w ∧
      (events v s).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
  have aux : ∀ k : ℕ, ∀ w : List Letter, w.length=k → ∀ s : Configuration n,
      ∃ v : List Letter, run v s=run w s ∧ rotationLetters v=rotationLetters w ∧
        (events v s).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro w hw s
      by_cases hnd : (events w s).Nodup
      · exact ⟨w, rfl, rfl, hnd, le_rfl, List.Sublist.refl _⟩
      · obtain ⟨u, middle, tail, he, hk⟩ := repeated_of_not_nodup w s hnd
        let shorter := u++middle++tail
        have hlt : shorter.length < k := by
          dsimp [shorter]
          rw [he] at hw
          simp only [List.length_append, List.length_singleton] at hw ⊢
          omega
        have hend : run shorter s=run w s := by
          rw [he]
          exact (delete_equal_events_context hn u middle tail s hk).symm
        have hrot : rotationLetters shorter=rotationLetters w := by
          rw [he]
          exact rotation_letters_delete u middle tail
        have hdrop : shorter.Sublist w := by
          rw [he]
          have hh := ((List.sublist_append_left u [.x]).append
            (List.sublist_append_left middle [.x])).append (List.Sublist.refl tail)
          simpa only [shorter, List.append_assoc] using hh
        obtain ⟨v, hv, hr, hndv, hlen, hsub⟩ := ih shorter.length hlt shorter rfl s
        refine ⟨v, hv.trans hend, hr.trans hrot, hndv, ?_, hsub.trans hdrop⟩
        omega
  exact aux w.length w rfl s

theorem event_count_length (w : List Letter) (s : Configuration n) :
    (events w s).length=BufferProgram.exchanges w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih => cases a <;> simp [events, BufferProgram.exchanges, ih]

theorem length_eq_event_rotation (w : List Letter) (s : Configuration n) :
    w.length=(events w s).length+BufferProgram.rotations w := by
  induction w generalizing s with
  | nil => rfl
  | cons a w ih =>
    have h := ih (step a s)
    cases a <;> simp_all [events, BufferProgram.rotations] <;> omega

/-- The reduced word has the same paid rotation sequence and the same exact
lifted endpoint as the original word. The trace has no repeated lifted pair. -/
theorem affine_reduced_word (hn : 2 ≤ n) (w : List Letter) :
    ∃ v : List Letter,
      run v (initial (n := n))=run w (initial (n := n)) ∧
      eval v=eval (n := n) w ∧
      rotationLetters v=rotationLetters w ∧
      BufferProgram.rotations v=BufferProgram.rotations w ∧
      (events v (initial (n := n))).Nodup ∧ v.length ≤ w.length ∧ v.Sublist w := by
  obtain ⟨v, he, hr, hnd, hlen, hsub⟩ := affine_pair_reduction hn w (initial (n := n))
  refine ⟨v, he, ?_, hr, ?_, hnd, hlen, hsub⟩
  · have h := congrArg (fun s : Configuration n => PhysicalModel.visible s.physical) he
    simpa only [run_physical, PhysicalModel.visible_run, initial,
      PhysicalModel.visible_initial, one_mul] using h
  · exact congrArg List.length hr

#print axioms affine_pair_reduction
#print axioms affine_reduced_word
end LRX.LiftedModel
