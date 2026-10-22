import LRX.BufferItinerary

/-! A frame rule for suspended buffer services. A nested call may change
unprotected labels and shift the integer head by a multiple of n-1. A parent
program using only protected labels remains legal and has the same coordinate
effect on them. This proves resumption, not existence of a covering scheduler. -/
namespace LRX.BufferProgram
variable {n : ℕ}

structure FrameEquivalent (active : Finset (Fin n)) (s t : Logical n) : Prop where
  buffer_eq : s.buffer=t.buffer
  head_eq : Int.ModEq (BufferMachine.slots n) s.head t.head
  coord_eq : ∀ i ∈ active, s.coord i=t.coord i

def Uses (active : Finset (Fin n)) : Command n → Prop
  | .forward | .backward => True
  | .exchange j => j ∈ active

theorem step_buffer_mem {active : Finset (Fin n)} {s : Logical n} {c : Command n}
    (hb : s.buffer ∈ active) (hu : Uses active c) :
    (logicalStep c s).buffer ∈ active := by
  cases c with
  | forward => exact hb
  | backward => exact hb
  | exchange j => exact hu

theorem frame_admissible {active : Finset (Fin n)} {s t : Logical n}
    (hf : FrameEquivalent active s t) {c : Command n}
    (hu : Uses active c) (hv : Admissible c s) : Admissible c t := by
  cases c with
  | forward => trivial
  | backward => trivial
  | exchange j =>
    refine ⟨by simpa only [← hf.buffer_eq] using hv.1, ?_⟩
    have he : Int.ModEq (BufferMachine.slots n) (s.coord j-s.head) (t.coord j-t.head) := by
      rw [hf.coord_eq j hu]
      exact (Int.ModEq.refl _).sub hf.head_eq
    exact he.eq.symm.trans hv.2

theorem step_frame {active : Finset (Fin n)} {s t : Logical n}
    (hf : FrameEquivalent active s t) (hb : s.buffer ∈ active)
    (c : Command n) : FrameEquivalent active (logicalStep c s) (logicalStep c t) := by
  cases c with
  | forward =>
    refine ⟨hf.buffer_eq, hf.head_eq.add_right 1, ?_⟩
    intro i hi
    simp only [logicalStep]
    rw [hf.coord_eq s.buffer hb, hf.buffer_eq]
    by_cases he : i=t.buffer
    · subst i; simp
    · simp only [Function.update_of_ne he]
      exact hf.coord_eq i hi
  | backward =>
    refine ⟨hf.buffer_eq, hf.head_eq.sub_right 1, ?_⟩
    intro i hi
    simp only [logicalStep]
    rw [hf.coord_eq s.buffer hb, hf.buffer_eq]
    by_cases he : i=t.buffer
    · subst i; simp
    · simp only [Function.update_of_ne he]
      exact hf.coord_eq i hi
  | exchange j => exact ⟨rfl, hf.head_eq, hf.coord_eq⟩

theorem run_frame {active : Finset (Fin n)} {s t : Logical n}
    (hf : FrameEquivalent active s t) (hb : s.buffer ∈ active)
    (cs : List (Command n)) (hu : ∀ c ∈ cs, Uses active c) :
    FrameEquivalent active (logicalRun cs s) (logicalRun cs t) ∧
      (logicalRun cs s).buffer ∈ active := by
  induction cs generalizing s t with
  | nil => exact ⟨hf, hb⟩
  | cons c cs ih =>
    exact ih (step_frame hf hb c) (step_buffer_mem hb (hu c (by simp)))
      (fun k hk => hu k (by simp [hk]))

theorem valid_frame {active : Finset (Fin n)} {s t : Logical n}
    (hf : FrameEquivalent active s t) (hb : s.buffer ∈ active)
    (cs : List (Command n)) (hu : ∀ c ∈ cs, Uses active c)
    (hv : Valid cs s) : Valid cs t := by
  induction cs generalizing s t with
  | nil => trivial
  | cons c cs ih =>
    have hc := hu c (by simp)
    exact ⟨frame_admissible hf hc hv.1,
      ih (step_frame hf hb c) (step_buffer_mem hb hc)
        (fun k hk => hu k (by simp [hk])) hv.2⟩

#print axioms run_frame
#print axioms valid_frame
end LRX.BufferProgram
