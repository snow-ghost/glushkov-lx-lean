import LRX.ProgramFootprint
import LRX.BufferScan

/-! Visited head classes are preserved by insertion of a disjoint child call.
Both endpoints of every program are included in the visit predicate. -/
namespace LRX.BufferProgram
variable {n : ℕ}

def Visits : List (Command n) → Logical n → ℤ → Prop
  | [], t, y => Int.ModEq (BufferMachine.slots n) t.head y
  | c::cs, t, y => Int.ModEq (BufferMachine.slots n) t.head y ∨ Visits cs (logicalStep c t) y

theorem visits_start (cs : List (Command n)) (t : Logical n) (y : ℤ)
    (h : Int.ModEq (BufferMachine.slots n) t.head y) : Visits cs t y := by
  cases cs with
  | nil => exact h
  | cons c cs => exact Or.inl h

theorem visits_end (cs : List (Command n)) (t : Logical n) (y : ℤ)
    (h : Int.ModEq (BufferMachine.slots n) (logicalRun cs t).head y) : Visits cs t y := by
  induction cs generalizing t with
  | nil => exact h
  | cons c cs ih => exact Or.inr (ih _ h)

theorem visits_append (u v : List (Command n)) (t : Logical n) (y : ℤ) :
    Visits (u++v) t y ↔ Visits u t y ∨ Visits v (logicalRun u t) y := by
  induction u generalizing t with
  | nil =>
    change Visits v t y ↔ Int.ModEq (BufferMachine.slots n) t.head y ∨ Visits v t y
    exact ⟨Or.inr, fun h => h.elim (visits_start v t y) id⟩
  | cons c u ih =>
    simp only [List.cons_append, Visits, logicalRun, ih, or_assoc]

theorem visits_prefix (cs : List (Command n)) (t : Logical n) (y : ℤ) :
    Visits cs t y ↔ ∃ u v, cs=u++v ∧
      Int.ModEq (BufferMachine.slots n) (logicalRun u t).head y := by
  constructor
  · induction cs generalizing t with
    | nil => intro h; exact ⟨[], [], rfl, h⟩
    | cons c cs ih =>
      intro h
      rcases h with h | h
      · exact ⟨[], c::cs, rfl, h⟩
      · obtain ⟨u, v, he, hh⟩ := ih _ h
        exact ⟨c::u, v, by simp [he], hh⟩
  · rintro ⟨u, v, rfl, h⟩
    exact (visits_append u v t y).mpr (Or.inl (visits_end u t y h))

theorem visits_frame {S : Finset (Fin n)} {s t : Logical n}
    (hf : FrameEquivalent S s t) (hb : s.buffer ∈ S)
    (cs : List (Command n)) (hu : ProgramUses S cs) (y : ℤ)
    (hv : Visits cs s y) : Visits cs t y := by
  induction cs generalizing s t with
  | nil => exact hf.head_eq.symm.trans hv
  | cons c cs ih =>
    rcases hv with hv | hv
    · exact Or.inl (hf.head_eq.symm.trans hv)
    · exact Or.inr (ih (step_frame hf hb c) (step_buffer_mem hb (hu c (by simp)))
        (fun k hk => hu k (by simp [hk])) hv)

/-- Old visits survive insertion whenever the child returns an equivalent
parent state. This is the monotonicity needed for finite cycle saturation. -/
theorem visits_insert {S : Finset (Fin n)} (u child v : List (Command n))
    (t : Logical n) (hb : (logicalRun u t).buffer ∈ S)
    (hu : ProgramUses S v)
    (hf : FrameEquivalent S (logicalRun u t) (logicalRun child (logicalRun u t)))
    (y : ℤ) (hv : Visits (u++v) t y) : Visits (u++child++v) t y := by
  rcases (visits_append u v t y).mp hv with hv | hv
  · apply (visits_append (u++child) v t y).mpr
    exact Or.inl ((visits_append u child t y).mpr (Or.inl hv))
  · apply (visits_append (u++child) v t y).mpr
    apply Or.inr
    rw [logicalRun_append]
    exact visits_frame hf hb v hu y hv

theorem move_visits (d z : ℤ) (t : Logical n)
    (hz : min 0 d ≤ z ∧ z ≤ max 0 d) :
    Visits (move (n := n) d) t (t.head+z) := by
  rw [move_split d z hz.1 hz.2]
  apply (visits_append _ _ _ _).mpr
  apply Or.inl
  apply visits_end
  rw [run_move]
  exact Int.ModEq.refl _

#print axioms visits_prefix
#print axioms visits_insert
#print axioms move_visits
end LRX.BufferProgram
