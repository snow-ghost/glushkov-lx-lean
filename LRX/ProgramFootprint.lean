import LRX.OrbitChild

/-! A program using a set of buffer labels preserves every coordinate outside
that set, at all prefixes. This allows insertion of disjoint child cycles. -/
namespace LRX.BufferProgram
variable {n : ℕ}

def ProgramUses (S : Finset (Fin n)) (cs : List (Command n)) : Prop :=
  ∀ c ∈ cs, Uses S c

theorem programUses_append (S : Finset (Fin n)) (u v : List (Command n)) :
    ProgramUses S (u++v) ↔ ProgramUses S u ∧ ProgramUses S v := by
  simp [ProgramUses, List.mem_append, or_imp, forall_and]

theorem programUses_mono {S T : Finset (Fin n)} (hST : S ⊆ T)
    {cs : List (Command n)} (h : ProgramUses S cs) : ProgramUses T cs := by
  intro c hc
  have hu := h c hc
  cases c with
  | forward => trivial
  | backward => trivial
  | exchange j => exact hST hu

theorem run_buffer_mem {S : Finset (Fin n)} (cs : List (Command n)) (t : Logical n)
    (hb : t.buffer ∈ S) (hu : ProgramUses S cs) : (logicalRun cs t).buffer ∈ S := by
  induction cs generalizing t with
  | nil => exact hb
  | cons c cs ih =>
    exact ih _ (step_buffer_mem hb (hu c (by simp))) (fun k hk => hu k (by simp [hk]))

theorem run_outside {S : Finset (Fin n)} (cs : List (Command n)) (t : Logical n)
    (hb : t.buffer ∈ S) (hu : ProgramUses S cs) (i : Fin n) (hi : i ∉ S) :
    (logicalRun cs t).coord i=t.coord i := by
  induction cs generalizing t with
  | nil => rfl
  | cons c cs ih =>
    have hc := hu c (by simp)
    rw [logicalRun, ih _ (step_buffer_mem hb hc) (fun k hk => hu k (by simp [hk]))]
    have hne : i ≠ t.buffer := by intro h; exact hi (h ▸ hb)
    cases c <;> simp [logicalStep, Function.update_of_ne hne]

theorem move_uses (S : Finset (Fin n)) (d : ℤ) : ProgramUses S (move d) := by
  intro c hc
  unfold move at hc
  split_ifs at hc <;> obtain ⟨_, rfl⟩ := List.mem_replicate.mp hc <;> trivial

theorem itinerary_uses (S : Finset (Fin n)) (d : Fin n → ℤ) (path : List (Fin n))
    (hp : ∀ i ∈ path, i ∈ S) : ProgramUses S (itinerary d path) := by
  induction path with
  | nil => simp [ProgramUses, itinerary]
  | cons a rest ih =>
    cases rest with
    | nil => rw [itinerary_single]; exact move_uses S (d a)
    | cons b rest =>
      rw [itinerary_pair, transfer, programUses_append, programUses_append]
      refine ⟨⟨move_uses S _, ?_⟩, ih (fun i hi => hp i (by simp [hi]))⟩
      intro c hc
      have he : c=Command.exchange b := by simpa using hc
      subst c
      exact hp b (by simp)

theorem orbit_child_uses (S : Finset (Fin n)) (p : State n) (d : Fin n → ℤ)
    (a parent : Fin n) (ha : a ∈ S) (hp : parent ∈ S)
    (ho : orbitLabels p a ⊆ S) : ProgramUses S (orbitChild p d a parent) := by
  rw [orbitChild, programUses_append, programUses_append]
  refine ⟨⟨?_, itinerary_uses S _ _ ?_⟩, ?_⟩
  · intro c hc
    have he : c=Command.exchange a := by simpa using hc
    subst c
    exact ha
  · intro i hi
    exact ho (List.mem_toFinset.mpr hi)
  · intro c hc
    have he : c=Command.exchange parent := by simpa using hc
    subst c
    exact hp

#print axioms run_outside
#print axioms orbit_child_uses
end LRX.BufferProgram
