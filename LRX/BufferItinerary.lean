import LRX.BufferTransfer

/-! Executable nonrepeating buffer itineraries. Compatibility is a local residue
condition on successive named labels; validity of the emitted LRX program is
proved for arbitrary itinerary length. Recursive cycle coverage is not asserted. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def itinerary (d : Fin n → ℤ) : List (Fin n) → List (Command n)
  | [] => []
  | a :: rest => move (d a) ++ match rest with
    | [] => []
    | b :: _ => [.exchange b] ++ itinerary d rest

def Compatible (base d : Fin n → ℤ) : List (Fin n) → Prop
  | [] => True
  | a :: rest => match rest with
    | [] => True
    | b :: _ => Int.ModEq (BufferMachine.slots n) (base a+d a) (base b) ∧ Compatible base d rest

theorem itinerary_single (d : Fin n → ℤ) (a : Fin n) : itinerary d [a] = move (d a) := by
  simp [itinerary]

theorem itinerary_pair (d : Fin n → ℤ) (a b : Fin n) (rest : List (Fin n)) :
    itinerary d (a::b::rest) = transfer (d a) b ++ itinerary d (b::rest) := by
  simp only [itinerary, transfer, List.append_assoc]

def HeadReady (t : Logical n) : Prop := (t.coord t.buffer-t.head)%BufferMachine.slots n=0

theorem step_head_ready (c : Command n) (t : Logical n)
    (hh : HeadReady t) (hc : Admissible c t) : HeadReady (logicalStep c t) := by
  dsimp [HeadReady] at hh
  cases c with
  | forward =>
    simp only [HeadReady, logicalStep, Function.update_self]
    rw [show t.coord t.buffer+1-(t.head+1)=t.coord t.buffer-t.head by ring]
    exact hh
  | backward =>
    simp only [HeadReady, logicalStep, Function.update_self]
    rw [show t.coord t.buffer-1-(t.head-1)=t.coord t.buffer-t.head by ring]
    exact hh
  | exchange j => exact hc.2

theorem valid_head_ready (cs : List (Command n)) (t : Logical n)
    (hh : HeadReady t) (hv : Valid cs t) : HeadReady (logicalRun cs t) := by
  induction cs generalizing t with
  | nil => exact hh
  | cons c cs ih => exact ih _ (step_head_ready c t hh hv.1) hv.2

theorem itinerary_valid (base d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (hstart : t.buffer=a)
    (hcoords : ∀ i ∈ a::rest, t.coord i=base i)
    (hh : HeadReady t) (hc : Compatible base d (a::rest)) :
    Valid (itinerary d (a::rest)) t := by
  induction rest generalizing a t with
  | nil => rw [itinerary_single]; exact move_valid _ _
  | cons b rest ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
    have hba : b ≠ a := by intro h; subst b; exact hnot (by simp)
    have hne : b ≠ t.buffer := by rwa [hstart]
    have ha := hcoords a (by simp)
    have hb := hcoords b (by simp)
    have hgoal : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer+d a) (t.coord b) := by
      simpa only [hstart, ha, hb] using hc.1
    have hv := transfer_valid (d a) b t hh hne hgoal
    rw [itinerary_pair, valid_append]
    refine ⟨hv, ?_⟩
    apply ih b (logicalRun (transfer (d a) b) t) htail
    · simp only [run_transfer]
    · intro i hi
      have hie : i ≠ t.buffer := by
        rw [hstart]
        intro he
        exact hnot (he ▸ hi)
      simp only [run_transfer, Function.update_of_ne hie]
      exact hcoords i (List.mem_cons_of_mem a hi)
    · exact valid_head_ready _ t hh hv
    · exact hc.2

/-- A nonrepeating itinerary moves each named token exactly by its requested
logical displacement and leaves all other token coordinates unchanged. -/
theorem itinerary_coordinates (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (hstart : t.buffer=a) (i : Fin n) :
    (logicalRun (itinerary d (a::rest)) t).coord i =
      t.coord i + if i ∈ a::rest then d i else 0 := by
  induction rest generalizing a t with
  | nil =>
    rw [itinerary_single, run_move]
    by_cases hi : i=a
    · subst i; simp [shift, hstart]
    · simp [shift, hstart, hi]
  | cons b rest ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
    rw [itinerary_pair, logicalRun_append]
    rw [ih b _ htail (by simp only [run_transfer])]
    by_cases hi : i=a
    · subst i
      simp [run_transfer, hstart, hnot]
    · have hie : i ≠ t.buffer := by rwa [hstart]
      simp [run_transfer, Function.update_of_ne hie, hi]

theorem itinerary_head (d : Fin n → ℤ) (path : List (Fin n)) (t : Logical n) :
    (logicalRun (itinerary d path) t).head = t.head + (path.map d).sum := by
  induction path generalizing t with
  | nil => simp [itinerary, logicalRun]
  | cons a rest ih =>
    cases rest with
    | nil => simp [itinerary_single, run_move, shift]
    | cons b rest =>
      rw [itinerary_pair, logicalRun_append, ih, run_transfer]
      simp [add_assoc]

theorem itinerary_rotation_price (d : Fin n → ℤ) (path : List (Fin n)) :
    rotations (compile (itinerary d path)) = (path.map (fun i => (d i).natAbs)).sum := by
  induction path with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => simp [itinerary_single, move_rotation_price]
    | cons b rest =>
      rw [itinerary_pair, compile_append, rotations_append, transfer_rotation_price, ih]
      rfl

theorem itinerary_length (d : Fin n → ℤ) (path : List (Fin n)) :
    (compile (itinerary d path)).length =
      2*(path.map (fun i => (d i).natAbs)).sum + path.length - 1 := by
  induction path with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => simp [itinerary_single, move_length]
    | cons b rest =>
      rw [itinerary_pair, compile_append, List.length_append, transfer_length, ih]
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem itinerary_correct [NeZero n] (hn : 2 ≤ n) (base d : Fin n → ℤ)
    (a : Fin n) (rest : List (Fin n)) {s : LiftedModel.Configuration n} {t : Logical n}
    (hm : Matches s t) (hnd : (a::rest).Nodup) (hstart : t.buffer=a)
    (hcoords : ∀ i ∈ a::rest, t.coord i=base i)
    (hc : Compatible base d (a::rest)) :
    Matches (LiftedModel.run (compile (itinerary d (a::rest))) s)
      (logicalRun (itinerary d (a::rest)) t) := by
  have hh : HeadReady t := by
    change (t.coord t.buffer-t.head)%BufferMachine.slots n=0
    rw [← hm.1]; exact hm.2.head
  exact compile_correct hn _ hm (itinerary_valid base d a rest t hnd hstart hcoords hh hc)


theorem itinerary_buffer (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hstart : t.buffer=a) :
    (logicalRun (itinerary d (a::rest)) t).buffer = (a::rest).getLast (by simp) := by
  induction rest generalizing a t with
  | nil => simp [itinerary_single, run_move, shift, hstart]
  | cons b rest ih =>
    rw [itinerary_pair, logicalRun_append, ih b _ (by simp only [run_transfer])]
    simp

#print axioms itinerary_correct
#print axioms itinerary_coordinates
#print axioms itinerary_rotation_price
#print axioms itinerary_length
end LRX.BufferProgram
