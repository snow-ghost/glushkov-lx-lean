import LRX.CycleWinding

/-! A literal child-cycle call with entry and return exchanges. The integer head
may acquire nonzero winding; the suspended parent buffer is returned unchanged. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def childService (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (parent : Fin n) : List (Command n) :=
  [.exchange a] ++ itinerary d (a::rest) ++ [.exchange parent]

theorem child_service_coordinates (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (i : Fin n) :
    (logicalRun (childService d a rest t.buffer) t).coord i =
      t.coord i + if i ∈ a::rest then d i else 0 := by
  simp only [childService, logicalRun_append, logicalRun, logicalStep]
  exact itinerary_coordinates d a rest (logicalStep (.exchange a) t) hnd rfl i

theorem child_service_buffer (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) :
    (logicalRun (childService d a rest t.buffer) t).buffer=t.buffer := by
  simp only [childService, logicalRun_append, logicalRun, logicalStep]

theorem child_service_head (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) :
    (logicalRun (childService d a rest t.buffer) t).head=t.head+((a::rest).map d).sum := by
  simp only [childService, logicalRun_append, logicalRun, logicalStep]
  exact itinerary_head d (a::rest) (logicalStep (.exchange a) t)

theorem child_service_valid (base d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (hout : t.buffer ∉ a::rest)
    (hcoords : ∀ i ∈ a::rest, t.coord i=base i)
    (hh : HeadReady t) (hentry : (t.coord a-t.head)%BufferMachine.slots n=0)
    (hc : Compatible base d (a::rest))
    (hw : BufferMachine.slots n ∣ ((a::rest).map d).sum) :
    Valid (childService d a rest t.buffer) t := by
  have ha : a ≠ t.buffer := by
    intro he
    exact hout (by simp [← he])
  have hent : Admissible (.exchange a) t := ⟨ha, hentry⟩
  let start := logicalStep (.exchange a) t
  have hhs : HeadReady start := step_head_ready (.exchange a) t hh hent
  have hv := itinerary_valid base d a rest start hnd rfl hcoords hhs hc
  have hparent : (logicalRun (itinerary d (a::rest)) start).coord t.buffer=t.coord t.buffer := by
    rw [itinerary_coordinates d a rest start hnd rfl t.buffer, ite_eq_right hout, add_zero]
    rfl
  have hlast : (logicalRun (itinerary d (a::rest)) start).buffer ≠ t.buffer := by
    rw [itinerary_buffer d a rest start rfl]
    intro he
    apply hout
    rw [← he]
    exact List.getLast_mem (by simp)
  have hreturn : Admissible (.exchange t.buffer) (logicalRun (itinerary d (a::rest)) start) := by
    refine ⟨Ne.symm hlast, ?_⟩
    rw [hparent, itinerary_head]
    change (t.coord t.buffer-(t.head+((a::rest).map d).sum))%BufferMachine.slots n=0
    have hzero : Int.ModEq (BufferMachine.slots n) ((a::rest).map d).sum 0 :=
      Int.modEq_zero_iff_dvd.mpr hw
    have hhead : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer-t.head) 0 := hh
    have he := hhead.sub hzero
    simpa only [sub_add_eq_sub_sub, sub_self, Int.zero_emod] using he.eq
  change Valid ([.exchange a] ++ itinerary d (a::rest) ++ [.exchange t.buffer]) t
  rw [valid_append, valid_append]
  exact ⟨⟨⟨hent, True.intro⟩, hv⟩, hreturn, True.intro⟩

theorem child_service_rotations (d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (parent : Fin n) :
    rotations (compile (childService d a rest parent))=
      ((a::rest).map (fun i => (d i).natAbs)).sum := by
  simp only [childService, compile_append, rotations_append]
  simpa [compile, word, rotations] using itinerary_rotation_price d (a::rest)

#print axioms child_service_valid
#print axioms child_service_coordinates
#print axioms child_service_rotations
end LRX.BufferProgram
