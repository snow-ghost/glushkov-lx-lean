import LRX.VisitedPorts

/-! Every arrow of a cycle service visits every contracted class of its lifted
segment. Together with visit preservation this supports finite saturation. -/
namespace LRX.BufferProgram
variable {n : ℕ}

theorem visits_modEq (cs : List (Command n)) (t : Logical n) {y z : ℤ}
    (hv : Visits cs t y) (he : Int.ModEq (BufferMachine.slots n) y z) : Visits cs t z := by
  induction cs generalizing t with
  | nil => exact hv.trans he
  | cons c cs ih => exact hv.elim (fun h => Or.inl (h.trans he)) (fun h => Or.inr (ih _ h))

theorem head_ready_modEq (t : Logical n) (hh : HeadReady t) :
    Int.ModEq (BufferMachine.slots n) t.head (t.coord t.buffer) := by
  have hz : Int.ModEq (BufferMachine.slots n) (t.coord t.buffer-t.head) 0 := hh
  simpa only [sub_add_cancel, zero_add] using (hz.add_right t.head).symm

theorem itinerary_visits (base d : Fin n → ℤ) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (hstart : t.buffer=a)
    (hcoords : ∀ i ∈ a::rest, t.coord i=base i)
    (hh : HeadReady t) (hc : Compatible base d (a::rest))
    (i : Fin n) (hi : i ∈ a::rest) (z : ℤ)
    (hz : min 0 (d i) ≤ z ∧ z ≤ max 0 (d i)) :
    Visits (itinerary d (a::rest)) t (base i+z) := by
  induction rest generalizing a t with
  | nil =>
    have he : i=a := by simpa using hi
    subst i
    rw [itinerary_single]
    apply visits_modEq _ _ (move_visits (d a) z t hz)
    have hm := (head_ready_modEq t hh).add_right z
    simpa only [hstart, hcoords a (by simp)] using hm
  | cons b rest ih =>
    by_cases he : i=a
    · subst i
      rw [itinerary]
      apply (visits_append _ _ _ _).mpr
      apply Or.inl
      apply visits_modEq _ _ (move_visits (d a) z t hz)
      have hm := (head_ready_modEq t hh).add_right z
      simpa only [hstart, hcoords a (by simp)] using hm
    · have hib : i ∈ b::rest := by simpa only [List.mem_cons, he, false_or] using hi
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hnd
      have hv := itinerary_valid base d a (b::rest) t hnd hstart hcoords hh hc
      rw [itinerary_pair, valid_append] at hv
      rw [itinerary_pair]
      apply (visits_append _ _ _ _).mpr
      apply Or.inr
      apply ih b (logicalRun (transfer (d a) b) t) htail
      · simp only [run_transfer]
      · intro j hj
        have hne : j ≠ t.buffer := by
          rw [hstart]
          intro heq
          exact hnot (heq ▸ hj)
        simp only [run_transfer, Function.update_of_ne hne]
        exact hcoords j (List.mem_cons_of_mem a hj)
      · exact valid_head_ready _ t hh hv.1
      · exact hc.2
      · exact hib

theorem lifted_itinerary_visits [NeZero n] {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (rest : List (Fin n))
    (t : Logical n) (hnd : (a::rest).Nodup) (hstart : t.buffer=a)
    (hcoords : ∀ i ∈ a::rest, t.coord i=PeriodicBuffer.contract (n : ℤ) (i : ℤ))
    (hh : HeadReady t) (hc : Follows p (a::rest))
    (i : Fin n) (hi : i ∈ a::rest) (v : ℤ)
    (hv : min (i : ℤ) ((i : ℤ)+d i) ≤ v ∧ v ≤ max (i : ℤ) ((i : ℤ)+d i)) :
    Visits (itinerary (logicalDelta d) (a::rest)) t (PeriodicBuffer.contract (n : ℤ) v) := by
  have hn : 0 < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hz := contracted_between hn (i : ℤ) ((i : ℤ)+d i) v hv
  have h := itinerary_visits (initialLogical (n := n)).coord (logicalDelta d) a rest t hnd
    hstart hcoords hh (follows_compatible hd _ hc) i hi
    (PeriodicBuffer.contract (n : ℤ) v-PeriodicBuffer.contract (n : ℤ) (i : ℤ)) hz
  simpa only [initialLogical, add_sub_cancel] using h

theorem orbit_child_visits [NeZero n] {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (a : Fin n) (ha : (p⁻¹) a ≠ a) (t : Logical n)
    (hcoords : ∀ i ∈ orbitLabels p a, t.coord i=PeriodicBuffer.contract (n : ℤ) (i : ℤ))
    (hentry : (t.coord a-t.head)%BufferMachine.slots n=0)
    (i : Fin n) (hi : i ∈ orbitLabels p a) (v : ℤ)
    (hv : min (i : ℤ) ((i : ℤ)+d i) ≤ v ∧ v ≤ max (i : ℤ) ((i : ℤ)+d i)) :
    Visits (orbitChild p d a t.buffer) t (PeriodicBuffer.contract (n : ℤ) v) := by
  obtain ⟨rest, he, hnd, hset, hfollow⟩ := exists_orbit_itinerary p a ha
  rw [orbitChild, he]
  apply (visits_append _ _ _ _).mpr
  apply Or.inl
  apply (visits_append _ _ _ _).mpr
  apply Or.inr
  apply lifted_itinerary_visits hd a rest (logicalStep (.exchange a) t) hnd rfl
  · intro j hj
    exact hcoords j (by rw [← hset]; exact List.mem_toFinset.mpr hj)
  · exact hentry
  · exact hfollow
  · simpa only [← hset, List.mem_toFinset] using hi
  · exact hv

#print axioms itinerary_visits
#print axioms orbit_child_visits
end LRX.BufferProgram
