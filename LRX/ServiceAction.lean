import LRX.PortEndpoints

/-! Transfer a service endpoint contract to an arbitrary physical state.
This retains integer positions, including previous winding of every token. -/
namespace LRX.LiftedModel
variable {n : ℕ} [NeZero n]

omit [NeZero n] in
theorem state_as_port_rename (s : Configuration n) :
    s=rename s.physical.tokens.symm
      (fun i => s.position i-(s.physical.tokens.symm i : ℤ))
      (atPort s.physical.cursor s.cursor) := by
  cases s with
  | mk physical position cursor =>
    cases physical with
    | mk tokens port =>
      simp only [rename, atPort, Equiv.symm_symm]
      congr 1
      · simp

theorem service_action (w : List Letter) (r : Fin n) (d : Fin n → ℤ)
    (hend : ∀ z i, (run w (atPort r z)).position i=(i : ℤ)+d i)
    (s : Configuration n) (hport : s.physical.cursor=r) (i : Fin n) :
    (run w s).position i=s.position i+d (s.physical.tokens.symm i) := by
  conv_lhs => rw [state_as_port_rename s]
  rw [← rename_run]
  change (run w (atPort s.physical.cursor s.cursor)).position (s.physical.tokens.symm i)+
    (s.position i-(s.physical.tokens.symm i : ℤ))= _
  rw [hport, hend]
  ring

omit [NeZero n] in
theorem displacement_frame (p q : State n) (d : Fin n → ℤ)
    (hd : ∀ i, p i=i → d i=0) (hdis : p.Disjoint q) (i : Fin n) :
    d (q.symm i)=d i := by
  by_cases hi : q.symm i=i
  · rw [hi]
  · have hqi : q i ≠ i := by
      intro h
      apply hi
      apply q.injective
      simpa using h.symm
    have hqj : q (q.symm i) ≠ q.symm i := by simpa using Ne.symm hi
    rw [hd i ((hdis i).resolve_right hqi), hd (q.symm i) ((hdis _).resolve_right hqj)]

theorem disjoint_service_action (w : List Letter) (r : Fin n) (d : Fin n → ℤ)
    (hend : ∀ z i, (run w (atPort r z)).position i=(i : ℤ)+d i)
    (p : State n) (hd : ∀ i, p i=i → d i=0)
    (s : Configuration n) (hport : s.physical.cursor=r)
    (hdis : p.Disjoint s.physical.tokens) (i : Fin n) :
    (run w s).position i=s.position i+d i := by
  rw [service_action w r d hend s hport i, displacement_frame p s.physical.tokens d hd hdis i]

#print axioms service_action
#print axioms disjoint_service_action
end LRX.LiftedModel
