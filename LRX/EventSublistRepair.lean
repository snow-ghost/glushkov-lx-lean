import LRX.ExactCycleEventFactorization

namespace LRX.ZeroGap
variable {n : ℕ}

def transportEvent (p : State n) (e : Event n) : Event n := (p e.1,p e.2)

theorem transport_event_swap (p : State n) (e : Event n) :
    eventSwap (transportEvent p e) = MulAut.conj p (eventSwap e) := by
  simpa only [transportEvent,eventSwap,MulAut.conj_apply] using Equiv.swap_apply_apply p e.1 e.2

theorem transport_event_product (p : State n) (events : List (Event n)) :
    ((events.map (transportEvent p)).map eventSwap).prod =
      MulAut.conj p ((events.map eventSwap).prod) := by
  rw [List.map_map]
  change (events.map (fun e => eventSwap (transportEvent p e))).prod = _
  simp_rw [transport_event_swap]
  simpa only [List.map_map,Function.comp_def] using
    (map_list_prod (MulAut.conj p) (events.map eventSwap)).symm

/-- Deleting events requires exactly one correcting transposition per deletion.
Kept events conjugate the correction; no commutation assumption is used. -/
theorem event_sublist_repair {part events : List (Event n)} (hsub : part.Sublist events) :
    ∃ repair : List (Event n), repair.length+part.length=events.length ∧
      (repair.map eventSwap).prod*(events.map eventSwap).prod=(part.map eventSwap).prod := by
  induction hsub with
  | slnil => exact ⟨[],by simp,by simp⟩
  | @cons part events e hsub ih =>
    obtain ⟨repair,hlen,hprod⟩ := ih
    refine ⟨repair++[e],by simp only [List.length_append,List.length_cons,List.length_nil]; omega,?_⟩
    simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons,List.map_nil,List.prod_nil,mul_one]
    calc
      _ = (repair.map eventSwap).prod * ((eventSwap e * eventSwap e) * (events.map eventSwap).prod) := by group
      _ = _ := by simpa only [eventSwap,Equiv.swap_mul_self,one_mul] using hprod
  | @cons_cons part events e hsub ih =>
    obtain ⟨repair,hlen,hprod⟩ := ih
    refine ⟨repair.map (transportEvent (eventSwap e)),by simp only [List.length_map,List.length_cons]; omega,?_⟩
    rw [transport_event_product]
    simp only [List.map_cons,List.prod_cons,MulAut.conj_apply]
    calc
      _ = eventSwap e * ((repair.map eventSwap).prod * (events.map eventSwap).prod) := by group
      _ = _ := by rw [hprod]

#print axioms event_sublist_repair
end LRX.ZeroGap
