import LRX.ZeroGapEventGeometry
import Mathlib

/-! Connected components of the event graph contain the cycles of the
original permutation and are invariant under it. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def EventEdge (events : List (Event n)) (i j : Fin n) : Prop :=
  ∃ e ∈ events, (i=e.1 ∧ j=e.2) ∨ (i=e.2 ∧ j=e.1)

abbrev EventReaches (events : List (Event n)) := Relation.ReflTransGen (EventEdge events)

theorem event_edge_symm (events : List (Event n)) {i j : Fin n} (h : EventEdge events i j) :
    EventEdge events j i := by
  obtain ⟨e,he,h⟩ := h
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
  · exact ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

theorem event_reaches_symm (events : List (Event n)) {i j : Fin n} (h : EventReaches events i j) :
    EventReaches events j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hp he ih => exact (Relation.ReflTransGen.single (event_edge_symm events he)).trans ih

theorem event_swap_reaches (events : List (Event n)) (e : Event n) (he : e ∈ events) (i : Fin n) :
    EventReaches events i (eventSwap e i) := by
  by_cases hi : i=e.1
  · subst i
    simp only [eventSwap,Equiv.swap_apply_left]
    exact Relation.ReflTransGen.single ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩
  · by_cases hi' : i=e.2
    · subst i
      simp only [eventSwap,Equiv.swap_apply_right]
      exact Relation.ReflTransGen.single ⟨e,he,Or.inr ⟨rfl,rfl⟩⟩
    · simp only [eventSwap,Equiv.swap_apply_of_ne_of_ne hi hi']
      exact Relation.ReflTransGen.refl

theorem event_product_reaches (events part : List (Event n)) (hsub : ∀ e ∈ part, e ∈ events) (i : Fin n) :
    EventReaches events i ((part.map eventSwap).prod i) := by
  induction part with
  | nil => exact Relation.ReflTransGen.refl
  | cons e rest ih =>
    have hp := ih (fun f hf => hsub f (List.mem_cons_of_mem _ hf))
    have he := event_swap_reaches events e (hsub e (by simp)) ((rest.map eventSwap).prod i)
    exact hp.trans he

theorem target_event_reachable (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) (i : Fin n) : EventReaches events i (p.symm i) := by
  have h := event_product_reaches events events (fun _ h => h) (p.symm i)
  rw [hprod,p.apply_symm_apply] at h
  exact event_reaches_symm events h

theorem cycle_event_reachable (events : List (Event n)) (p : State n)
    (hprod : (events.map eventSwap).prod=p) {i j : Fin n} (hc : (p⁻¹).SameCycle i j) :
    EventReaches events i j := by
  obtain ⟨k,rfl⟩ := hc.exists_nat_pow_eq
  clear hc
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih =>
    have he := target_event_reachable events p hprod (((p⁻¹)^k) i)
    simpa only [pow_succ',Equiv.Perm.mul_apply,Equiv.Perm.inv_def] using ih.trans he

noncomputable def eventComponent (events : List (Event n)) (root : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (EventReaches events root)

@[simp] theorem mem_eventComponent (events : List (Event n)) (root i : Fin n) :
    i ∈ eventComponent events root ↔ EventReaches events root i := by
  classical
  simp [eventComponent]


#print axioms cycle_event_reachable
end LRX.ZeroGap
