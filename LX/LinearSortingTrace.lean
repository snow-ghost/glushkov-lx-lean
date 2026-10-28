import LX.LinearEventComponents
import LX.PaddedSortingEvents
import Mathlib

/-! Project the padded sorting trace back to its original finite interval.
On a linear event graph, graph reachability already determines integer travel. -/
namespace LX.Core.ZeroGap
variable {n : ℕ} [NeZero n]

theorem linear_reaches_travel (events : List (Event n))
    (hlinear : ∀ e ∈ events, e.1.val < e.2.val) {i j : Fin n}
    (h : EventReaches events i j) : Travel events i j ((j : ℤ)-(i : ℤ)) := by
  induction h with
  | refl => simpa using Travel.refl (events := events) i
  | @tail a b hp he ih =>
    obtain ⟨e,he,hor⟩ := he
    have hdist : (distance e.1 e.2 : ℤ)=(e.2 : ℤ)-(e.1 : ℤ) := by
      unfold distance
      rw [Fin.sub_val_of_le (show e.1 ≤ e.2 from le_of_lt (hlinear e he))]
      have hh := hlinear e he
      omega
    have hstep : Travel events a b ((b : ℤ)-(a : ℤ)) := by
      rcases hor with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · have hm : EventMove events e.1 e.2 ((e.2 : ℤ)-(e.1 : ℤ)) :=
          ⟨e,he,Or.inl ⟨rfl,rfl,hdist.symm⟩⟩
        simpa using Travel.head hm (Travel.refl e.2)
      · have hm : EventMove events e.2 e.1 ((e.1 : ℤ)-(e.2 : ℤ)) :=
          ⟨e,he,Or.inr ⟨rfl,rfl,by omega⟩⟩
        simpa using Travel.head hm (Travel.refl e.1)
    convert ih.trans hstep using 1; ring

end LX.Core.ZeroGap

namespace LX.Core.FiniteCuts
open ZeroGap FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem linear_sorting_events (p : State n) :
    ∃ events : List (Event n), (events.map eventSwap).prod=p ∧
      (events.length : ℤ)=(∑ i, |displacement p.symm i|)-(inversionNumber p : ℤ) ∧
      (∀ e ∈ events, e.1 ∈ p.support ∧ e.2 ∈ p.support) ∧
      (∀ e ∈ events, e.1.val < e.2.val) ∧ events.Pairwise LaterOutside ∧
      (∀ i, Travel events i (p.symm i) (displacement p.symm i)) := by
  classical
  let : NeZero (2*n+1) := ⟨by omega⟩
  let W : Window (2*n+1) n := ⟨0,by omega⟩
  let q := permutation W p
  obtain ⟨events,hprod,hlen,_,ha,hl,hs⟩ := padded_sorting_events p
  let project (i : Fin (2*n+1)) : Fin n := if h : i.val < n then ⟨i.val,h⟩ else 0
  let projectEvent (e : Event (2*n+1)) : Event n := (project e.1,project e.2)
  have hins (i : Fin (2*n+1)) (hi : i ∈ q.support) : i.val < n := by
    have hc : Contains W i := by
      by_contra hh
      exact (Equiv.Perm.mem_support.mp hi) (permutation_outside W p i hh)
    simpa only [Contains,W,zero_add] using hc.2
  have hval (i : Fin (2*n+1)) (hi : i.val < n) : (project i).val=i.val := by
    simp only [project,dite_eq_left hi]
  have hemb (i : Fin (2*n+1)) (hi : i.val < n) : embed W (project i)=i := by
    apply Fin.ext
    simp only [embed,W,zero_add,hval i hi]
  have hswap (e : Event (2*n+1)) (he : e ∈ events) (i : Fin n) :
      eventSwap e (embed W i)=embed W (eventSwap (projectEvent e) i) := by
    have hh := (embed_injective W).swap_apply (project e.1) (project e.2) i
    rw [hemb _ (hins _ (ha e he).1),hemb _ (hins _ (ha e he).2)] at hh
    exact hh
  have hprod' (es : List (Event (2*n+1))) (hsub : ∀ e ∈ es, e ∈ events) (i : Fin n) :
      (es.map eventSwap).prod (embed W i)=embed W ((es.map projectEvent |>.map eventSwap).prod i) := by
    induction es with
    | nil => rfl
    | cons e es ih =>
      simp only [List.map_cons,List.prod_cons,Equiv.Perm.mul_apply]
      rw [ih (fun f hf => hsub f (List.mem_cons_of_mem _ hf)),hswap e (hsub e (by simp))]
  have htarget : ((events.map projectEvent).map eventSwap).prod=p := by
    apply Equiv.ext
    intro i
    apply embed_injective W
    have hh := hprod' events (fun _ h => h) i
    rw [hprod,permutation_embed] at hh
    exact hh.symm
  have hlin : ∀ e ∈ events.map projectEvent, e.1.val < e.2.val := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    simpa only [projectEvent,hval _ (hins _ (ha f hf).1),hval _ (hins _ (ha f hf).2)] using hl f hf
  have hactive : ∀ e ∈ events.map projectEvent, e.1 ∈ p.support ∧ e.2 ∈ p.support := by
    have moved (i : Fin (2*n+1)) (hi : i ∈ q.support) : project i ∈ p.support := by
      apply Equiv.Perm.mem_support.mpr
      intro hh
      apply Equiv.Perm.mem_support.mp hi
      rw [← hemb i (hins i hi)]
      change permutation W p (embed W (project i))=embed W (project i)
      rw [permutation_embed,hh]
    intro e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact ⟨moved _ (ha f hf).1,moved _ (ha f hf).2⟩
  have hsep : (events.map projectEvent).Pairwise LaterOutside := by
    apply List.pairwise_map.mpr
    apply hs.imp_of_mem
    intro e f he hf hef
    have he' := hlin (projectEvent e) (List.mem_map.mpr ⟨e,he,rfl⟩)
    have same (i : Fin (2*n+1)) (hi : i.val < n) :
        Inside (projectEvent e) (project i) ↔ Inside e i := by
      rw [inside_linear_iff _ he',inside_linear_iff _ (hl e he)]
      simp only [projectEvent,hval _ (hins _ (ha e he).1),hval _ (hins _ (ha e he).2),hval i hi]
    exact ⟨fun hh => hef.1 ((same f.1 (hins _ (ha f hf).1)).mp hh),
      fun hh => hef.2 ((same f.2 (hins _ (ha f hf).2)).mp hh)⟩
  refine ⟨events.map projectEvent,htarget,?_,hactive,hlin,hsep,?_⟩
  · simpa only [List.length_map,displacement_mass_inverse] using hlen
  · intro i
    exact linear_reaches_travel _ hlin (target_event_reachable _ p htarget i)

#print axioms ZeroGap.linear_reaches_travel
#print axioms linear_sorting_events
end LX.Core.FiniteCuts
