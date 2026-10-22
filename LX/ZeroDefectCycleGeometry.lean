import LX.EvenUnitStructure
import LRX.LinearSortingTrace
import LRX.MinimalEventCycle

namespace LX.EventGeometry
open LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- Two different components of a separated linear event graph cannot
alternate. The component statement itself does not require minimality. -/
theorem components_noncrossing (events : List (Event n))
    (hlinear : ∀ e ∈ events,e.1.val < e.2.val)
    (hsep : events.Pairwise LaterOutside)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : EventReaches events a c) (hbd : EventReaches events b d) :
    EventReaches events a b := by
  classical
  by_contra hnot
  let A := eventComponent events a
  let B := eventComponent events b
  have hA : A.Nonempty := ⟨a,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  have hB : B.Nonempty := ⟨b,(mem_eventComponent _ _ _).mpr Relation.ReflTransGen.refl⟩
  let amin := A.min' hA
  let amax := A.max' hA
  let bmin := B.min' hB
  let bmax := B.max' hB
  have boundA (i : Fin n) (hi : EventReaches events a i) : amin.val ≤ i.val ∧ i.val ≤ amax.val :=
    ⟨Finset.min'_le A i ((mem_eventComponent _ _ _).mpr hi),
     Finset.le_max' A i ((mem_eventComponent _ _ _).mpr hi)⟩
  have boundB (i : Fin n) (hi : EventReaches events b i) : bmin.val ≤ i.val ∧ i.val ≤ bmax.val :=
    ⟨Finset.min'_le B i ((mem_eventComponent _ _ _).mpr hi),
     Finset.le_max' B i ((mem_eventComponent _ _ _).mpr hi)⟩
  have hbmax : EventReaches events b bmax :=
    (mem_eventComponent _ _ _).mp (Finset.max'_mem B hB)
  have hamax : EventReaches events a amax :=
    (mem_eventComponent _ _ _).mp (Finset.max'_mem A hA)
  have hbnd := component_inside_hull events hlinear hsep a b c hab hbc hac hnot
    amin.val amax.val boundA bmax hbmax
  have havoid : ¬EventReaches events b c := by
    intro h
    exact hnot (hac.trans (event_reaches_symm events h))
  have hcmax : EventReaches events c amax := (event_reaches_symm events hac).trans hamax
  have habnd := component_inside_hull events hlinear hsep b c d hbc hcd hbd havoid
    bmin.val bmax.val boundB amax hcmax
  omega

/-- In a factorization of exact reflection rank, graph connectivity is
exactly cycle membership in the actual product. -/
theorem minimal_reaches_iff_same_cycle (events : List (Event n)) (p : LX.State n)
    (hprod : (events.map eventSwap).prod=p)
    (hminimal : events.length+(p⁻¹).cycleFactorsFinset.card=p.support.card)
    (a b : Fin n) : EventReaches events a b ↔ p.SameCycle a b := by
  constructor
  · intro hab
    have hm := minimal_factorization_component_minimal events p hprod hminimal a
    have hsel := minimal_event_same_cycle (componentEvents events a) a
      (by rwa [selected_component_eq]) b (by
        rw [selected_component_eq]
        exact (mem_eventComponent _ _ _).mpr hab)
    have hh := selected_same_cycle events a b hsel
    rwa [hprod] at hh
  · intro hab
    exact cycle_event_reachable events p hprod hab.inv

end LX.EventGeometry

namespace LX.CycleGeometry
open scoped BigOperators
open LRX.ZeroGap LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Zero finite defect forbids alternating vertices from distinct actual
cycles. This follows from the existing sorting event graph. -/
theorem zero_defect_cycles_noncrossing (q : LX.State n) (hq : cycleDefect q=0)
    (a b c d : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) (hcd : c.val < d.val)
    (hac : q.SameCycle a c) (hbd : q.SameCycle b d) : q.SameCycle a b := by
  obtain ⟨events,hprod,hlen,_,hlin,hsep,_⟩ := linear_sorting_events q
  have hcount : (q⁻¹).cycleFactorsFinset.card=q.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv q)
    simpa [Equiv.Perm.cycleType] using hh
  have hminimal : events.length+(q⁻¹).cycleFactorsFinset.card=q.support.card := by
    rw [hcount]
    rw [displacement_mass_inverse] at hlen
    unfold cycleDefect at hq
    omega
  have he := LX.EventGeometry.minimal_reaches_iff_same_cycle events q hprod hminimal
  exact (he a b).mp (LX.EventGeometry.components_noncrossing events hlin hsep a b c d hab hbc hcd
    ((he a c).mpr hac) ((he b d).mpr hbd))

/-- The open interval between neighboring vertices of one cycle is
invariant under the whole permutation, even when other cycles fill it. -/
theorem zero_defect_cycle_gap_forward (q : LX.State n) (hq : cycleDefect q=0)
    (a c : Fin n) (hac : q.SameCycle a c)
    (hgap : ∀ b : Fin n,a.val < b.val → b.val < c.val → ¬q.SameCycle a b)
    (b : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val) :
    a.val < (q b).val ∧ (q b).val < c.val := by
  have hstep : q.SameCycle b (q b) := (Equiv.Perm.SameCycle.refl q b).apply_right
  have hnot := hgap b hab hbc
  have hqa : q b ≠ a := by
    intro he
    exact hnot (he ▸ hstep.symm)
  have hqc : q b ≠ c := by
    intro he
    exact hnot (hac.trans (he ▸ hstep.symm))
  have hqav : (q b).val ≠ a.val := fun h => hqa (Fin.ext h)
  have hqcv : (q b).val ≠ c.val := fun h => hqc (Fin.ext h)
  constructor
  · by_contra hbad
    have h := zero_defect_cycles_noncrossing q hq (q b) a b c (by omega) hab hbc hstep.symm hac
    exact hnot (h.symm.trans hstep.symm)
  · by_contra hbad
    exact hnot (zero_defect_cycles_noncrossing q hq a b c (q b) hab hbc (by omega) hac hstep)

/-- Both directions of gap invariance are proved, so the gap can be used
as an invariant pruning set without a new geometric premise. -/
theorem zero_defect_cycle_gap_invariant (q : LX.State n) (hq : cycleDefect q=0)
    (a c : Fin n) (hac : q.SameCycle a c)
    (hgap : ∀ b : Fin n,a.val < b.val → b.val < c.val → ¬q.SameCycle a b)
    (b : Fin n) :
    (a.val < (q b).val ∧ (q b).val < c.val) ↔ (a.val < b.val ∧ b.val < c.val) := by
  classical
  let S := Finset.univ.filter (fun b : Fin n => a.val < b.val ∧ b.val < c.val)
  have hf : ∀ b ∈ S,q b ∈ S := by
    intro b hb
    have hb' := (Finset.mem_filter.mp hb).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      zero_defect_cycle_gap_forward q hq a c hac hgap b hb'.1 hb'.2⟩
  have he : S.image q=S := by
    apply Finset.eq_of_subset_of_card_le
    · intro i hi
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hi
      exact hf b hb
    · rw [Finset.card_image_of_injective _ q.injective]
  have hi : q b ∈ S ↔ b ∈ S := by
    constructor
    · intro hb
      rw [← he] at hb
      obtain ⟨j,hj,hje⟩ := Finset.mem_image.mp hb
      exact q.injective hje ▸ hj
    · exact hf b
  simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hi

#print axioms zero_defect_cycles_noncrossing
#print axioms zero_defect_cycle_gap_invariant
end LX.CycleGeometry

namespace LX.AnchoredPhases
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- Noncrossing of actual cycles holds in every phase of the remaining
even unit-reserve input, including phases which are not majorized. -/
theorem even_unit_all_anchor_cycles_noncrossing {p : State n} {a : Fin n}
    (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)*(m-1)) (b : Fin n)
    (i j k l : Fin n) (hij : i.val < j.val) (hjk : j.val < k.val) (hkl : k.val < l.val)
    (hik : (permutation p b).SameCycle i k) (hjl : (permutation p b).SameCycle j l) :
    (permutation p b).SameCycle i j :=
  LX.CycleGeometry.zero_defect_cycles_noncrossing (permutation p b)
    (even_unit_all_anchor_zero_defect m hn ha hunit b) i j k l hij hjk hkl hik hjl

#print axioms even_unit_all_anchor_cycles_noncrossing
end LX.AnchoredPhases
