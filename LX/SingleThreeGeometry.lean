import LX.EvenUnitStructure
import LX.FixedPairJoinPrice
import LX.PairFilledCycleGaps
import Mathlib

namespace LX.CycleGeometry
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- One unit of excess over pair cycles identifies one actual 3-cycle. -/
theorem excess_one_single_three (q : State n)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1) :
    ∃ g ∈ q.cycleFactorsFinset,g.support.card=3 ∧
      ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2 := by
  classical
  obtain ⟨hs,hcount⟩ := AnchoredPhases.small_cycle_excess_profile q 1 (by omega) he
  have hc3 : (q.cycleFactorsFinset.filter (fun g => g.support.card=3)).card=1 := by
    change AnchoredPhases.cycleSizeCount q 3=1
    omega
  have hc4 : (q.cycleFactorsFinset.filter (fun g => g.support.card=4)).card=0 := by
    change AnchoredPhases.cycleSizeCount q 4=0
    omega
  obtain ⟨g,hg⟩ := Finset.card_pos.mp (show 0 < (q.cycleFactorsFinset.filter
    (fun g => g.support.card=3)).card by omega)
  refine ⟨g,(Finset.mem_filter.mp hg).1,(Finset.mem_filter.mp hg).2,?_⟩
  intro f hf hne
  rcases hs f hf with h | h | h
  · exact h
  · have heq := Finset.card_le_one.mp hc3.le f (Finset.mem_filter.mpr ⟨hf,h⟩) g hg
    exact False.elim (hne heq)
  · have hm : f ∈ q.cycleFactorsFinset.filter (fun g => g.support.card=4) := Finset.mem_filter.mpr ⟨hf,h⟩
    rw [Finset.card_eq_zero.mp hc4] at hm
    exact False.elim (Finset.notMem_empty _ hm)

theorem shift_support_and_cycle_count (q : State n) (t : ℕ) :
    (shiftConjugate q t).support.card=q.support.card ∧
      (shiftConjugate q t).cycleFactorsFinset.card=q.cycleFactorsFinset.card := by
  constructor
  · simpa only [shiftConjugate,inv_inv] using
      (Equiv.Perm.card_support_conj (σ := (finRotate n^t)⁻¹) (τ := q))
  · have hh := congrArg Multiset.card (Equiv.Perm.cycleType_conj
      (σ := q) (τ := (finRotate n^t)⁻¹))
    simpa only [shiftConjugate,inv_inv,Equiv.Perm.cycleType,Multiset.card_map,Finset.card_def] using hh

theorem shift_cycle_defect (q : State n) (t : ℕ) :
    cycleDefect (shiftConjugate q t)=cycleDefect q := by
  have hh := LX.FiniteJoin.shift_depth_deficit q t
  obtain ⟨hs,hc⟩ := shift_support_and_cycle_count q t
  unfold cycleDefect
  rw [hs,hc]
  change LX.FiniteJoin.depthDeficit (shiftConjugate q t)-_+_=
    LX.FiniteJoin.depthDeficit q-_+_
  rw [hh]

/-- A three-element interval support consists of three consecutive physical
positions. The forbidden backward unit arrow fixes the orientation. -/
theorem single_three_consecutive_at_zero (q : State n) (hq : cycleDefect q=0)
    (he : q.support.card=2*q.cycleFactorsFinset.card+1)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∃ a b c : Fin n,a.val+1=b.val ∧ b.val+1=c.val ∧
      q a=b ∧ q b=c ∧ q c=a ∧
      ∀ i : Fin n,i ≠ a → i ≠ b → i ≠ c → q (q i)=i := by
  classical
  obtain ⟨g,hg,hg3,hother⟩ := excess_one_single_three q he
  have hint := single_cycle_support_interval_at_zero q g hq hg hother hfixed hback
  have hnon : g.support.Nonempty := Finset.card_pos.mp (by omega)
  let a := g.support.min' hnon
  let c := g.support.max' hnon
  have ha : a ∈ g.support := Finset.min'_mem _ _
  have hc : c ∈ g.support := Finset.max'_mem _ _
  have hamin (i : Fin n) (hi : i ∈ g.support) : a.val ≤ i.val := Finset.min'_le _ _ hi
  have hcmax (i : Fin n) (hi : i ∈ g.support) : i.val ≤ c.val := Finset.le_max' _ _ hi
  have heq : g.support=Finset.Icc a c := by
    ext i
    simp only [Finset.mem_Icc,Fin.le_def]
    constructor
    · intro hi
      exact ⟨hamin i hi,hcmax i hi⟩
    · rintro ⟨hai,hic⟩
      by_cases hia : i=a
      · exact hia ▸ ha
      by_cases hic' : i=c
      · exact hic' ▸ hc
      exact hint a ha c hc i (by have : i.val ≠ a.val := fun h => hia (Fin.ext h); omega)
        (by have : i.val ≠ c.val := fun h => hic' (Fin.ext h); omega)
  have hac : a.val+2=c.val := by
    rw [heq,Fin.card_Icc] at hg3
    omega
  let b : Fin n := ⟨a.val+1,by have := c.isLt; omega⟩
  have hab : a.val+1=b.val := rfl
  have hbc : b.val+1=c.val := by dsimp [b]; omega
  have hb : b ∈ g.support := hint a ha c hc b (by omega) (by omega)
  have hmembers (i : Fin n) : i ∈ g.support ↔ i=a ∨ i=b ∨ i=c := by
    rw [heq,Finset.mem_Icc]
    change (a.val ≤ i.val ∧ i.val ≤ c.val) ↔ _
    constructor
    · intro hi
      have hv : i.val=a.val ∨ i.val=b.val ∨ i.val=c.val := by omega
      rcases hv with h | h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Or.inl (Fin.ext h))
      · exact Or.inr (Or.inr (Fin.ext h))
    · rintro (rfl | rfl | rfl) <;> omega
  have hagree (i : Fin n) (hi : i ∈ g.support) : g i=q i := by
    rw [Equiv.Perm.cycle_is_cycleOf hi hg,Equiv.Perm.cycleOf_apply_self]
  have hmove (i : Fin n) (hi : i ∈ g.support) : q i ≠ i := by
    rw [← hagree i hi]
    exact Equiv.Perm.mem_support.mp hi
  have himage (i : Fin n) (hi : i ∈ g.support) : q i=a ∨ q i=b ∨ q i=c := by
    apply (hmembers _).mp
    rw [← hagree i hi]
    exact Equiv.Perm.apply_mem_support.mpr hi
  have hqb : q b=c := by
    rcases himage b hb with h | h | h
    · exact False.elim (hback a b hab h)
    · exact False.elim (hmove b hb h)
    · exact h
  have hqa : q a=b := by
    rcases himage a ha with h | h | h
    · exact False.elim (hmove a ha h)
    · exact h
    · have hab' := q.injective (h.trans hqb.symm)
      have hv := congrArg Fin.val hab'
      omega
  have hqc : q c=a := by
    rcases himage c hc with h | h | h
    · exact h
    · have hca := q.injective (h.trans hqa.symm)
      have hv := congrArg Fin.val hca
      omega
    · exact False.elim (hmove c hc h)
  refine ⟨a,b,c,hab,hbc,hqa,hqb,hqc,?_⟩
  intro i hia hib hic
  exact outside_single_cycle_involutive q g hg hother i (by
    rw [hmembers]
    tauto)

#print axioms single_three_consecutive_at_zero
end LX.CycleGeometry
