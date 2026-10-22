import LX.EvenUnitPhaseParity

namespace LX.CycleGeometry
open scoped BigOperators
open LRX.FiniteCuts LRX.ZeroGap
variable {n : ℕ} [NeZero n]

/-- An invariant interval with no fixed point would have a unit arrow in
its minimal sorting-event forest. Thus forbidding unit arrows forces a
fixed point in every nonempty invariant interval. -/
theorem zero_defect_invariant_gap_fixed (q : State n) (hq : cycleDefect q=0)
    (hunit : ∀ i : Fin n,|displacement q i| ≠ 1)
    (a c b : Fin n) (hab : a.val < b.val) (hbc : b.val < c.val)
    (hinv : ∀ i : Fin n,(a.val < (q i).val ∧ (q i).val < c.val) ↔
      (a.val < i.val ∧ i.val < c.val)) :
    ∃ i : Fin n,a.val < i.val ∧ i.val < c.val ∧ q i=i := by
  classical
  by_contra hnone
  let S := Finset.univ.filter (fun i : Fin n => a.val < i.val ∧ i.val < c.val)
  have hS (i : Fin n) : q i ∈ S ↔ i ∈ S := by
    simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hinv i
  let g := LRX.PrunedLift.permutation q S hS
  have hgzero : cycleDefect g=0 := zero_defect_pruned_factor q S hS hq
  have hgSupport : g.support=S := by
    ext i
    simp only [Equiv.Perm.mem_support]
    by_cases hi : i ∈ S
    · have hb' := (Finset.mem_filter.mp hi).2
      have hmove : q i ≠ i := fun he => hnone ⟨i,hb'.1,hb'.2,he⟩
      simp [g,hi,hmove]
    · simp [g,hi]
  obtain ⟨events,hprod,hlen,hactive,hlin,hsep,_⟩ := linear_sorting_events g
  have hcount : (g⁻¹).cycleFactorsFinset.card=g.cycleFactorsFinset.card := by
    have hh := congrArg Multiset.card (Equiv.Perm.cycleType_inv g)
    simpa [Equiv.Perm.cycleType] using hh
  have hminimal : events.length+(g⁻¹).cycleFactorsFinset.card=g.support.card := by
    rw [hcount]
    rw [displacement_mass_inverse] at hlen
    unfold cycleDefect at hgzero
    omega
  have hnon : g.support.Nonempty := by
    rw [hgSupport]
    exact ⟨b,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hab,hbc⟩⟩
  have hinter : CarrierInterval g.support Finset.univ := by
    rw [hgSupport]
    refine ⟨Finset.subset_univ _,?_⟩
    intro x hx y hy z _ hxz hzy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega,by omega⟩
  obtain ⟨i,hi⟩ := minimal_interval_event_unit_arrow events g hprod hactive hlin hsep hnon hinter hminimal
  have his : i ∈ S := by
    by_contra hiS
    have hgi : g i=i := by simp [g,hiS]
    simp only [displacement,hgi,sub_self,abs_zero] at hi
    omega
  have hgi : g i=q i := by simp [g,his]
  apply hunit i
  simpa only [displacement,hgi] using hi

/-- The gap between consecutive support vertices of one actual cycle is
an invariant interval. With no unit arrow it contains a fixed point. -/
theorem cycle_factor_gap_fixed (q g : State n) (hq : cycleDefect q=0)
    (hunit : ∀ i : Fin n,|displacement q i| ≠ 1)
    (hg : g ∈ q.cycleFactorsFinset) (a c : Fin n)
    (ha : a ∈ g.support) (hc : c ∈ g.support) (hwidth : a.val+1 < c.val)
    (hgap : ∀ i : Fin n,a.val < i.val → i.val < c.val → i ∉ g.support) :
    ∃ i : Fin n,a.val < i.val ∧ i.val < c.val ∧ q i=i := by
  have hac : q.SameCycle a c :=
    (cycle_root_same_cycle hg ha).symm.trans (cycle_root_same_cycle hg hc)
  have hno (i : Fin n) (hai : a.val < i.val) (hic : i.val < c.val) : ¬q.SameCycle a i := by
    intro hs
    have he := Equiv.Perm.cycle_is_cycleOf ha hg
    have hmove := Equiv.Perm.mem_support.mp ha
    rw [he,Equiv.Perm.cycleOf_apply_self] at hmove
    have hm : i ∈ (q.cycleOf a).support :=
      Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨hs,Equiv.Perm.mem_support.mpr hmove⟩
    rw [← he] at hm
    exact hgap i hai hic hm
  let b : Fin n := ⟨a.val+1,by have := c.isLt; omega⟩
  exact zero_defect_invariant_gap_fixed q hq hunit a c b (by dsimp [b]; omega)
    (by dsimp [b]; omega) (zero_defect_cycle_gap_invariant q hq a c hac hno)

/-- With the cut at a fixed point, two fixed positions cannot fill two
nonempty internal gaps of a longer cycle. Consequently every cycle is a
pair whenever neighboring physical positions lie in different cycles. -/
theorem two_fixed_no_neighbor_cycles_are_pairs (q : State n) (hq : cycleDefect q=0)
    (hzero : q 0=0) (hfixed : (fixedPositions q).card ≤ 2)
    (hsep : ∀ i j : Fin n,i.val+1=j.val → ¬q.SameCycle i j) :
    ∀ g ∈ q.cycleFactorsFinset,g.support.card=2 := by
  classical
  have hunit (i : Fin n) : |displacement q i| ≠ 1 := by
    intro hh
    have hs : q.SameCycle i (q i) := (Equiv.Perm.SameCycle.refl q i).apply_right
    unfold displacement at hh
    rw [abs_eq_max_neg] at hh
    have hc : i.val+1=(q i).val ∨ (q i).val+1=i.val := by omega
    rcases hc with hc | hc
    · exact hsep i (q i) hc hs
    · exact hsep (q i) i hc hs.symm
  intro g hg
  have hsize := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1.two_le_card_support
  by_contra hnot
  have hthree : 3 ≤ g.support.card := by omega
  let S := g.support
  have hS : S.Nonempty := Finset.card_pos.mp (by dsimp [S]; omega)
  let a := S.min' hS
  have ha : a ∈ S := Finset.min'_mem S hS
  have hS1 : (S.erase a).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem ha]
    dsimp [S]
    omega)
  let b := (S.erase a).min' hS1
  have hb1 : b ∈ S.erase a := Finset.min'_mem _ _
  have hb : b ∈ S := (Finset.mem_erase.mp hb1).2
  have hba : b ≠ a := (Finset.mem_erase.mp hb1).1
  have hS2 : ((S.erase a).erase b).Nonempty := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hb1,Finset.card_erase_of_mem ha]
    dsimp [S]
    omega)
  let c := ((S.erase a).erase b).min' hS2
  have hc2 : c ∈ (S.erase a).erase b := Finset.min'_mem _ _
  have hc1 : c ∈ S.erase a := (Finset.mem_erase.mp hc2).2
  have hc : c ∈ S := (Finset.mem_erase.mp hc1).2
  have hcb : c ≠ b := (Finset.mem_erase.mp hc2).1
  have hab : a.val < b.val := by
    have hlo : a.val ≤ b.val := Finset.min'_le S b hb
    have hne : b.val ≠ a.val := fun h => hba (Fin.ext h)
    omega
  have hbc : b.val < c.val := by
    have hlo : b.val ≤ c.val := Finset.min'_le (S.erase a) c hc1
    have hne : c.val ≠ b.val := fun h => hcb (Fin.ext h)
    omega
  have hgapAB (i : Fin n) (hai : a.val < i.val) (hib : i.val < b.val) : i ∉ g.support := by
    intro hi
    have hia : i ≠ a := by intro h; have := congrArg Fin.val h; omega
    have hm : i ∈ S.erase a := Finset.mem_erase.mpr ⟨hia,hi⟩
    have hh : b.val ≤ i.val := Finset.min'_le (S.erase a) i hm
    omega
  have hgapBC (i : Fin n) (hbi : b.val < i.val) (hic : i.val < c.val) : i ∉ g.support := by
    intro hi
    have hia : i ≠ a := by intro h; have := congrArg Fin.val h; omega
    have hib : i ≠ b := by intro h; have := congrArg Fin.val h; omega
    have hm : i ∈ (S.erase a).erase b := Finset.mem_erase.mpr ⟨hib,Finset.mem_erase.mpr ⟨hia,hi⟩⟩
    have hh : c.val ≤ i.val := Finset.min'_le ((S.erase a).erase b) i hm
    omega
  have habCycle : q.SameCycle a b := (cycle_root_same_cycle hg ha).symm.trans (cycle_root_same_cycle hg hb)
  have hbcCycle : q.SameCycle b c := (cycle_root_same_cycle hg hb).symm.trans (cycle_root_same_cycle hg hc)
  have hab2 : a.val+1 < b.val := by
    have hne : a.val+1 ≠ b.val := fun he => hsep a b he habCycle
    omega
  have hbc2 : b.val+1 < c.val := by
    have hne : b.val+1 ≠ c.val := fun he => hsep b c he hbcCycle
    omega
  obtain ⟨u,hau,hub,hu⟩ := cycle_factor_gap_fixed q g hq hunit hg a b ha hb hab2 hgapAB
  obtain ⟨v,hbv,hvc,hv⟩ := cycle_factor_gap_fixed q g hq hunit hg b c hb hc hbc2 hgapBC
  have hz : (0 : Fin n) ∈ fixedPositions q := (mem_fixedPositions _ _).mpr hzero
  have hcard : ((fixedPositions q).erase 0).card ≤ 1 := by
    rw [Finset.card_erase_of_mem hz]
    omega
  have hum : u ∈ (fixedPositions q).erase 0 := Finset.mem_erase.mpr ⟨by
    intro h; rw [h,Fin.val_zero] at hau; omega,(mem_fixedPositions _ _).mpr hu⟩
  have hvm : v ∈ (fixedPositions q).erase 0 := Finset.mem_erase.mpr ⟨by
    intro h; rw [h,Fin.val_zero] at hbv; omega,(mem_fixedPositions _ _).mpr hv⟩
  have he := Finset.card_le_one.mp hcard u hum v hvm
  have hh := congrArg Fin.val he
  omega

#print axioms zero_defect_invariant_gap_fixed
#print axioms two_fixed_no_neighbor_cycles_are_pairs
end LX.CycleGeometry
