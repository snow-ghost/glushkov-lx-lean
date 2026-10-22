import LX.ZeroDefectCycleGeometry

namespace LX.CycleGeometry
open LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- An invariant nonempty interval filled only by transpositions must
contain a fixed position or an adjacent pair. The latter is forbidden in
the majorized even source. -/
theorem pair_filled_gap_empty (q : State n) (hq : cycleDefect q=0)
    (a c : Fin n)
    (hinv : ∀ b : Fin n,a.val < b.val → b.val < c.val →
      a.val < (q b).val ∧ (q b).val < c.val)
    (hpairs : ∀ b : Fin n,a.val < b.val → b.val < c.val → q (q b)=b)
    (hfixed : ∀ b : Fin n,a.val < b.val → b.val < c.val → q b ≠ b)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) : c.val ≤ a.val+1 := by
  by_contra hnot
  let b : Fin n := ⟨a.val+1,by have := c.isLt; omega⟩
  have hab : a.val < b.val := by dsimp [b]; omega
  have hbc : b.val < c.val := by dsimp [b]; omega
  have hqb := hinv b hab hbc
  have hneq := hfixed b hab hbc
  have hpair := hpairs b hab hbc
  let e := LX.PairCore.permutation q
  have he (i : Fin n) (hai : a.val < i.val) (hic : i.val < c.val) : e i=q i := by
    simp only [e,LX.PairCore.permutation_apply,ite_eq_left (hpairs i hai hic)]
  have hlt : b.val < (q b).val := by
    have hnv : (q b).val ≠ b.val := fun h => hneq (Fin.ext h)
    dsimp [b] at *
    omega
  obtain ⟨x,hx,hbx,hxq⟩ := LX.PairCore.pair_hits_ports e
    (LX.PairCore.permutation_involutive q) (LX.PairCore.permutation_noncrossing q hq)
    b (q b) hlt (he b hab hbc)
  have hax : a.val < x.val := by omega
  have hxc : x.val < c.val := by omega
  rcases Finset.mem_union.mp hx with hfix | hadj
  · have hx' := (mem_fixedPositions e x).mp hfix
    rw [he x hax hxc] at hx'
    exact hfixed x hax hxc hx'
  · have hx' := (Finset.mem_filter.mp hadj).2
    rw [he x hax hxc] at hx'
    exact hback x (q x) hx' (hpairs x hax hxc)

/-- Positions outside a singled-out non-pair cycle are fixed or belong
to genuine transposition cycles of the original permutation. -/
theorem outside_single_cycle_involutive (q g : State n)
    (hg : g ∈ q.cycleFactorsFinset)
    (hother : ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2)
    (i : Fin n) (hi : i ∉ g.support) : q (q i)=i := by
  classical
  by_cases hfix : q i=i
  · rw [hfix,hfix]
  · have hc : q.cycleOf i ∈ q.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr (Equiv.Perm.mem_support.mpr hfix)
    have hne : q.cycleOf i ≠ g := by
      intro he
      exact hi ((Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff q g hg i).mp he.symm)
    obtain ⟨u,v,_,he⟩ := Equiv.Perm.card_support_eq_two.mp (hother _ hc hne)
    have hh : (q.cycleOf i) ((q.cycleOf i) i)=i := by rw [he]; simp
    rwa [Equiv.Perm.cycleOf_apply_self,Equiv.Perm.cycleOf_apply_apply_self] at hh

/-- A gap between consecutive vertices of the sole non-pair cycle is
empty if the only fixed position lies outside that gap. -/
theorem single_cycle_gap_empty (q g : State n) (hq : cycleDefect q=0)
    (hg : g ∈ q.cycleFactorsFinset)
    (hother : ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i)
    (a c : Fin n) (ha : a ∈ g.support) (hc : c ∈ g.support)
    (hgap : ∀ i : Fin n,a.val < i.val → i.val < c.val → i ∉ g.support)
    (hfixed : ∀ i : Fin n,a.val < i.val → i.val < c.val → q i ≠ i) :
    c.val ≤ a.val+1 := by
  have hac : q.SameCycle a c :=
    (LRX.ZeroGap.cycle_root_same_cycle hg ha).symm.trans (LRX.ZeroGap.cycle_root_same_cycle hg hc)
  have hno (i : Fin n) (hai : a.val < i.val) (hic : i.val < c.val) : ¬q.SameCycle a i := by
    intro hs
    have he := Equiv.Perm.cycle_is_cycleOf ha hg
    have hm : i ∈ (q.cycleOf a).support :=
      Equiv.Perm.mem_support_cycleOf_iff.mpr ⟨hs,by
        have hne := Equiv.Perm.mem_support.mp ha
        rw [he,Equiv.Perm.cycleOf_apply_self] at hne
        exact Equiv.Perm.mem_support.mpr hne⟩
    rw [← he] at hm
    exact hgap i hai hic hm
  exact pair_filled_gap_empty q hq a c
    (fun i hai hic => zero_defect_cycle_gap_forward q hq a c hac hno i hai hic)
    (fun i hai hic => outside_single_cycle_involutive q g hg hother i (hgap i hai hic))
    hfixed hback

/-- After cutting at the unique fixed position, the sole non-pair cycle
has no gaps in its physical support. This controls positions, not just ranks. -/
theorem single_cycle_support_interval_at_zero (q g : State n) (hq : cycleDefect q=0)
    (hg : g ∈ q.cycleFactorsFinset)
    (hother : ∀ f ∈ q.cycleFactorsFinset,f ≠ g → f.support.card=2)
    (hfixed : ∀ i : Fin n,q i=i → i=0)
    (hback : ∀ i j : Fin n,i.val+1=j.val → q j ≠ i) :
    ∀ a ∈ g.support,∀ c ∈ g.support,∀ i : Fin n,
      a.val < i.val → i.val < c.val → i ∈ g.support := by
  classical
  intro a ha c hc i hai hic
  by_contra hnot
  let A := g.support.filter (fun x : Fin n => x.val < i.val)
  let C := g.support.filter (fun x : Fin n => i.val < x.val)
  have hA : A.Nonempty := ⟨a,Finset.mem_filter.mpr ⟨ha,hai⟩⟩
  have hC : C.Nonempty := ⟨c,Finset.mem_filter.mpr ⟨hc,hic⟩⟩
  let l := A.max' hA
  let r := C.min' hC
  have hl := Finset.mem_filter.mp (Finset.max'_mem A hA)
  have hr := Finset.mem_filter.mp (Finset.min'_mem C hC)
  have hgap (j : Fin n) (hlj : l.val < j.val) (hjr : j.val < r.val) : j ∉ g.support := by
    intro hj
    by_cases hji : j.val < i.val
    · have hm : j ∈ A := Finset.mem_filter.mpr ⟨hj,hji⟩
      have hb := Finset.le_max' A j hm
      change j.val ≤ l.val at hb
      omega
    · by_cases hij : i.val < j.val
      · have hm : j ∈ C := Finset.mem_filter.mpr ⟨hj,hij⟩
        have hb := Finset.min'_le C j hm
        change r.val ≤ j.val at hb
        omega
      · have he : j=i := Fin.ext (by omega)
        exact hnot (he ▸ hj)
  have hempty := single_cycle_gap_empty q g hq hg hother hback l r hl.1 hr.1 hgap (by
    intro j hlj _ hj
    have he := hfixed j hj
    rw [he,Fin.val_zero] at hlj
    omega)
  omega

#print axioms pair_filled_gap_empty
#print axioms single_cycle_support_interval_at_zero
end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- Majorization excludes every backward unit arrow in the even maximal
height source, not merely the arrows belonging to pairs. -/
theorem even_source_no_backward_unit (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (hn : n=2*height p a+2) (i : Fin n) :
    permutation p a (i+1) ≠ i := by
  intro hi
  have he : cyclicOffset p a (i+1)= -(1 : Fin n) := by
    rw [cyclic_offset_normalized,hi]
    abel
  have hn1 : 1 < n := by omega
  have hne : (1 : Fin n) ≠ 0 := by
    intro hh
    have hv := congrArg Fin.val hh
    norm_num [Nat.mod_eq_of_lt hn1] at hv
  have hv : (-(1 : Fin n)).val=n-1 := by simp [Fin.val_neg,hne,Nat.mod_eq_of_lt hn1]
  have hu := (short_coordinates (is_lift p a).1 hm (i+1)).1
  rw [displacement_offset,he] at hu
  change 2*((((-(1 : Fin n)).val : ℕ) : ℤ)-(height p a : ℤ)) ≤ (n : ℤ)-1 at hu
  rw [hv] at hu
  omega

#print axioms even_source_no_backward_unit
end LX.AnchoredPhases
