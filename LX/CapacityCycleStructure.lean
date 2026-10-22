import LX.ZeroDefectCycleGeometry

namespace LX.CycleGeometry
open scoped BigOperators
open LRX.FiniteCuts
variable {n : ℕ}

/-- Equality of total descending count and reflection rank makes the
descending-count bound tight in each actual disjoint cycle. -/
theorem rank_descending_equality_cycles (q : State n)
    (he : (descendingPositions q).card+q.cycleFactorsFinset.card=q.support.card) :
    ∀ g ∈ q.cycleFactorsFinset,(descendingPositions g).card+1=g.support.card := by
  classical
  have hlo (g : State n) (hg : g ∈ q.cycleFactorsFinset) :
      (descendingPositions g).card+1 ≤ g.support.card :=
    cycle_descending_count_lt_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1
  have hs : (∑ g ∈ q.cycleFactorsFinset,((descendingPositions g).card+1))=
      ∑ g ∈ q.cycleFactorsFinset,g.support.card := by
    rw [Finset.sum_add_distrib,← descending_count_cycle_sum,cycle_support_card_sum]
    simpa using he
  exact (Finset.sum_eq_sum_iff_of_le hlo).mp hs

/-- A cycle with maximal descending count has one increasing arrow, from
its minimum support position to its maximum. Every other support vertex
moves strictly left. No shallow-cycle classification is assumed. -/
theorem cycle_max_descending_single_ascent (g : State n) (hg : g.IsCycle)
    (he : (descendingPositions g).card+1=g.support.card) :
    ∃ a b : Fin n,a ∈ g.support ∧ b ∈ g.support ∧ g a=b ∧ a.val < b.val ∧
      (∀ i ∈ g.support,a.val ≤ i.val ∧ i.val ≤ b.val) ∧
      (∀ i ∈ g.support,i ≠ a → (g i).val < i.val) := by
  classical
  have hS := hg.nonempty_support
  let a := g.support.min' hS
  let b := g.support.max' hS
  have ha : a ∈ g.support := Finset.min'_mem _ _
  have hb : b ∈ g.support := Finset.max'_mem _ _
  have hmin (i : Fin n) (hi : i ∈ g.support) : a.val ≤ i.val := Finset.min'_le _ _ hi
  have hmax (i : Fin n) (hi : i ∈ g.support) : i.val ≤ b.val := Finset.le_max' _ _ hi
  have hna : a ∉ descendingPositions g := by
    intro had
    have hh := (mem_descendingPositions g a).mp had
    have hge := hmin (g a) (Equiv.Perm.apply_mem_support.mpr ha)
    omega
  have hsub : descendingPositions g ⊆ g.support.erase a := by
    intro i hi
    exact Finset.mem_erase.mpr ⟨fun he => hna (he ▸ hi),descending_positions_subset_support g hi⟩
  have hset : descendingPositions g=g.support.erase a := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_erase_of_mem ha]
    omega
  have hdesc (i : Fin n) (hi : i ∈ g.support) (hia : i ≠ a) : (g i).val < i.val := by
    apply (mem_descendingPositions g i).mp
    rw [hset]
    exact Finset.mem_erase.mpr ⟨hia,hi⟩
  have hpre : g.symm b ∈ g.support := by
    apply Equiv.Perm.apply_mem_support.mp
    simpa using hb
  have hprea : g.symm b=a := by
    by_contra hnot
    have hd := hdesc (g.symm b) hpre hnot
    rw [g.apply_symm_apply] at hd
    have hm := hmax (g.symm b) hpre
    omega
  have hab : g a=b := by rw [← hprea,g.apply_symm_apply]
  have hlt : a.val < b.val := by
    have hle := hmin b hb
    have hne : a ≠ b := fun hh => (Equiv.Perm.mem_support.mp ha) (hab.trans hh.symm)
    have hnev : a.val ≠ b.val := fun hh => hne (Fin.ext hh)
    omega
  exact ⟨a,b,ha,hb,hab,hlt,fun i hi => ⟨hmin i hi,hmax i hi⟩,hdesc⟩

end LX.CycleGeometry

namespace LX.AnchoredPhases
open scoped BigOperators
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Full strip capacity already forces zero event defect and exact rank,
even when the source phase is not majorized or globally minimal. -/
theorem zero_strip_capacity_structure (p : State n) (a : Fin n)
    (hz : anchorReserve p a=0) :
    cycleDefect (permutation p a)=0 ∧
      height p a+(permutation p a).cycleFactorsFinset.card=(permutation p a).support.card ∧
      (∀ g ∈ (permutation p a).cycleFactorsFinset,
        (descendingPositions g).card+1=g.support.card) ∧
      (n : ℤ)-2*height p a ≤ (fixedPositions (permutation p a)).card := by
  have hd := small_anchor_reserve_zero_defect p a (by omega)
  have he := anchor_reserve_decomposition p a
  rw [hz,hd] at he
  have hrank : height p a+(permutation p a).cycleFactorsFinset.card=(permutation p a).support.card := by omega
  have hcycles := LX.CycleGeometry.rank_descending_equality_cycles (permutation p a) hrank
  have hs := twice_cycle_count_le_support (permutation p a)
  have hf := fixed_positions_card (permutation p a)
  exact ⟨hd,hrank,hcycles,by omega⟩

/-- The increasing arrow and every descending arrow are recovered on each
actual cycle of the capacity phase; their physical endpoints are explicit. -/
theorem zero_strip_capacity_cycle_arrows (p : State n) (a : Fin n)
    (hz : anchorReserve p a=0) (g : State n) (hg : g ∈ (permutation p a).cycleFactorsFinset) :
    ∃ l r : Fin n,l ∈ g.support ∧ r ∈ g.support ∧ g l=r ∧ l.val < r.val ∧
      (∀ i ∈ g.support,l.val ≤ i.val ∧ i.val ≤ r.val) ∧
      (∀ i ∈ g.support,i ≠ l → (g i).val < i.val) :=
  LX.CycleGeometry.cycle_max_descending_single_ascent g
    (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hg).1
    ((zero_strip_capacity_structure p a hz).2.2.1 g hg)

/-- A capacity phase with no more than the dimension's extreme-count
allowance is a noncrossing matching. Majorization is not required. -/
theorem zero_strip_capacity_matching (p : State n) (a : Fin n)
    (hz : anchorReserve p a=0)
    (hf : ((fixedPositions (permutation p a)).card : ℤ) ≤ (n : ℤ)-2*height p a) :
    Function.Involutive (permutation p a) ∧ NoncrossingPairs (permutation p a) := by
  obtain ⟨hd,hrank,_,_⟩ := zero_strip_capacity_structure p a hz
  have hfixed := fixed_positions_card (permutation p a)
  have hsize := twice_cycle_count_le_support (permutation p a)
  have he : (permutation p a).support.card=2*(permutation p a).cycleFactorsFinset.card := by omega
  have hpairs := cycles_are_swaps_of_support_eq_twice_count (permutation p a) he
  have hinv := involutive_of_cycles_are_swaps (permutation p a) hpairs
  have hdef : (∑ i, |LRX.FiniteCuts.displacement (permutation p a) i|)-
      (inversionNumber (permutation p a) : ℤ)=((permutation p a).cycleFactorsFinset.card : ℤ) := by
    unfold cycleDefect at hd
    rw [he] at hd
    push_cast at hd
    omega
  exact ⟨hinv,finite_shallow_matching_noncrossing (permutation p a) _ he hdef⟩

/-- In even maximal height, one fixed position cannot attain full strip
capacity. This is the stopping obstruction for a one-fixed phase walk. -/
theorem even_one_fixed_positive_strip_reserve (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hf : (fixedPositions (permutation p a)).card=1) :
    1 ≤ anchorReserve p a := by
  have hnonneg := anchor_reserve_nonneg p a
  by_contra hnot
  have hz : anchorReserve p a=0 := by omega
  have hbound := (zero_strip_capacity_structure p a hz).2.2.2
  rw [hf] at hbound
  omega

#print axioms zero_strip_capacity_structure
#print axioms zero_strip_capacity_cycle_arrows
#print axioms zero_strip_capacity_matching
#print axioms even_one_fixed_positive_strip_reserve
end LX.AnchoredPhases
