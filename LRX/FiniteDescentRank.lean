import LRX.FiniteDepthRank

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ}

/-- Positions whose images lie strictly to their left; these are not adjacent descents. -/
def descendingPositions (p : State n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => (p i).val < i.val)

@[simp] theorem mem_descendingPositions (p : State n) (i : Fin n) :
    i ∈ descendingPositions p ↔ (p i).val < i.val := by
  simp [descendingPositions]

theorem descending_positions_subset_support (p : State n) :
    descendingPositions p ⊆ p.support := by
  intro i hi
  apply Equiv.Perm.mem_support.mpr
  intro heq
  have h := (mem_descendingPositions p i).mp hi
  rw [heq] at h
  omega

theorem descending_positions_mul (p q : State n) (h : p.Disjoint q) :
    descendingPositions (p*q) = descendingPositions p ∪ descendingPositions q := by
  ext i
  simp only [Finset.mem_union, mem_descendingPositions]
  rcases h i with hi | hi
  · have hm : (p*q) i = q i := by rw [h.commute.eq]; simp [hi]
    rw [hm,hi]
    omega
  · have hm : (p*q) i = p i := by simp [hi]
    rw [hm,hi]
    omega

theorem descending_positions_disjoint (p q : State n) (h : p.Disjoint q) :
    Disjoint (descendingPositions p) (descendingPositions q) := by
  apply Finset.disjoint_left.mpr
  intro i hp hq
  have hp := (mem_descendingPositions p i).mp hp
  have hq := (mem_descendingPositions q i).mp hq
  rcases h i with hi | hi
  · rw [hi] at hp; omega
  · rw [hi] at hq; omega

theorem descending_count_mul (p q : State n) (h : p.Disjoint q) :
    (descendingPositions (p*q)).card =
      (descendingPositions p).card + (descendingPositions q).card := by
  rw [descending_positions_mul p q h,
    Finset.card_union_of_disjoint (descending_positions_disjoint p q h)]

@[simp] theorem descending_positions_one : descendingPositions (1 : State n) = ∅ := by
  ext i
  simp

theorem descending_count_list_prod (l : List (State n)) (h : l.Pairwise Equiv.Perm.Disjoint) :
    (descendingPositions l.prod).card = (l.map (fun p => (descendingPositions p).card)).sum := by
  induction l with
  | nil => simp
  | cons p l ih =>
    obtain ⟨hp,hl⟩ := List.pairwise_cons.mp h
    have hd : p.Disjoint l.prod := Equiv.Perm.disjoint_prod_right l hp
    simpa using (descending_count_mul p l.prod hd).trans (by rw [ih hl])

theorem descending_count_cycle_sum (p : State n) :
    (descendingPositions p).card = ∑ q ∈ p.cycleFactorsFinset, (descendingPositions q).card := by
  classical
  obtain ⟨l,hn,heq⟩ := p.cycleFactorsFinset.exists_list_nodup_eq
  have h := (Equiv.Perm.cycleFactorsFinset_eq_list_toFinset hn).mp heq.symm
  rw [← heq, List.sum_toFinset _ hn, ← descending_count_list_prod l h.2.1, h.2.2]

/-- A nontrivial cycle has a minimum moved position which cannot move left. -/
theorem cycle_descending_count_lt_support {p : State n} (hp : p.IsCycle) :
    (descendingPositions p).card < p.support.card := by
  classical
  have hne : p.support.Nonempty := Finset.card_pos.mp (by have := hp.two_le_card_support; omega)
  let a := p.support.min' hne
  have ha : a ∈ p.support := Finset.min'_mem _ hne
  have hpa : p a ∈ p.support := Equiv.Perm.apply_mem_support.mpr ha
  have hmin : a ≤ p a := Finset.min'_le _ _ hpa
  have hnot : a ∉ descendingPositions p := by
    rw [mem_descendingPositions]
    exact not_lt.mpr hmin
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨descending_positions_subset_support p,?_⟩
  intro heq
  exact hnot (heq.symm ▸ ha)

/-- Each cycle contributes at least one position that does not move left. -/
theorem descending_count_add_cycles_le_support (p : State n) :
    (descendingPositions p).card + p.cycleFactorsFinset.card ≤ p.support.card := by
  classical
  have h : ∑ q ∈ p.cycleFactorsFinset, ((descendingPositions q).card+1) ≤
      ∑ q ∈ p.cycleFactorsFinset, q.support.card := by
    apply Finset.sum_le_sum
    intro q hq
    exact cycle_descending_count_lt_support (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).1
  simpa only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
    ← descending_count_cycle_sum, cycle_support_card_sum] using h

/-- The finite depth bound with the left-moving position count needed by the strict-band cap. -/
theorem finite_depth_descending (p : State n) :
    (inversionNumber p : ℤ) + ((descendingPositions p).card : ℤ) ≤
      ∑ i : Fin n, |displacement p i| := by
  have hr := finite_depth_rank p
  have hc : ((descendingPositions p).card : ℤ) + (p.cycleFactorsFinset.card : ℤ) ≤
      (p.support.card : ℤ) := by exact_mod_cast descending_count_add_cycles_le_support p
  omega

/-- Half of the displacement mass, summed over positions moving left. -/
def leftDepth (p : State n) : ℤ :=
  ∑ i ∈ descendingPositions p, ((i : ℤ)-(p i : ℤ))

theorem displacement_mass_eq_twice_leftDepth (p : State n) :
    (∑ i : Fin n, |displacement p i|) = 2*leftDepth p := by
  have hbalance : (∑ i : Fin n, displacement p i)=0 := (canonical_lift p).1
  have hpoint (i : Fin n) : |displacement p i| = displacement p i +
      2*(if (p i).val < i.val then (i : ℤ)-(p i : ℤ) else 0) := by
    unfold displacement
    split_ifs with h
    · rw [abs_of_neg (by omega)]
      ring
    · rw [abs_of_nonneg (by omega)]
      ring
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib, hbalance, zero_add, ← Finset.mul_sum]
  congr 1
  simp only [leftDepth, descendingPositions, Finset.sum_filter]

/-- This is the finite input `2 dep - I ≥ #D` to the affine capacity identity. -/
theorem leftDepth_inversion_deficit (p : State n) :
    ((descendingPositions p).card : ℤ) ≤ 2*leftDepth p-(inversionNumber p : ℤ) := by
  have h := finite_depth_descending p
  rw [displacement_mass_eq_twice_leftDepth] at h
  omega

#print axioms descending_count_add_cycles_le_support
#print axioms finite_depth_descending
#print axioms leftDepth_inversion_deficit
end LRX.FiniteCuts
