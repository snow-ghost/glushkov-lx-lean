import LX.PairCorePorts

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Equal exchange counts at actual anchors of the same input give equal
energies. Thus a new anchor inherits global minimality, not just a height bound. -/
theorem global_minimum_of_equal_exchanges {p : State n} {a b : Fin n}
    (ha : GlobalMinimum p a)
    (hx : inversions (displacement p b)=inversions (displacement p a)) : GlobalMinimum p b := by
  have he := anchor_energy_inversion_invariant p a b
  rw [hx] at he
  have heq : energy (displacement p b)=energy (displacement p a) := by omega
  intro c d hd
  rw [heq]
  exact ha c d hd

/-- In the remaining odd unit-reserve case a minimum-height anchor also
minimizes exchanges, and its own strip reserve is zero. -/
theorem odd_unit_reserve_matching_anchor {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m+1) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)^2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,GlobalMinimum p b ∧ height p b+1=m ∧ anchorReserve p b=0 := by
  obtain ⟨b,hmin,hheight⟩ := odd_unpaid_single_height p m hn hn4 hunpaid
  have hx := (candidate_price_components p b).1
  have hle := global_minimum_exchanges ha b
  have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
  have hh : (height p b : ℤ)+1=m := by exact_mod_cast hheight
  have hx' : inversions (displacement p b)=inversions (displacement p a) := by
    have hle' : (inversions (displacement p a) : ℤ) ≤ inversions (displacement p b) := by exact_mod_cast hle
    have he : (inversions (displacement p b) : ℤ)=(inversions (displacement p a) : ℤ) := by nlinarith
    exact_mod_cast he
  refine ⟨b,global_minimum_of_equal_exchanges ha hx',hheight,?_⟩
  unfold anchorReserve
  rw [hx']
  nlinarith

/-- The true source after the new phase selection is a noncrossing matching
with exactly three fixed positions and no adjacent pair. The old six-position
exception set is no longer needed in this odd branch. -/
theorem odd_unit_reserve_three_fixed_matching {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m+1) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)^2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,GlobalMinimum p b ∧ height p b+1=m ∧
      Function.Involutive (permutation p b) ∧ LRX.FiniteCuts.NoncrossingPairs (permutation p b) ∧
      (LRX.FiniteCuts.fixedPositions (permutation p b)).card=3 ∧
      ∀ i : Fin n,i.val+1 ≠ (permutation p b i).val := by
  obtain ⟨b,hb,hh,hzero⟩ := odd_unit_reserve_matching_anchor hn4 m hn ha hunit hunpaid
  have hm := global_minimum_majorized hb
  have hd := is_lift p b
  have heq : (LRX.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+displacement p b i) : ℤ)=
      (height p b : ℤ)*((n : ℤ)-height p b-1) := by
    change (inversions (displacement p b) : ℤ)=_
    unfold anchorReserve at hzero
    omega
  obtain ⟨hs,hc,hdef,hpairs⟩ := LRX.FiniteCuts.inherited_capacity_equality_pairs hd.1 hm hd
    (height p b : ℤ) (by omega) (displacement_band p b) (fun _ hi => hi) heq
  simp only [shifted_anchor_permutation] at hs hc hdef hpairs
  have hinv := LRX.FiniteCuts.involutive_of_cycles_are_swaps (permutation p b) hpairs
  have hnc : LRX.FiniteCuts.NoncrossingPairs (permutation p b) := by
    intro i j k l hij hjk hkl hik
    have ht := LRX.FiniteCuts.inherited_capacity_equality_noncrossing hd.1 hm hd
      (height p b : ℤ) (by omega) (displacement_band p b) (fun _ hi => hi) heq
    simpa only [shifted_anchor_permutation] using ht i j k l hij hjk hkl (by
      simpa only [shifted_anchor_permutation] using hik)
  have hf := LRX.FiniteCuts.fixed_positions_card (permutation p b)
  refine ⟨b,hb,hh,hinv,hnc,by omega,?_⟩
  intro i hi
  have hr := actual_adjacent_reverse_coordinate p b i (hinv i) hi
  have hu := (short_coordinates hd.1 hm (permutation p b i)).1
  rw [hr] at hu
  omega

/-- The three ports are the actual fixed positions of the selected source;
every transposition interval contains one of them. -/
theorem odd_unit_reserve_three_ports {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m+1) (ha : GlobalMinimum p a)
    (hunit : (inversions (displacement p a) : ℤ)+1=(m : ℤ)^2)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,GlobalMinimum p b ∧ height p b+1=m ∧
      Function.Involutive (permutation p b) ∧ LRX.FiniteCuts.NoncrossingPairs (permutation p b) ∧
      (LRX.FiniteCuts.fixedPositions (permutation p b)).card=3 ∧
      ∀ i j : Fin n,i.val < j.val → permutation p b i=j →
        ∃ x ∈ LRX.FiniteCuts.fixedPositions (permutation p b),i.val ≤ x.val ∧ x.val ≤ j.val := by
  obtain ⟨b,hb,hh,hinv,hnc,hcard,hnoadj⟩ := odd_unit_reserve_three_fixed_matching hn4 m hn ha hunit hunpaid
  refine ⟨b,hb,hh,hinv,hnc,hcard,?_⟩
  intro i j hij he
  obtain ⟨x,hx,hix,hxj⟩ := LX.PairCore.pair_hits_ports (permutation p b) hinv hnc i j hij he
  rcases Finset.mem_union.mp hx with hfixed | hadj
  · exact ⟨x,hfixed,hix,hxj⟩
  · exact False.elim (hnoadj x (Finset.mem_filter.mp hadj).2)

/-- In the selected three-fixed-position matching, two different innermost
arcs of length two would consume the same unique positive extreme. -/
theorem three_fixed_matching_unique_gap_two (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (hn : n=2*height p a+3)
    (hinv : Function.Involutive (permutation p a)) (i j : Fin n)
    (hi : i.val+2=(permutation p a i).val)
    (hj : j.val+2=(permutation p a j).val) : i=j := by
  have hreverse (k : Fin n) (hk : k.val+2=(permutation p a k).val) :
      displacement p a (permutation p a k)=(height p a : ℤ)+1 := by
    have hlt : k.val < (permutation p a k).val := by omega
    have hpair := hinv k
    simp only [displacement,LRX.FiniteCuts.clockwiseRepresentative,hpair,ite_eq_left hlt]
    omega
  have hri := hreverse i hi
  have hrj := hreverse j hj
  have hc := majorized_level_count hm ((height p a : ℤ)+1) (by omega)
  have hc1 : (Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1)).card ≤ 1 := by omega
  have him : permutation p a i ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hri
  have hjm : permutation p a j ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)+1) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hrj
  exact (permutation p a).injective (Finset.card_le_one.mp hc1 _ him _ hjm)

#print axioms global_minimum_of_equal_exchanges
#print axioms odd_unit_reserve_matching_anchor
#print axioms odd_unit_reserve_three_fixed_matching
#print axioms odd_unit_reserve_three_ports
#print axioms three_fixed_matching_unique_gap_two
end LX.AnchoredPhases
