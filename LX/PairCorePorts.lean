import LX.PairCoreGeometry

namespace LX.PairCore
variable {n : ℕ}

/-- Fixed points and the left endpoints of adjacent pairs hit every pair
interval of a noncrossing involution. -/
def ports (e : State n) : Finset (Fin n) :=
  LRX.FiniteCuts.fixedPositions e ∪ Finset.univ.filter (fun i => i.val+1=(e i).val)

theorem pair_hits_ports (e : State n) (hinv : Function.Involutive e)
    (hnc : LRX.FiniteCuts.NoncrossingPairs e) (a b : Fin n)
    (hab : a.val < b.val) (he : e a=b) :
    ∃ x ∈ ports e,a.val ≤ x.val ∧ x.val ≤ b.val := by
  by_cases hf : ∃ x : Fin n,a.val ≤ x.val ∧ x.val ≤ b.val ∧ e x=x
  · obtain ⟨x,hax,hxb,hx⟩ := hf
    refine ⟨x,Finset.mem_union_left _ ((LRX.FiniteCuts.mem_fixedPositions e x).mpr hx),hax,hxb⟩
  · have hfixed (x : Fin n) (hax : a.val ≤ x.val) (hxb : x.val ≤ b.val) : e x ≠ x := by
      intro hx
      exact hf ⟨x,hax,hxb,hx⟩
    obtain ⟨x,y,hax,hyb,hxy,hex⟩ := LRX.FiniteCuts.noncrossing_pair_contains_adjacent
      e hinv hnc a b hab he hfixed
    refine ⟨x,Finset.mem_union_right _ ?_,hax,by omega⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hex]; exact hxy⟩

/-- Pruning creates fixed points only at removed positions. -/
theorem fixed_positions_bound (q : State n) :
    (LRX.FiniteCuts.fixedPositions (permutation q)).card ≤
      (LRX.FiniteCuts.fixedPositions q).card+(positions q)ᶜ.card := by
  have hsub : LRX.FiniteCuts.fixedPositions (permutation q) ⊆
      LRX.FiniteCuts.fixedPositions q ∪ (positions q)ᶜ := by
    intro i hi
    have he : permutation q i=i := (LRX.FiniteCuts.mem_fixedPositions _ _).mp hi
    by_cases hh : q (q i)=i
    · rw [permutation_apply,ite_eq_left hh] at he
      exact Finset.mem_union_left _ ((LRX.FiniteCuts.mem_fixedPositions _ _).mpr he)
    · exact Finset.mem_union_right _ (by simpa [positions] using hh)
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- A moved arrow of the pruned factor is an unchanged transposition arrow
of the input permutation. -/
theorem moved_arrow_original (q : State n) (i : Fin n) (hi : permutation q i ≠ i) :
    permutation q i=q i ∧ q (q i)=i := by
  by_cases hh : q (q i)=i
  · exact ⟨by simp [hh],hh⟩
  · simp [hh] at hi

end LX.PairCore

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Small dimension-wide reserve forces height to be within one below the
largest half-size height; this is derived from the actual exchange count. -/
theorem small_dimension_reserve_height_gap (p : State n) (a : Fin n)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) : n ≤ 2*height p a+3 := by
  have hx := (candidate_price_components p a).1
  have hpar : (n : ℤ)=2*((n/2 : ℕ) : ℤ) ∨ (n : ℤ)=2*((n/2 : ℕ) : ℤ)+1 := by omega
  have hs : ((n : ℤ)-1-2*height p a)^2 ≤ 5 := by
    rcases hpar with he | ho <;> nlinarith
  by_contra hnot
  have hh : (3 : ℤ) ≤ (n : ℤ)-1-2*height p a := by omega
  nlinarith [sq_nonneg ((n : ℤ)-4-2*height p a)]

theorem majorized_anchor_fixed_positions (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) :
    ((LRX.FiniteCuts.fixedPositions (permutation p a)).card : ℤ) ≤ (n : ℤ)-2*height p a := by
  have hh := (short_coordinates (is_lift p a).1 hm a).2
  rw [displacement_anchor] at hh
  have hext := majorized_negative_level_count (is_lift p a).1 hm (height p a : ℤ) (by omega)
  have hs := LRX.FiniteCuts.shifted_support_add_extreme_count (is_lift p a)
    (height p a : ℤ) (displacement_band p a)
  rw [shifted_anchor_permutation] at hs
  have hf := LRX.FiniteCuts.fixed_positions_card (permutation p a)
  omega

/-- The matching part has at most nine fixed positions, including the
positions removed from long cycles. Their locations are still unrestricted. -/
theorem small_global_reserve_pair_core_fixed_count {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    (LRX.FiniteCuts.fixedPositions (LX.PairCore.permutation (permutation p a))).card ≤ 9 := by
  have hc := LX.PairCore.fixed_positions_bound (permutation p a)
  have hf := majorized_anchor_fixed_positions p a (global_minimum_majorized ha)
  have hh := small_dimension_reserve_height_gap p a hsmall
  have hr := (LX.PairCore.removed_positions_card (permutation p a)).trans
    (small_global_reserve_nonpair_mass ha hsmall)
  omega

/-- The reverse arrow of an actual adjacent pair attains the positive
endpoint n-1-h. Only a local two-cycle premise is used. -/
theorem actual_adjacent_reverse_coordinate (p : State n) (a i : Fin n)
    (hpair : permutation p a (permutation p a i)=i)
    (hi : i.val+1=(permutation p a i).val) :
    displacement p a (permutation p a i)=(n : ℤ)-1-height p a := by
  have hlt : i.val < (permutation p a i).val := by omega
  simp only [displacement,LRX.FiniteCuts.clockwiseRepresentative,hpair,ite_eq_left hlt]
  omega

/-- An adjacent pair in the matching core forces the odd maximal height.
In particular no such pair is possible in an even dimension. -/
theorem pair_core_adjacent_parity (p : State n) (a i : Fin n)
    (hm : Majorized (displacement p a))
    (hi : i.val+1=(LX.PairCore.permutation (permutation p a) i).val) :
    n=2*height p a+1 := by
  have hne : LX.PairCore.permutation (permutation p a) i ≠ i := by
    intro he
    rw [he] at hi
    omega
  obtain ⟨he,hpair⟩ := LX.PairCore.moved_arrow_original (permutation p a) i hne
  rw [he] at hi
  have hr := actual_adjacent_reverse_coordinate p a i hpair hi
  have hu := (short_coordinates (is_lift p a).1 hm (permutation p a i)).1
  have hl := (short_coordinates (is_lift p a).1 hm a).2
  rw [hr] at hu
  rw [displacement_anchor] at hl
  omega

/-- Majorization permits at most one adjacent pair in the retained matching.
This limits its possible innermost arcs without postulating a reflection. -/
theorem pair_core_unique_adjacent (p : State n) (a : Fin n)
    (hm : Majorized (displacement p a)) (i j : Fin n)
    (hi : i.val+1=(LX.PairCore.permutation (permutation p a) i).val)
    (hj : j.val+1=(LX.PairCore.permutation (permutation p a) j).val) : i=j := by
  have hn := pair_core_adjacent_parity p a i hm hi
  have hni : LX.PairCore.permutation (permutation p a) i ≠ i := by
    intro he; rw [he] at hi; omega
  have hnj : LX.PairCore.permutation (permutation p a) j ≠ j := by
    intro he; rw [he] at hj; omega
  obtain ⟨hei,hpi⟩ := LX.PairCore.moved_arrow_original (permutation p a) i hni
  obtain ⟨hej,hpj⟩ := LX.PairCore.moved_arrow_original (permutation p a) j hnj
  rw [hei] at hi
  rw [hej] at hj
  have hri := actual_adjacent_reverse_coordinate p a i hpi hi
  have hrj := actual_adjacent_reverse_coordinate p a j hpj hj
  have hc := majorized_level_count hm (height p a : ℤ) (by omega)
  have hc1 : (Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ))).card ≤ 1 := by omega
  have him : permutation p a i ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  have hjm : permutation p a j ∈ Finset.univ.filter (fun k => displacement p a k=(height p a : ℤ)) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    omega
  exact (permutation p a).injective (Finset.card_le_one.mp hc1 _ him _ hjm)

/-- The unit-reserve matching admits at most ten actual ports meeting every
pair interval. This is a geometric reduction, not yet a word-price bound. -/
theorem small_global_reserve_pair_ports {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hsmall : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-
      inversions (displacement p a) ≤ 1) :
    let e := LX.PairCore.permutation (permutation p a)
    ∃ P : Finset (Fin n),P.card ≤ 10 ∧
      ∀ i j : Fin n,i.val < j.val → e i=j →
        ∃ x ∈ P,i.val ≤ x.val ∧ x.val ≤ j.val := by
  intro e
  refine ⟨LX.PairCore.ports e,?_,?_⟩
  · have hf := small_global_reserve_pair_core_fixed_count ha hsmall
    have hadj : (Finset.univ.filter (fun i : Fin n => i.val+1=(e i).val)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro i hi j hj
      exact pair_core_unique_adjacent p a (global_minimum_majorized ha) i j
        (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    have hu := Finset.card_union_le (LRX.FiniteCuts.fixedPositions e)
      (Finset.univ.filter (fun i : Fin n => i.val+1=(e i).val))
    change (LX.PairCore.ports e).card ≤ _ at hu
    change (LRX.FiniteCuts.fixedPositions e).card ≤ 9 at hf
    omega
  · intro i j hij he
    exact LX.PairCore.pair_hits_ports e (LX.PairCore.permutation_involutive _)
      (small_global_reserve_pair_core ha hsmall) i j hij he

#print axioms small_global_reserve_pair_core_fixed_count
#print axioms pair_core_adjacent_parity
#print axioms pair_core_unique_adjacent
#print axioms small_global_reserve_pair_ports
end LX.AnchoredPhases
