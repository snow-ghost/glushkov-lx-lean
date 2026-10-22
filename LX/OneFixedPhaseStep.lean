import LX.CapacityCycleStructure
import LX.UniqueFixedCursor

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Raising the unique minimum remains a strict-width lift and recovers
an actual anchor. Height cannot increase, and exchange and offset changes
are exact. The construction does not assume majorization of the new phase. -/
theorem one_fixed_next_anchor (p : State n) (a : Fin n)
    (hf : (fixedPositions (permutation p a)).card=1) :
    ∃ b : Fin n,height p b ≤ height p a ∧
      (inversions (displacement p b) : ℤ)-inversions (displacement p a)=
        (n : ℤ)-1-2*height p a ∧
      p b-b+(height p b : Fin n)=p a-a+(height p a : Fin n)+1 := by
  let d := displacement p a
  let e := raiseMinimum d a
  have hd := is_lift p a
  have hmin (i : Fin n) : d a ≤ d i := by
    have hb := (displacement_band p a i).1
    change displacement p a a ≤ displacement p a i
    rw [displacement_anchor]
    omega
  have hunique (i : Fin n) (hi : d i=d a) : i=a := by
    have hi' : displacement p a i= -(height p a : ℤ) := hi.trans (displacement_anchor p a)
    rw [displacement_offset] at hi'
    have hz : cyclicOffset p a i=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
    exact one_fixed_last_offset p a hf i (sub_eq_zero.mp hz)
  have hwidth := displacement_strict_width p a
  have helower (i : Fin n) : -(height p a : ℤ) ≤ e i := by
    have hh := raise_unique_minimum_lower d a hmin hunique i
    change displacement p a a ≤ e i at hh
    rwa [displacement_anchor] at hh
  have heupper (i : Fin n) : e i ≤ (n : ℤ)-height p a-1 := by
    change raiseMinimum d a i ≤ _
    rw [raise_minimum_apply]
    by_cases hi : i=a
    · subst i
      rw [ite_eq_left rfl]
      change displacement p a a-1+(n : ℤ) ≤ _
      rw [displacement_anchor]
      omega
    · rw [ite_eq_right hi]
      have hh := (displacement_band p a i).2
      change displacement p a i-1+0 ≤ _
      omega
  have hewidth (i j : Fin n) : e i-e j < (n : ℤ) := by
    have hi := heupper i
    have hj := helower j
    omega
  have heLift := raise_minimum_lift hd a
  obtain ⟨b,_,hb⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) e ⟨a,Finset.mem_univ _⟩
  obtain ⟨heq,hphase⟩ := recovers_strict_strip heLift b (fun i => hb i (Finset.mem_univ _)) (fun i => hewidth i b)
  change displacement p b=e at heq
  have hheight : height p b ≤ height p a := by
    have hh := helower b
    rw [← heq,displacement_anchor] at hh
    omega
  have hprice := raise_minimum_inversions hd a hmin hwidth
  rw [displacement_anchor] at hprice
  refine ⟨b,hheight,?_,?_⟩
  · rw [heq]
    change (inversions (raiseMinimum (displacement p a) a) : ℤ)-inversions (displacement p a)=_
    linarith
  · simp only [phase,Int.cast_add,Int.cast_sub,Int.cast_natCast,Int.cast_one,
      Fin.cast_val_eq_self,Fin.natCast_self] at hphase
    linear_combination -hphase

/-- For the unpaid even source, a height drop would already be paid.
Thus the unique minimum leads to an actual same-height phase one raw offset
later, costing exactly one exchange and leaving one or two fixed positions. -/
theorem even_unpaid_one_fixed_next_phase {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hf : (fixedPositions (permutation p a)).card=1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ b : Fin n,height p b=height p a ∧ p b-b=p a-a+1 ∧
      inversions (displacement p b)=inversions (displacement p a)+1 ∧
      anchorReserve p b=anchorReserve p a-1 ∧
      ¬GlobalMinimum p b ∧
      ((fixedPositions (permutation p b)).card=1 ∨ (fixedPositions (permutation p b)).card=2) := by
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  obtain ⟨b,hle,hprice,hoff⟩ := one_fixed_next_anchor p a hf
  have hx : inversions (displacement p b)=inversions (displacement p a)+1 := by omega
  have hheight : height p b=height p a := by
    by_contra hnot
    by_cases hsecond : height p b+1=height p a
    · exact hunpaid (even_second_near_minimum_upper_word hn4 ha b (by omega) 1 hx.le (by omega))
    · obtain ⟨w,hw,hbound⟩ := height_five_word (by omega : 2 ≤ n) p b (by omega)
      exact hunpaid ⟨w,hw,by linarith⟩
  have hraw : p b-b=p a-a+1 := by
    rw [hheight] at hoff
    linear_combination hoff
  have hreserve : anchorReserve p b=anchorReserve p a-1 := by
    unfold anchorReserve
    rw [hheight,hx]
    push_cast
    ring
  have hnotmin : ¬GlobalMinimum p b := by
    intro hb
    have hle := global_minimum_exchanges hb a
    omega
  have hm := near_majorized_of_exchange_allowance ha b 1 hx.le
  let F := fixedPositions (permutation p b)
  have hsum : (∑ i ∈ F,-displacement p b i)=(F.card : ℤ)*height p b := by
    have he : (∑ i ∈ F,-displacement p b i)=∑ _i ∈ F,(height p b : ℤ) :=
      Finset.sum_congr rfl (fun i hi => by rw [fixed_source_displacement p b i hi]; ring)
    rw [he]
    simp
  have hquad := near_majorized_neg (is_lift p b).1 hm F
  rw [hsum] at hquad
  have hn' : (n : ℤ)=2*(height p b : ℤ)+2 := by omega
  have hcard : F.card ≤ 2 := by
    by_contra hnot
    have hp := mul_nonneg (show (0 : ℤ) ≤ (F.card : ℤ)-3 by omega)
      (show (0 : ℤ) ≤ (F.card : ℤ)+1 by omega)
    norm_num only [Nat.cast_one] at hquad
    nlinarith
  have hpos : 0 < F.card := Finset.card_pos.mpr
    ⟨b,(mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
  exact ⟨b,hheight,hraw,hx,hreserve,hnotmin,by change F.card=1 ∨ F.card=2; omega⟩

#print axioms one_fixed_next_anchor
#print axioms even_unpaid_one_fixed_next_phase
end LX.AnchoredPhases
