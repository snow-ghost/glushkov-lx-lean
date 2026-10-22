import LX.SmallExchangeReserve

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- If every global minimum in odd dimension has maximal height, the
singleton minimum is tight and advances the minimum phase by one offset.
The resulting orbit contains every residue, forcing a complete mapping. -/
theorem odd_maximal_minima_complete (p : State n) (m : ℕ) (hn : n=2*m+1)
    (hheight : ∀ a : Fin n,GlobalMinimum p a → height p a=m) : CompleteMapping p := by
  have hstep (a : Fin n) (ha : GlobalMinimum p a) :
      ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+1 := by
    have hh := hheight a ha
    let S := (Finset.univ : Finset (Fin n)).erase a
    have hcard : S.card=n-1 := by simp [S]
    have hsum : (∑ i ∈ S,displacement p a i)=(m : ℤ) := by
      have hs := Finset.sum_erase_add Finset.univ (displacement p a) (Finset.mem_univ a)
      rw [displacement_balance,displacement_anchor,hh] at hs
      change (∑ i ∈ S,displacement p a i)+ -(m : ℤ)=0 at hs
      omega
    have htight : 2*(∑ i ∈ S,displacement p a i)=(S.card : ℤ)*((n : ℤ)-S.card) := by
      rw [hsum,hcard,Nat.cast_sub (NeZero.pos n)]
      norm_num only [Nat.cast_one]
      have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
      nlinarith
    obtain ⟨b,hb,_,hphase,_⟩ := zero_slack_phase ha S htight
    have hbheight := hheight b hb
    rw [hcard,Nat.cast_sub (NeZero.pos n),Fin.natCast_self,Nat.cast_one] at hphase
    simp only [phase,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,hh,hbheight] at hphase
    exact ⟨b,hb,by linear_combination -hphase⟩
  obtain ⟨a,ha⟩ := exists_global_minimum p
  have hiter : ∀ k : ℕ,∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+(k : Fin n) := by
    intro k
    induction k with
    | zero => exact ⟨a,ha,by simp⟩
    | succ k ih =>
      obtain ⟨b,hb,hbr⟩ := ih
      obtain ⟨c,hc,hcr⟩ := hstep b hb
      refine ⟨c,hc,?_⟩
      rw [hcr,hbr,Nat.cast_add,Nat.cast_one]
      ring
  apply Finite.injective_iff_surjective.mpr
  intro r
  obtain ⟨b,_,hbr⟩ := hiter (r-(p a-a)).val
  simp only [Fin.cast_val_eq_self] at hbr
  exact ⟨b,by linear_combination hbr⟩

/-- An unpaid odd input has a globally minimal, majorized phase exactly
one below the maximal height. The chosen phase is not merely height-minimal. -/
theorem odd_unpaid_lower_global_minimum (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m+1)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m := by
  by_contra hnone
  have hheight (a : Fin n) (ha : GlobalMinimum p a) : height p a=m := by
    have hh := (short_coordinates (is_lift p a).1 (global_minimum_majorized ha) a).2
    rw [displacement_anchor] at hh
    by_contra hnot
    have hne : height p a+1 ≠ m := fun he => hnone ⟨a,ha,he⟩
    have hlow : 2*height p a+5 ≤ n := by omega
    obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a hlow
    exact hunpaid ⟨w,hw,by linarith⟩
  exact hunpaid (complete_mapping_upper_word p (odd_maximal_minima_complete p m hn hheight) hn4)

/-- The lower global phase removes a whole additional lap from the uniform
odd budget. Any unpaid odd input has reserve at most m-29, for n=2m+1. -/
theorem odd_unpaid_reserve_upper {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m+1) (ha : GlobalMinimum p a)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    (m : ℤ)^2-inversions (displacement p a) ≤ (m : ℤ)-29 := by
  obtain ⟨b,hb,hh⟩ := odd_unpaid_lower_global_minimum hn4 p m hn hunpaid
  have hx : inversions (displacement p b)=inversions (displacement p a) :=
    Nat.le_antisymm (global_minimum_exchanges hb a) (global_minimum_exchanges ha b)
  by_contra hnot
  obtain ⟨w,hw,hprice⟩ := majorized_exchange_reserve_word (by omega : 2 ≤ n)
    p (phase p b) (displacement p b) (is_lift p b) (global_minimum_majorized hb)
    (height p b) (by omega) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i)
  rw [hx] at hprice
  have hn' : (n : ℤ)=2*(m : ℤ)+1 := by exact_mod_cast hn
  have hh' : (height p b : ℤ)+1=m := by exact_mod_cast hh
  exact hunpaid ⟨w,hw,by nlinarith⟩

#print axioms odd_maximal_minima_complete
#print axioms odd_unpaid_lower_global_minimum
#print axioms odd_unpaid_reserve_upper
end LX.AnchoredPhases
