import LX.EvenSecondReserve

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The exact two-step phase transition uses only equal maximal heights
of the minima and two fixed positions. No exchange-reserve restriction is needed. -/
theorem maximal_even_two_fixed_next_phase {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a) (hn : n=2*height p a+2)
    (hf : (fixedPositions (permutation p a)).card=2)
    (hheight : ∀ b : Fin n,GlobalMinimum p b → height p b=height p a) :
    ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=(p a-a)+2 := by
  let F := fixedPositions (permutation p a)
  have hsum : (∑ j ∈ F,displacement p a j)= -2*(height p a : ℤ) := by
    have heq : (∑ j ∈ F,displacement p a j)=∑ _j ∈ F,-(height p a : ℤ) :=
      Finset.sum_congr rfl (fun j hj => fixed_source_displacement p a j hj)
    rw [heq]
    simp only [Finset.sum_const,nsmul_eq_mul]
    change (F.card : ℤ)*_= -2*_
    rw [hf]
    ring
  have htop : (∑ j ∈ Fᶜ,displacement p a j)=2*(height p a : ℤ) := by
    have he := Finset.sum_compl_add_sum F (displacement p a)
    rw [hsum,displacement_balance] at he
    omega
  have hcard : Fᶜ.card=n-2 := by rw [Finset.card_compl,Fintype.card_fin,hf]
  have htight : 2*(∑ j ∈ Fᶜ,displacement p a j)=(Fᶜ.card : ℤ)*((n : ℤ)-Fᶜ.card) := by
    rw [htop,hcard,Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num only [Nat.cast_ofNat]
    have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
    nlinarith
  obtain ⟨b,hb,_,hphase,_⟩ := zero_slack_phase ha Fᶜ htight
  have heighth := hheight b hb
  have hphase' : (phase p b : Fin n)=(phase p a : Fin n)-2 := by
    rw [hcard,Nat.cast_sub (by omega : 2 ≤ n),Fin.natCast_self] at hphase
    simpa only [zero_sub,sub_eq_add_neg,Nat.cast_ofNat,zero_add] using hphase
  refine ⟨b,hb,?_⟩
  simp only [phase,Int.cast_sub,Int.cast_natCast,Fin.cast_val_eq_self,heighth] at hphase'
  linear_combination -hphase'

/-- Repeated exact phase transitions reach every offset in the same
even-difference class, with witnesses remaining global minima throughout. -/
theorem two_step_minimum_orbit {p : State n} {a : Fin n}
    (ha : GlobalMinimum p a)
    (hstep : ∀ b : Fin n,GlobalMinimum p b →
      ∃ c : Fin n,GlobalMinimum p c ∧ p c-c=(p b-b)+2)
    (r : Fin n) (he : Even (r-(p a-a))) :
    ∃ b : Fin n,GlobalMinimum p b ∧ p b-b=r := by
  have hiter : ∀ k : ℕ,∃ b : Fin n,GlobalMinimum p b ∧
      p b-b=(p a-a)+(k : Fin n)+(k : Fin n) := by
    intro k
    induction k with
    | zero => exact ⟨a,ha,by simp⟩
    | succ k ih =>
      obtain ⟨b,hb,hbr⟩ := ih
      obtain ⟨c,hc,hcr⟩ := hstep b hb
      refine ⟨c,hc,?_⟩
      rw [hcr,hbr,Nat.cast_add,Nat.cast_one]
      ring
  obtain ⟨t,ht⟩ := he
  obtain ⟨b,hb,hbr⟩ := hiter t.val
  simp only [Fin.cast_val_eq_self] at hbr
  exact ⟨b,hb,by linear_combination hbr-ht⟩

/-- Among raw offsets minus 8 through minus 11, an exact two-step orbit
provides a minimum phase different from the original head's offset. -/
theorem two_step_terminal_anchor {p : State n} {a : Fin n}
    (hn : 12 ≤ n) (ha : GlobalMinimum p a)
    (hstep : ∀ b : Fin n,GlobalMinimum p b →
      ∃ c : Fin n,GlobalMinimum p c ∧ p c-c=(p b-b)+2) :
    ∃ b : Fin n,∃ k : ℕ,GlobalMinimum p b ∧ 8 ≤ k ∧ k ≤ 11 ∧
      p b-b= -(k : Fin n) ∧ p 0 ≠ p b-b := by
  let r := p a-a
  have heven : ∃ k : ℕ,(k=10 ∨ k=11) ∧ Even (-(k : Fin n)-r) := by
    rcases Nat.even_or_odd r.val with h | h
    · have hh : Even (r.val+10) := h.add (by decide)
      have hc : Even ((r.val+10 : ℕ) : Fin n) := hh.natCast
      simp only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_ofNat] at hc
      refine ⟨10,Or.inl rfl,?_⟩
      convert hc.neg using 1 <;> ring
    · have hh : Even (r.val+11) := h.add_odd (by decide)
      have hc : Even ((r.val+11 : ℕ) : Fin n) := hh.natCast
      simp only [Nat.cast_add,Fin.cast_val_eq_self,Nat.cast_ofNat] at hc
      refine ⟨11,Or.inr rfl,?_⟩
      convert hc.neg using 1 <;> ring
  obtain ⟨k,hk,hke⟩ := heven
  obtain ⟨b,hb,hbr⟩ := two_step_minimum_orbit ha hstep (-(k : Fin n)) hke
  by_cases hhead : p 0=p b-b
  · obtain ⟨c,hc,hcr⟩ := hstep b hb
    refine ⟨c,k-2,hc,by omega,by omega,?_,?_⟩
    · rw [hcr,hbr,Nat.cast_sub (by omega : 2 ≤ k)]
      push_cast
      ring
    · intro he
      have hcancel : (p b-b)+2=(p b-b)+0 := by
        simpa only [add_zero] using hcr.symm.trans (he.symm.trans hhead)
      have htwo : (2 : Fin n)=0 := add_left_cancel hcancel
      have hv := congrArg Fin.val htwo
      norm_num [Nat.mod_eq_of_lt (by omega : 2 < n)] at hv
  · exact ⟨b,k,hb,by omega,by omega,hbr,hhead⟩

#print axioms maximal_even_two_fixed_next_phase
#print axioms two_step_terminal_anchor
end LX.AnchoredPhases
