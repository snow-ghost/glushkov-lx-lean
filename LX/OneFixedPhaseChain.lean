import LX.MinimumHeightPrefix
import LX.OneFixedPhaseStep

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Along a minimum-height even phase, a singleton fixed set advances the
raw offset by one and spends exactly one unit of the strip reserve. -/
theorem minimum_height_singleton_step (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hmin : ∀ b,height p a ≤ height p b)
    (hf : (fixedPositions (permutation p a)).card=1) :
    ∃ b : Fin n,height p b=height p a ∧ p b-b=p a-a+1 ∧
      inversions (displacement p b)=inversions (displacement p a)+1 ∧
      anchorReserve p b=anchorReserve p a-1 := by
  obtain ⟨b,hb,hI,hoff⟩ := one_fixed_next_anchor p a hf
  have hh : height p b=height p a := Nat.le_antisymm hb (hmin b)
  have hx : inversions (displacement p b)=inversions (displacement p a)+1 := by omega
  refine ⟨b,hh,?_,hx,?_⟩
  · rw [hh] at hoff
    linear_combination hoff
  · unfold anchorReserve
    rw [hh,hx]
    push_cast
    ring

/-- A chain of singleton phases terminates at a genuine multiple-fixed
phase. The number of steps, exchange cost, and raw phase change agree
exactly; no majorization of the terminal phase is assumed. -/
theorem minimum_height_multiple_fixed_phase (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hmin : ∀ b,height p a ≤ height p b) :
    ∃ b : Fin n,∃ k : ℕ,2 ≤ (fixedPositions (permutation p b)).card ∧
      height p b=height p a ∧ p b-b=p a-a+(k : Fin n) ∧
      inversions (displacement p b)=inversions (displacement p a)+k ∧
      anchorReserve p b=anchorReserve p a-k ∧ (k : ℤ) ≤ anchorReserve p a := by
  have aux : ∀ K : ℕ,∀ a : Fin n,n=2*height p a+2 →
      (∀ b,height p a ≤ height p b) → anchorReserve p a ≤ K →
      ∃ b : Fin n,∃ k : ℕ,2 ≤ (fixedPositions (permutation p b)).card ∧
        height p b=height p a ∧ p b-b=p a-a+(k : Fin n) ∧
        inversions (displacement p b)=inversions (displacement p a)+k ∧
        anchorReserve p b=anchorReserve p a-k ∧ (k : ℤ) ≤ anchorReserve p a := by
    intro K
    induction K with
    | zero =>
      intro a hn hmin hK
      have hf : 2 ≤ (fixedPositions (permutation p a)).card := by
        by_contra hnot
        have hpos : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
          ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
        obtain ⟨b,_,_,_,hr⟩ := minimum_height_singleton_step p a hn hmin (by omega)
        have hb := anchor_reserve_nonneg p b
        norm_num at hK
        omega
      exact ⟨a,0,hf,rfl,by simp,by simp,by simp,anchor_reserve_nonneg p a⟩
    | succ K ih =>
      intro a hn hmin hK
      by_cases hf : 2 ≤ (fixedPositions (permutation p a)).card
      · exact ⟨a,0,hf,rfl,by simp,by simp,by simp,anchor_reserve_nonneg p a⟩
      · have hpos : 0 < (fixedPositions (permutation p a)).card := Finset.card_pos.mpr
          ⟨a,(mem_fixedPositions _ _).mpr (permutation_anchor p a)⟩
        obtain ⟨b,hb,hoff,hI,hr⟩ := minimum_height_singleton_step p a hn hmin (by omega)
        obtain ⟨c,k,hcf,hch,hcoff,hcI,hcr,hck⟩ := ih b (by omega)
          (fun c => by rw [hb]; exact hmin c) (by omega)
        refine ⟨c,k+1,hcf,hch.trans hb,?_,by omega,?_,?_⟩
        · rw [hcoff,hoff,Nat.cast_add,Nat.cast_one]
          ring
        · rw [hcr,hr,Nat.cast_add,Nat.cast_one]
          ring
        · have hc := anchor_reserve_nonneg p c
          omega
  exact aux (anchorReserve p a).toNat a hn hmin
    (by rw [Int.toNat_of_nonneg (anchor_reserve_nonneg p a)])

/-- A singleton start requires a positive number of steps. -/
theorem minimum_height_singleton_chain (p : State n) (a : Fin n)
    (hn : n=2*height p a+2) (hmin : ∀ b,height p a ≤ height p b)
    (hf : (fixedPositions (permutation p a)).card=1) :
    ∃ b : Fin n,∃ k : ℕ,0 < k ∧ 2 ≤ (fixedPositions (permutation p b)).card ∧
      height p b=height p a ∧ p b-b=p a-a+(k : Fin n) ∧
      inversions (displacement p b)=inversions (displacement p a)+k ∧
      anchorReserve p b=anchorReserve p a-k ∧ (k : ℤ) ≤ anchorReserve p a := by
  obtain ⟨b,hb,hoff,hI,hr⟩ := minimum_height_singleton_step p a hn hmin hf
  obtain ⟨c,k,hcf,hch,hcoff,hcI,hcr,hck⟩ := minimum_height_multiple_fixed_phase p b
    (by omega) (fun c => by rw [hb]; exact hmin c)
  refine ⟨c,k+1,by omega,hcf,hch.trans hb,?_,by omega,?_,?_⟩
  · rw [hcoff,hoff,Nat.cast_add,Nat.cast_one]
    ring
  · rw [hcr,hr,Nat.cast_add,Nat.cast_one]
    ring
  · have hc := anchor_reserve_nonneg p c
    omega

#print axioms minimum_height_singleton_step
#print axioms minimum_height_multiple_fixed_phase
#print axioms minimum_height_singleton_chain

/-- Before the orientation seam, every singleton step spends one exchange
and shortens the final cyclic gap by one. Their contribution to the price
is invariant along the entire chain. -/
theorem singleton_chain_cyclic_price (p : State n) (a b : Fin n) (k : ℕ)
    (hoff : p b-b=p a-a+(k : Fin n))
    (hr : anchorReserve p b=anchorReserve p a-k)
    (hk : (k : ℤ) ≤ anchorReserve p a)
    (hgap : anchorReserve p a+31 ≤ ((a-p a).val : ℤ)) :
    (b-p b).val+k=(a-p a).val ∧
      ((b-p b).val : ℤ)-anchorReserve p b=
        ((a-p a).val : ℤ)-anchorReserve p a ∧
      anchorReserve p b+31 ≤ ((b-p b).val : ℤ) := by
  have hkn : k < n := by have := (a-p a).isLt; omega
  have hkv : (k : Fin n).val=k := by simp [Nat.mod_eq_of_lt hkn]
  have hback : b-p b=a-p a-(k : Fin n) := by linear_combination -hoff
  have hle : (k : Fin n) ≤ a-p a := by change (k : Fin n).val ≤ (a-p a).val; rw [hkv]; omega
  have hv : (b-p b).val=(a-p a).val-k := by
    rw [hback,Fin.coe_sub_iff_le.mpr hle,hkv]
  exact ⟨by omega,by omega,by omega⟩

/-- The remaining even obstruction has an actual multiple-fixed phase
reached from a global singleton phase at an exactly charged exchange cost.
The terminal phase is not asserted to be globally minimal. -/
theorem even_unpaid_multiple_fixed_phase (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a b : Fin n,∃ k : ℕ,GlobalMinimum p a ∧
      (fixedPositions (permutation p a)).card=1 ∧
      0 < k ∧ 2 ≤ (fixedPositions (permutation p b)).card ∧
      height p b+1=m ∧ (∀ c,height p b ≤ height p c) ∧
      inversions (displacement p b)=inversions (displacement p a)+k ∧
      anchorReserve p b=anchorReserve p a-k ∧ (k : ℤ) ≤ anchorReserve p a ∧
      (b-p b).val+k=(a-p a).val ∧
      anchorReserve p b+31 ≤ ((b-p b).val : ℤ) ∧
      NearMajorized (displacement p b) k ∧ ¬GlobalMinimum p b := by
  obtain ⟨a,ha,hh,hf,hgap,_⟩ := even_unpaid_one_fixed_cyclic_gap hn4 p m hn hunpaid
  have hmin := even_unpaid_global_minimum_height p m hn hn4 hunpaid a ha
  have hr : anchorReserve p a=(m : ℤ)*(m-1)-inversions (displacement p a) := by
    unfold anchorReserve
    have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
    have hh' : (height p a : ℤ)+1=m := by exact_mod_cast hh
    nlinarith
  rw [← hr] at hgap
  obtain ⟨b,k,hk,hbf,hbh,hboff,hbI,hbr,hkb⟩ := minimum_height_singleton_chain p a
    (by omega) hmin hf
  have hg := singleton_chain_cyclic_price p a b k hboff hbr hkb hgap
  refine ⟨a,b,k,ha,hf,hk,hbf,by omega,?_,hbI,hbr,hkb,hg.1,hg.2.2,
    near_majorized_of_exchange_allowance ha b k hbI.le,?_⟩
  · intro c
    rw [hbh]
    exact hmin c
  · intro hb
    have hle := global_minimum_exchanges hb a
    omega

#print axioms singleton_chain_cyclic_price
#print axioms even_unpaid_multiple_fixed_phase
end LX.AnchoredPhases
