import LX.SecondExcess

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- The peak is tested by a genuine phase-shifted lift, even when its
threshold is unoccupied. Its strip capacity bounds the original exchanges. -/
theorem global_rank_peak_reserve (p : State n) (a t : Fin n)
    (ha : GlobalMinimum p a) :
    rankSurplus p a t.val *
      (2*(height p a : ℤ)+rankSurplus p a t.val+1-n) ≤ anchorReserve p a := by
  classical
  let C := belowCount p a t.val
  let S := (Finset.univ.filter fun i => (cyclicOffset p a i).val < t.val)ᶜ
  have hC : C ≤ n := (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  have hcard : S.card=n-C := by
    dsimp only [S]
    rw [Finset.card_compl,Fintype.card_fin]
    rfl
  have htop : IsTopSet (displacement p a) S := by
    intro i hi j hj
    have hi' : t.val ≤ (cyclicOffset p a i).val := by simpa [S] using hi
    have hj' : (cyclicOffset p a j).val < t.val := by simpa [S] using hj
    rw [displacement_offset,displacement_offset]
    omega
  let d := phaseShift (displacement p a) S
  have hd := shift_lift (is_lift p a) S
  have hband (i : Fin n) :
      0 ≤ d i+((height p a : ℤ)+rankSurplus p a t.val) ∧
      d i+((height p a : ℤ)+rankSurplus p a t.val) < (n : ℤ) := by
    dsimp only [d,phaseShift]
    rw [hcard,Nat.cast_sub hC,displacement_offset]
    unfold rankSurplus
    change 0 ≤ _+((height p a : ℤ)+((C : ℤ)-(t.val : ℤ))) ∧ _
    have hoff := (cyclicOffset p a i).isLt
    have ht := t.isLt
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      have hi' : t.val ≤ (cyclicOffset p a i).val := by simpa [S] using hi
      omega
    · rw [ite_eq_right hi]
      have hi' : (cyclicOffset p a i).val < t.val := by simpa [S] using hi
      omega
  have hcap := shifted_lift_inversion_capacity hd
    ((height p a : ℤ)+rankSurplus p a t.val) hband
  have he := top_phase_exchange_price (is_lift p a) (global_minimum_majorized ha) S htop
  have hle : (inversions (displacement p a) : ℤ) ≤ inversions d := by
    dsimp only [d]
    rw [he]
    omega
  change (inversions d : ℤ) ≤ _ at hcap
  unfold anchorReserve
  nlinarith only [hcap,hle]

/-- Critical parity cases spend a quadratic amount of the actual reserve. -/
theorem critical_rank_peak_reserve (p : State n) (a t : Fin n)
    (ha : GlobalMinimum p a) (e : ℕ) (hn : n=2*height p a+2+e) :
    rankSurplus p a t.val*(rankSurplus p a t.val-1-e) ≤ anchorReserve p a := by
  have hh := global_rank_peak_reserve p a t ha
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2+e := by exact_mod_cast hn
  rw [hn'] at hh
  convert hh using 1
  ring

#print axioms global_rank_peak_reserve
#print axioms critical_rank_peak_reserve
end LX.AnchoredPhases
