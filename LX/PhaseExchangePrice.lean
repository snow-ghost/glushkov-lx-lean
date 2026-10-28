import LX.ScanInversions
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- Changing a phase alters each signed crossing by the difference of the
selected endpoint indicators. -/
theorem phase_shift_crossing (d : Fin n → ℤ) (S : Finset (Fin n)) (i j : Fin n) :
    crossing (phaseShift d S) i j=crossing d i j-
      (if i ∈ S then (1 : ℤ) else 0)+(if j ∈ S then (1 : ℤ) else 0) := by
  have he : crossingNumerator (phaseShift d S) i j=crossingNumerator d i j+
      ((if i ∈ S then (1 : ℤ) else 0)-(if j ∈ S then (1 : ℤ) else 0))*(n : ℤ) := by
    unfold crossingNumerator phaseShift
    split_ifs <;> ring
  rw [crossing,he,Int.add_mul_ediv_right _ _ (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)]
  unfold crossing
  ring

theorem ordered_crossing_bounds (d : Fin n → ℤ) (i j : Fin n)
    (horder : d j ≤ d i) (hwidth : d i-d j < (n : ℤ)) :
    0 ≤ crossing d i j ∧ crossing d i j ≤ 1 := by
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hv := (j-i).isLt
  have hlo : -(n : ℤ) ≤ crossingNumerator d i j := by
    unfold crossingNumerator
    omega
  have hhi : crossingNumerator d i j < (n : ℤ) := by
    unfold crossingNumerator
    omega
  have hqlo := (Int.le_ediv_iff_mul_le hn).mpr (show (-1 : ℤ)*n ≤ crossingNumerator d i j by omega)
  have hqhi := (Int.ediv_lt_iff_lt_mul hn).mpr (show crossingNumerator d i j < (1 : ℤ)*n by omega)
  unfold crossing
  omega

/-- Exact exchange-price change when a top set of a strict-width lift is
wrapped through the phase seam. Ties may be selected individually. -/
theorem top_phase_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (S : Finset (Fin n))
    (hwidth : ∀ i j, d i-d j < (n : ℤ))
    (htop : ∀ i ∈ S, ∀ j ∉ S, d j ≤ d i) :
    (inversions (phaseShift d S) : ℤ)-inversions d=
      (S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i := by
  let χ := fun i : Fin n => if i ∈ S then (1 : ℤ) else 0
  have hχ : (∑ i : Fin n,χ i)=(S.card : ℤ) := by simp [χ]
  have hpoint (i j : Fin n) :
      |crossing (phaseShift d S) i j|-|crossing d i j|=
        χ i+χ j-2*(χ i*χ j)-2*(χ i*crossing d i j)+2*(χ j*crossing d i j) := by
    rw [phase_shift_crossing]
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · simp [χ,hi,hj]
    · have hb := ordered_crossing_bounds d i j (htop i hi j hj) (hwidth i j)
      have hc : crossing d i j=0 ∨ crossing d i j=1 := by omega
      rcases hc with hc | hc <;> simp [χ,hi,hj,hc]
    · have hb := ordered_crossing_bounds d j i (htop j hj i hi) (hwidth j i)
      have hanti := crossing_antisymm hd i j
      have hc : crossing d i j=0 ∨ crossing d i j= -1 := by omega
      rcases hc with hc | hc <;> simp [χ,hi,hj,hc]
    · simp [χ,hi,hj]
  have h1 : (∑ i : Fin n, ∑ _j : Fin n, χ i)=(n : ℤ)*S.card := by
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.mul_sum,hχ]
  have h2 : (∑ _i : Fin n, ∑ j : Fin n, χ j)=(n : ℤ)*S.card := by simp [hχ]
  have h3 : (∑ i : Fin n, ∑ j : Fin n, χ i*χ j)=(S.card : ℤ)^2 := by
    simp_rw [← Finset.mul_sum,hχ]
    rw [← Finset.sum_mul,hχ]
    ring
  have h4 : (∑ i : Fin n, ∑ j : Fin n, χ i*crossing d i j)=∑ i ∈ S,d i := by
    simp_rw [← Finset.mul_sum,crossing_row_sum hd]
    simp [χ,Finset.sum_filter]
  have h5 : (∑ i : Fin n, ∑ j : Fin n, χ j*crossing d i j)= -(∑ i ∈ S,d i) := by
    rw [Finset.sum_comm]
    have he : (∑ j : Fin n, ∑ i : Fin n, χ j*crossing d i j)=
        ∑ j : Fin n, ∑ i : Fin n, -(χ j*crossing d j i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      rw [crossing_antisymm hd i j]
      ring
    rw [he]
    simp only [Finset.sum_neg_distrib]
    exact congrArg Neg.neg h4
  have htwo (f : Fin n → Fin n → ℤ) : (∑ i : Fin n, ∑ j : Fin n, 2*f i j)=
      2*(∑ i : Fin n, ∑ j : Fin n, f i j) := by simp_rw [← Finset.mul_sum]
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (|crossing (phaseShift d S) i j|-|crossing d i j|))=
      2*((S.card : ℤ)*((n : ℤ)-S.card)-2*∑ i ∈ S,d i) := by
    simp only [hpoint,Finset.sum_add_distrib,Finset.sum_sub_distrib]
    rw [htwo,htwo,htwo,h1,h2,h3,h4,h5]
    ring
  have hold := LX.Core.RotationWords.twice_inversion_count hd
  have hnew := LX.Core.RotationWords.twice_inversion_count (shift_lift hd S)
  have hold' : 2*(inversions d : ℤ)=∑ i : Fin n, ∑ j : Fin n, |crossing d i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)=_
    have hc := congrArg (fun k : ℕ => (k : ℤ)) hold
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hc
  have hnew' : 2*(inversions (phaseShift d S) : ℤ)=
      ∑ i : Fin n, ∑ j : Fin n, |crossing (phaseShift d S) i j| := by
    change 2*(LX.Core.LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+phaseShift d S i) : ℤ)=_
    have hc := congrArg (fun k : ℕ => (k : ℤ)) hnew
    simpa only [inversions,targets,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sum,Int.natCast_natAbs] using hc
  simp only [Finset.sum_sub_distrib] at hsum
  rw [← hold',← hnew'] at hsum
  omega

/-- The energy difference gives the exact exchange difference for the phase
move, rather than a heuristic comparison of different sorting problems. -/
theorem top_phase_energy_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (S : Finset (Fin n))
    (hwidth : ∀ i j, d i-d j < (n : ℤ))
    (htop : ∀ i ∈ S, ∀ j ∉ S, d j ≤ d i) :
    (energy (phaseShift d S) : ℤ)-(n : ℤ)*inversions (phaseShift d S)=
      (energy d : ℤ)-(n : ℤ)*inversions d := by
  have he := shift_energy d S hd.1
  have hx := top_phase_inversions hd S hwidth htop
  rw [← hx] at he
  nlinarith

#print axioms top_phase_inversions
#print axioms top_phase_energy_inversions
end LX.AffineScan
