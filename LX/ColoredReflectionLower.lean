import LX.AntipodeCandidates

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def oppositeColorInversions (ρ : State n) (χ : Fin n → Bool) : ℕ :=
  ∑ i : Fin n,∑ j : Fin n,
    if i < j ∧ ρ j < ρ i ∧ χ i ≠ χ j then 1 else 0

/-- A reversed rank pair with opposite winding parity contributes an
inversion instead of removing one. Keeping those pairs improves the
coarse reflection lower bound by two per pair. -/
theorem reflection_opposite_pairs (d : Fin n → ℤ) (ρ : State n)
    (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(ρ i : ℤ)+(n : ℤ)*k i) :
    sameColorPairs (fun i => decide (k i % 2=0))+
      2*oppositeColorInversions ρ (fun i => decide (k i % 2=0)) ≤
        inversions d+LRX.FiniteCuts.inversionNumber ρ := by
  let χ : Fin n → Bool := fun i => decide (k i % 2=0)
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hp (i j : Fin n) :
      (if i < j ∧ χ i=χ j then 1 else 0)+
      2*(if i < j ∧ ρ j < ρ i ∧ χ i ≠ χ j then 1 else 0) ≤
      (if i < j then ((targets d j-targets d i)/(n : ℤ)).natAbs else 0)+
      (if i.val < j.val ∧ (ρ j).val < (ρ i).val then 1 else 0 : ℕ) := by
    by_cases hij : i < j
    · have hijv : i.val < j.val := hij
      simp only [hij,hijv,true_and,ite_true]
      by_cases hr : ρ j < ρ i
      · have hrv : (ρ j).val < (ρ i).val := hr
        simp only [hr,hrv,true_and,ite_true]
        by_cases hχ : χ i=χ j
        · simp [hχ]
        · simp only [ite_eq_right hχ,ite_eq_left hχ,zero_add,mul_one]
          have hq : (targets d j-targets d i)/(n : ℤ)=k j-k i := by
            rw [hF j,hF i]
            have hlt : (ρ j : ℤ) < ρ i := by exact_mod_cast hrv
            have hi := (ρ i).isLt
            have hj := (ρ j).isLt
            apply LRX.PeriodicBuffer.quotient_eq_of_bounds hn <;> nlinarith
          have hk : k i ≠ k j := by intro hh; apply hχ; simp only [χ,hh]
          have hpos : 0 < (k j-k i).natAbs := Int.natAbs_pos.mpr (by omega)
          rw [hq]
          omega
      · have hrv : ¬(ρ j).val < (ρ i).val := hr
        simp only [hr,hrv,false_and,ite_false,mul_zero,add_zero]
        by_cases hχ : χ i=χ j
        · rw [ite_eq_left hχ]
          have hne : ρ i ≠ ρ j := fun hh => (ne_of_lt hij) (ρ.injective hh)
          have hlt : (ρ i : ℤ) < ρ j := by
            have hvals : (ρ i).val ≠ (ρ j).val := fun hh => hne (Fin.ext hh)
            omega
          have hq : (targets d j-targets d i)/(n : ℤ)=k j-k i-1 := by
            rw [hF j,hF i]
            have hi := (ρ i).isLt
            have hj := (ρ j).isLt
            apply LRX.PeriodicBuffer.quotient_eq_of_bounds hn <;> nlinarith
          have hcolor : (k i % 2=0) ↔ (k j % 2=0) := by
            simpa only [χ,decide_eq_decide] using hχ
          have hmod : k i % 2=k j % 2 := by omega
          rw [hq]
          exact Int.natAbs_pos.mpr (by omega)
        · rw [ite_eq_right hχ]; exact Nat.zero_le _
    · have hijv : ¬i.val < j.val := hij
      simp [hij,hijv]
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hp i j))
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,sameColorPairs,oppositeColorInversions,
    inversions,LRX.LiftedModel.inversionCount,LRX.FiniteCuts.inversionNumber,χ] using hs

end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

theorem odd_opposite_pairs_count (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (χ : Fin n → Bool) :
    oppositeColorInversions (oddRank m hm hn) χ=
      (Finset.univ.filter fun j : Fin n => 2 < j.val ∧ j.val ≤ m+1 ∧ χ 2 ≠ χ j).card := by
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hp (i j : Fin n) :
      (i < j ∧ oddRank m hm hn j < oddRank m hm hn i) ↔ i=2 ∧ 2 < j.val ∧ j.val ≤ m+1 := by
    have hea : i=2 ↔ i.val=2 := by rw [Fin.ext_iff,hv2]
    rw [hea]
    change (i.val < j.val ∧ oddRankValue m j.val < oddRankValue m i.val) ↔
      i.val=2 ∧ 2 < j.val ∧ j.val ≤ m+1
    unfold oddRankValue
    split_ifs <;> omega
  unfold oppositeColorInversions
  simp_rw [← and_assoc,hp]
  rw [Finset.sum_comm]
  simp only [and_assoc,ite_and,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [← ite_and,Finset.sum_boole]
  rfl

theorem odd_colored_inversions_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    (d : Fin n → ℤ) (C : ℤ) (k : Fin n → ℤ)
    (hF : ∀ i,targets d i=C-(oddRank m hm hn i : ℤ)+(n : ℤ)*k i) :
    m^2+2*(Finset.univ.filter fun j : Fin n =>
      2 < j.val ∧ j.val ≤ m+1 ∧ decide (k 2 % 2=0) ≠ decide (k j % 2=0)).card ≤
        inversions d+(m-1) := by
  have hh := reflection_opposite_pairs d (oddRank m hm hn) C k hF
  rw [odd_rank_inversions m hm hn,odd_opposite_pairs_count m hm hn] at hh
  have hp := odd_same_color_pairs_lower (fun i => decide (k i % 2=0)) m hn
  omega

#print axioms odd_colored_inversions_lower
end LX.Antipode
