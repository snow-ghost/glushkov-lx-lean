import LRX.GapFamilySquareCap

/-! The square envelope cap is derived from the original majorized lift and
the actual partition of its source packet. -/
namespace LRX.FiniteGaps
open scoped BigOperators Fin.NatCast

theorem floor_square_identity (n : ℕ) : 4*((n : ℤ)^2/4)=(n : ℤ)^2-(n%2 : ℕ) := by
  have hp : n%2=0 ∨ n%2=1 := by omega
  have hn : (n : ℤ)=2*(n/2 : ℕ)+(n%2 : ℕ) := by omega
  have hsq : ((n%2 : ℕ) : ℤ)^2=(n%2 : ℕ) := by rcases hp with h | h <;> simp [h]
  let q : ℤ := (n/2 : ℕ)*((n/2 : ℕ)+(n%2 : ℕ))
  have he : (n : ℤ)^2=4*q+(n%2 : ℕ) := by
    rw [hn]
    dsimp [q]
    push_cast at hsq ⊢
    nlinarith
  omega

variable {n : ℕ} [NeZero n]

theorem complement_reserve_identity (p : State n) (d : Fin n → ℤ) :
    4*complementReserve p d=
      (((n-(PrunedLift.core p d 0).card : ℕ) : ℤ)+((PrunedLift.core p d 0).card%2 : ℕ))^2-(n%2 : ℕ) := by
  have hcard : (PrunedLift.core p d 0).card ≤ n := by simpa using Finset.card_le_univ (PrunedLift.core p d 0)
  have he : ((n-(PrunedLift.core p d 0).card : ℕ) : ℤ)+((PrunedLift.core p d 0).card%2 : ℕ)=
      (n : ℤ)-2*PrunedLift.coreHalfSize p d := by unfold PrunedLift.coreHalfSize; omega
  rw [he]
  have hf := floor_square_identity n
  unfold complementReserve
  nlinarith

theorem square_envelope_cap {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) :
    2*squareEnvelope p d ≤ (PrunedLift.coreHalfSize p d : ℤ)^2+1 := by
  classical
  have hcard : (PrunedLift.core p d 0).card ≤ n := by simpa using Finset.card_le_univ (PrunedLift.core p d 0)
  apply family_square_cap (internalStarts p d) (fun a => (size (PrunedLift.core p d 0) a : ℤ))
    (n : ℤ) (PrunedLift.coreHalfSize p d : ℤ) ((PrunedLift.core p d 0).card%2 : ℕ)
    ((n-(PrunedLift.core p d 0).card : ℕ) : ℤ) (n%2 : ℕ) (complementReserve p d) (PrunedLift.coreReserve p d)
    (by positivity) (by positivity) (by omega)
    (by unfold PrunedLift.coreHalfSize; omega) (by omega)
    (complement_reserve_identity p d) (PrunedLift.core_reserve_nonneg hd hm hcover hroot)
  · intro a ha
    positivity
  · have h := internal_sizes_total p d
    exact_mod_cast h
  · intro a ha
    have h := internal_size_bound hd hm a (Finset.mem_filter.mp ha).2
    omega
  · intro a ha
    exact core_reserve_complement hd hm a

theorem selected_gap_quadratic_envelope {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PrunedLift.PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0)
    (a : Fin n) (ha : a ∈ internalStarts p d) (K : ℕ)
    (hK : 2*gapEnergy p d a+(K : ℤ)^2 ≤ (size (PrunedLift.core p d 0) a : ℤ)^2) :
    2*(K : ℤ)^2 ≤ (PrunedLift.coreHalfSize p d : ℤ)^2+1+4*epsilon d := by
  have hlocal := localized_gap_energy hd hcover hroot a ha K hK
  have hcap := square_envelope_cap hd hm hcover hroot
  omega

#print axioms square_envelope_cap
#print axioms selected_gap_quadratic_envelope
end LRX.FiniteGaps
