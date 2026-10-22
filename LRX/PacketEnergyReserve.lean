import LRX.PacketComplementEnergy

/-! The packet reserve H in the connected-branch arithmetic is a quantity of
the original lift. Both geometric lower bounds are derived here. -/
namespace LRX.PrunedLift
open scoped BigOperators Fin.NatCast
variable {n : ℕ} [NeZero n]

noncomputable def coreEnergy (p : State n) (d : Fin n → ℤ) : ℤ := ∑ i ∈ core p d 0, |d i|

noncomputable def coreHalfSize (p : State n) (d : Fin n → ℤ) : ℕ := (core p d 0).card/2

noncomputable def coreReserve (p : State n) (d : Fin n → ℤ) : ℤ :=
  (coreHalfSize p d : ℤ)*(n-coreHalfSize p d)-coreEnergy p d

theorem core_reserve_nonneg {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d)
    (hcover : PacketCover p d 0) (hroot : p⁻¹ 0 ≠ 0) : 0 ≤ coreReserve p d := by
  have h := core_energy_bound hd hm hcover hroot
  unfold coreReserve coreHalfSize coreEnergy
  omega

theorem core_reserve_complement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hm : AffineLift.Majorized d) (r : Fin n) (b : ℕ)
    (hr : r.val=b+1)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < r.val → ¬InCore p d 0 i) :
    (coreHalfSize p d : ℤ)*(2*(b : ℤ)-n+coreHalfSize p d) ≤ coreReserve p d := by
  have h := core_complement_energy hd hm r b hr hgap
  unfold coreReserve coreHalfSize coreEnergy
  nlinarith

#print axioms core_reserve_nonneg
#print axioms core_reserve_complement
end LRX.PrunedLift
