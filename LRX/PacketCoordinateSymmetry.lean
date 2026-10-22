import LRX.PacketPortSymmetry
import LRX.BalancedSubsetEnergy

/-! Coordinate changes preserve majorization and the entire strongly
connected root packet. -/
namespace LRX.AffineLift
open scoped BigOperators
variable {n : ℕ}

theorem majorized_comp {d : Fin n → ℤ} (hm : Majorized d) (e : State n) :
    Majorized (fun i => d (e i)) := by
  intro S
  have h := hm (S.image e)
  rw [Finset.card_image_of_injective _ e.injective,
    Finset.sum_image (fun i _ j _ hij => e.injective hij)] at h
  exact h
end LRX.AffineLift

namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem majorized_recenter {d : Fin n → ℤ} (hm : AffineLift.Majorized d) (r : Fin n) :
    AffineLift.Majorized (localDisplacement d r) :=
  AffineLift.majorized_comp hm (rotation r)

theorem reaches_recenter (p : State n) (d : Fin n → ℤ) (r : Fin n) {i j : Fin n} :
    PrunedLift.Reaches (localTarget p 0 r) (localDisplacement d r) i j ↔
      PrunedLift.Reaches p d (rotation r i) (rotation r j) := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp he ih => exact ih.tail ((service_edge_recenter p d r _ _).mp he)
  · intro h
    simpa only [Equiv.symm_apply_apply] using reaches_recenter_inverse p d r h

theorem core_recenter (p : State n) (d : Fin n → ℤ) (r i : Fin n) :
    PrunedLift.InCore (localTarget p 0 r) (localDisplacement d r) 0 i ↔
      PrunedLift.InCore p d r (i+r) := by
  unfold PrunedLift.InCore
  rw [reaches_recenter,reaches_recenter]
  simp [rotation,AffineLift.rotation_power_apply]

theorem shifted_word_target (p : State n) (r start finish : Fin n) :
    (rotation (start-r))⁻¹*localTarget p 0 r*rotation (finish-r)=
      (rotation start)⁻¹*p*rotation finish := by
  rw [rotation_sub,rotation_sub,local_target_zero]
  group
end LRX.RotationWords

namespace LRX.WordReflection
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem majorized_reflected {d : Fin n → ℤ} (hd : ∑ i, d i=0) (hm : AffineLift.Majorized d) :
    AffineLift.Majorized (reflectedDisplacement d) :=
  AffineLift.majorized_comp (AffineLift.majorized_neg hd hm) reflection
end LRX.WordReflection

#print axioms LRX.RotationWords.core_recenter
#print axioms LRX.RotationWords.shifted_word_target
#print axioms LRX.WordReflection.majorized_reflected
