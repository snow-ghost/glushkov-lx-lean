import LRX.PacketCoverage
import LRX.ReflectedRootStar

/-! Recenter and reflect reachability of the whole root packet, including
paths between its different permutation cycles. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem reaches_recenter_inverse (p : State n) (d : Fin n → ℤ) (r : Fin n)
    {a b : Fin n} (h : PrunedLift.Reaches p d a b) :
    PrunedLift.Reaches (localTarget p 0 r) (localDisplacement d r)
      ((rotation r).symm a) ((rotation r).symm b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hpath he ih =>
    apply ih.tail
    apply (service_edge_recenter p d r _ _).mpr
    simpa only [Equiv.apply_symm_apply] using he

theorem packet_cover_recenter (p : State n) (d : Fin n → ℤ) (r : Fin n)
    (hcover : PrunedLift.PacketCover p d r) :
    PrunedLift.PacketCover (localTarget p 0 r) (localDisplacement d r) 0 := by
  intro i hi
  change d (rotation r i) ≠ 0 at hi
  obtain ⟨a,j,hra,har,he,hj⟩ := hcover (rotation r i) hi
  have hz : (rotation r).symm r=0 := by
    apply (rotation r).injective
    simp [rotation,AffineLift.rotation_power_apply]
  refine ⟨(rotation r).symm a,(rotation r).symm j,?_,?_,?_,?_⟩
  · simpa only [hz] using reaches_recenter_inverse p d r hra
  · simpa only [hz] using reaches_recenter_inverse p d r har
  · apply (service_edge_recenter p d r _ _).mpr
    simpa only [Equiv.apply_symm_apply] using he
  · apply (same_cycle_recenter p r _ i).mpr
    simpa only [Equiv.apply_symm_apply] using hj

end LRX.RotationWords
namespace LRX.WordReflection
variable {n : ℕ} [NeZero n]

theorem reaches_reflected (p : State n) (d : Fin n → ℤ) {a b : Fin n}
    (h : PrunedLift.Reaches p d a b) :
    PrunedLift.Reaches (reflectedTarget p) (reflectedDisplacement d) (reflection a) (reflection b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hpath he ih => exact ih.tail ((service_edge_reflected p d _ _).mpr he)

theorem packet_cover_reflected (p : State n) (d : Fin n → ℤ) (r : Fin n)
    (hcover : PrunedLift.PacketCover p d r) :
    PrunedLift.PacketCover (reflectedTarget p) (reflectedDisplacement d) (reflection r) := by
  intro i hi
  have hdi : d (reflection i) ≠ 0 := by simpa only [reflectedDisplacement,neg_ne_zero] using hi
  obtain ⟨a,j,hra,har,he,hj⟩ := hcover (reflection i) hdi
  refine ⟨reflection a,reflection j,reaches_reflected p d hra,reaches_reflected p d har,
    (service_edge_reflected p d a j).mpr he,?_⟩
  have h := (same_cycle_reflected p j (reflection i)).mpr hj
  simpa only [reflection_twice] using h

#print axioms packet_cover_reflected
end LRX.WordReflection
