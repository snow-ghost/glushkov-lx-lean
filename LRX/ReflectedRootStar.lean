import LRX.RecenteredRootStar
import LRX.ReflectedExactService

/-! Reflection preserves the geometric root-star condition, so the left
incident service is available for any balanced short root star. -/
namespace LRX.BufferProgram

theorem touches_neg (N a d b : ℤ) : Touches N a d b ↔ Touches N (-a) (-d) (-b) := by
  have hm : min 0 (-d)= -max 0 d := by omega
  have hx : max 0 (-d)= -min 0 d := by omega
  rw [touches_relative,touches_relative,hm,hx]
  constructor <;> rintro ⟨k,hl,hh⟩ <;> refine ⟨-k,?_,?_⟩ <;> simp only [neg_mul] <;> omega

end LRX.BufferProgram
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem same_cycle_reflected (p : State n) (i j : Fin n) :
    ((reflectedTarget p)⁻¹).SameCycle (reflection i) (reflection j) ↔ (p⁻¹).SameCycle i j := by
  have he : (reflectedTarget p)⁻¹=reflection*p⁻¹*(reflection (n := n))⁻¹ := by
    simp [reflectedTarget,mul_inv_rev,reflection_inv,mul_assoc]
  rw [he,Equiv.Perm.sameCycle_conj]
  simp only [reflection_inv,reflection_twice]

theorem moving_reflected (p : State n) (i : Fin n) :
    (reflectedTarget p)⁻¹ (reflection i) ≠ reflection i ↔ p⁻¹ i ≠ i := by
  simp only [reflectedTarget,mul_inv_rev,reflection_inv,Equiv.Perm.mul_apply,reflection_twice]
  exact not_congr (reflection (n := n)).injective.eq_iff

theorem reflection_difference_modEq (i j : Fin n) :
    Int.ModEq (n : ℤ) ((reflection j : ℤ)-(reflection i : ℤ)) (-(j : ℤ)-(-(i : ℤ))) := by
  apply (LiftedModel.cast_eq_iff_modEq _ _).mp
  simp only [Int.cast_sub,Int.cast_neg,Int.cast_natCast,Fin.cast_val_eq_self,reflection_apply]
  ring

theorem touches_reflected (d : Fin n → ℤ) (i j : Fin n) :
    BufferProgram.Touches (n : ℤ) (reflection i : ℤ) (reflectedDisplacement d (reflection i)) (reflection j : ℤ) ↔
      BufferProgram.Touches (n : ℤ) (i : ℤ) (d i) (j : ℤ) := by
  simp only [reflectedDisplacement,reflection_twice]
  exact (BufferProgram.touches_modEq_iff (reflection_difference_modEq i j)).trans
    (BufferProgram.touches_neg (n : ℤ) (i : ℤ) (d i) (j : ℤ)).symm

theorem service_edge_reflected (p : State n) (d : Fin n → ℤ) (i j : Fin n) :
    BufferProgram.ServiceEdge (reflectedTarget p) (reflectedDisplacement d) (reflection i) (reflection j) ↔
      BufferProgram.ServiceEdge p d i j := by
  change (((reflectedTarget p)⁻¹).SameCycle (reflection i) (reflection j) ∨
    ((reflectedTarget p)⁻¹ (reflection j) ≠ reflection j ∧
      BufferProgram.Touches (n : ℤ) (reflection i : ℤ) (reflectedDisplacement d (reflection i)) (reflection j : ℤ))) ↔ _
  rw [same_cycle_reflected,moving_reflected,touches_reflected]
  rfl

theorem root_star_reflected (p : State n) (d : Fin n → ℤ) (r : Fin n)
    (hstar : PrunedLift.RootStar p d r) :
    PrunedLift.RootStar (reflectedTarget p) (reflectedDisplacement d) (reflection r) := by
  intro i hi
  have hdi : d (reflection i) ≠ 0 := by simpa only [reflectedDisplacement,neg_ne_zero] using hi
  obtain ⟨a,j,ha,he,hj⟩ := hstar (reflection i) hdi
  refine ⟨reflection a,reflection j,(same_cycle_reflected p r a).mpr ha,
    (service_edge_reflected p d a j).mpr he,?_⟩
  have h := (same_cycle_reflected p j (reflection i)).mpr hj
  simpa only [reflection_twice] using h

theorem root_star_exact_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hroot : d r ≠ 0) (hstar : PrunedLift.RootStar p d r) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d (r-1) := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have href : AffineLift.IsLift (reflectedTarget p) 0 (reflectedDisplacement d) := by
    simpa using reflected_lift 0 hd0
  have hs (i : Fin n) : |reflectedDisplacement d i| < (n : ℤ) := by
    simpa only [reflectedDisplacement,abs_neg] using hshort (reflection i)
  have hr : reflectedDisplacement d (reflection r) ≠ 0 := by
    simpa only [reflectedDisplacement,reflection_twice,neg_ne_zero] using hroot
  obtain ⟨a,ha,ht,hd',hprice⟩ := root_star_exact_service hn href hs (reflection r) hr
    (root_star_reflected p d r hstar)
  refine ⟨mirrorExactService a,?_,?_,?_,?_⟩
  · simp only [mirrorExactService,mirrorService,ha,reflection_apply]; ring
  · simp only [mirrorExactService,mirrorService,ht,reflected_target_twice]
  · simp only [mirrorExactService,hd',reflected_displacement_twice]
  · simp only [mirrorExactService,mirrorService,mirror_rotations]
    rw [hprice,reflected_mass,port_load_reflected]

#print axioms service_edge_reflected
#print axioms root_star_reflected
#print axioms root_star_exact_left_service
end LRX.WordReflection
