import LRX.LiftedReflection
import LRX.ReducedServiceRoute

/-! Left services preserve exact integer endpoints by reflection of execution. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords LiftedModel
variable {n : ℕ} [NeZero n]

theorem mirror_endpoints (w : List Letter) (r : Fin n) (d : Fin n → ℤ)
    (hend : ∀ z i, (run w (atPort r z)).position i=(i : ℤ)+d i) :
    ∀ z i, (run (mirror w) (atPort (-r) z)).position i=
      (i : ℤ)+reflectedDisplacement d i := by
  intro z i
  have h := congrArg (fun s : Configuration n => s.position i)
    (reflect_run w (atPort r (-z)))
  rw [reflect_at_port, neg_neg] at h
  change (i : ℤ)+(reflection i : ℤ)-(run w (atPort r (-z))).position (reflection i)= _ at h
  rw [hend] at h
  unfold reflectedDisplacement
  omega

def mirrorExactService (a : ExactService n) : ExactService n where
  service := mirrorService a.service
  displacement := reflectedDisplacement a.displacement
  stationary i hi := by
    change reflection (a.service.target (reflection i))=i at hi
    have h := congrArg (reflection (n := n)) hi
    rw [reflection_twice] at h
    simp only [reflectedDisplacement, a.stationary _ h, neg_zero]
  endpoint := mirror_endpoints a.service.word a.service.port a.displacement a.endpoint

@[simp] theorem reflected_displacement_twice (d : Fin n → ℤ) :
    reflectedDisplacement (reflectedDisplacement d)=d := by
  funext i
  simp only [reflectedDisplacement, reflection_twice, neg_neg]

theorem single_cycle_exact_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∃ a : ExactService n, a.service.port=r-1 ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d (r-1) := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have href : AffineLift.IsLift (reflectedTarget p) 0 (reflectedDisplacement d) := by
    simpa using reflected_lift 0 hd0
  have hc : (reflectedTarget p).IsCycle := by
    simpa only [reflectedTarget, reflection_inv] using hp.conj (g := reflection)
  have hs (i : Fin n) : |reflectedDisplacement d i| < (n : ℤ) := by
    simpa only [reflectedDisplacement, abs_neg] using hshort (reflection i)
  have hr : reflectedDisplacement d (reflection r) ≠ 0 := by
    simpa only [reflectedDisplacement, reflection_twice, neg_ne_zero] using hroot
  obtain ⟨a, ha, ht, hd', hprice⟩ := single_cycle_exact_service hn hc href hs (reflection r) hr
  refine ⟨mirrorExactService a, ?_, ?_, ?_, ?_⟩
  · simp only [mirrorExactService, mirrorService, ha, reflection_apply]
    ring
  · simp only [mirrorExactService, mirrorService, ht, reflected_target_twice]
  · simp only [mirrorExactService, hd', reflected_displacement_twice]
  · simp only [mirrorExactService, mirrorService, mirror_rotations]
    rw [hprice, reflected_mass, port_load_reflected]

#print axioms mirror_endpoints
#print axioms single_cycle_exact_left_service
end LRX.WordReflection
