import LRX.LeftPortPrice

/-! Reflected closed services are genuine route tasks at the opposite ports,
with identical letter counts and no extra coordinate-change cost. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem rotation_reflection (r : Fin n) :
    reflection*rotation r*reflection=rotation (-r) := by
  apply Equiv.ext
  intro i
  simp only [Equiv.Perm.mul_apply, RotationWords.rotation, AffineLift.rotation_power_apply,
    Fin.cast_val_eq_self, reflection_apply]
  ring

omit [NeZero n] in
theorem mirror_increment (w : List Letter) :
    ((mirror w).map LiftedModel.increment).sum=-(w.map LiftedModel.increment).sum := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a <;> simp_all [mirror, Letter.inverse, LiftedModel.increment] <;> omega

@[simp] theorem reflected_target_twice (p : State n) :
    reflectedTarget (reflectedTarget p)=p := by
  simp only [reflectedTarget, mul_assoc, ← mul_assoc (reflection : State n) reflection,
    reflection_square, one_mul, mul_one]

def mirrorService (s : ClosedService n) : ClosedService n where
  port := -s.port
  word := mirror s.word
  target := reflectedTarget s.target
  correct := by
    rw [mirror_eval, s.correct, ← rotation_reflection]
    simp only [reflectedTarget, mul_inv_rev, reflection_inv, mul_assoc,
      ← mul_assoc (reflection : State n) reflection, reflection_square, one_mul]
  closed := by rw [mirror_increment, s.closed, neg_zero]

/-- A balanced reachable cluster supplies a closed task at the left edge of
its root. Its price uses the original, unreflected inversion count and load. -/
theorem exists_left_closed_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (r : Fin n) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (hroot : d r ≠ 0)
    (hreach : ∀ i : Fin n, localDisplacement (reflectedDisplacement d) (reflection r) i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge
        (localTarget (reflectedTarget p) 0 (reflection r))
        (localDisplacement (reflectedDisplacement d) (reflection r))) 0 i) :
    ∃ service : ClosedService n, service.port=r-1 ∧ service.target=p ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1) := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have href : AffineLift.IsLift (reflectedTarget p) 0 (reflectedDisplacement d) := by
    simpa using reflected_lift 0 hd0
  have hs (i : Fin n) : |reflectedDisplacement d i| < (n : ℤ) := by
    simpa only [reflectedDisplacement, abs_neg] using hshort (reflection i)
  have hr : reflectedDisplacement d (reflection r) ≠ 0 := by
    simpa only [reflectedDisplacement, reflection_twice, neg_ne_zero] using hroot
  obtain ⟨s, hport, htarget, hx, hlen⟩ := exists_closed_service hn (reflection r) href hs hr hreach
  rw [inversion_count_reflected 0 hd0] at hx hlen
  rw [reflected_mass, port_load_reflected] at hlen
  refine ⟨mirrorService s, ?_, ?_, ?_, ?_⟩
  · simp only [mirrorService, hport, reflection_apply]
    ring
  · simp only [mirrorService, htarget, reflected_target_twice]
  · simpa only [mirrorService, mirror_exchanges] using hx
  · simpa only [mirrorService, mirror_length] using hlen

#print axioms mirror_increment
#print axioms exists_left_closed_service
end LRX.WordReflection
