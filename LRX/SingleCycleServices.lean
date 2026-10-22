import LRX.ReflectedClosedService

/-! Reachability for a single nontrivial cycle is derived from cycle structure.
Both incident-port services are consequently available without a routing premise. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem cycle_root_reaches {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∀ i : Fin n, localDisplacement d r i ≠ 0 →
      Relation.ReflTransGen (BufferProgram.ServiceEdge (localTarget p 0 r)
        (localDisplacement d r)) 0 i := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have hlift := recentered_lift 0 r hd0
  have hc : (localTarget p 0 r).IsCycle := by
    rw [local_target_zero]
    simpa only [inv_inv] using hp.conj (g := (rotation r)⁻¹)
  have hm (i : Fin n) (hi : localDisplacement d r i ≠ 0) :
      (localTarget p 0 r)⁻¹ i ≠ i := by
    intro hf
    exact hi (BufferProgram.fixed_short_displacement hlift i (hshort _) hf)
  have hz : (localTarget p 0 r)⁻¹ 0 ≠ 0 := by
    apply hm
    simpa only [local_displacement_zero] using hroot
  intro i hi
  exact Relation.ReflTransGen.single (Or.inl (hc.inv.sameCycle hz (hm i hi)))

theorem single_cycle_right_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∃ service : ClosedService n, service.port=r ∧ service.target=p ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d r :=
  exists_closed_service hn r hd hshort hroot (cycle_root_reaches hp hd hshort r hroot)

theorem single_cycle_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hp : p.IsCycle) (hd : AffineLift.IsLift p 0 d)
    (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n) (hroot : d r ≠ 0) :
    ∃ service : ClosedService n, service.port=r-1 ∧ service.target=p ∧
      BufferProgram.exchanges service.word=LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) ∧
      (service.word.length : ℤ)=
        (LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) : ℤ)+
        (∑ i : Fin n, |d i|)-portLoad d (r-1) := by
  have hd0 : AffineLift.IsLift p ((0 : Fin n) : ℤ) d := by simpa using hd
  have href : AffineLift.IsLift (WordReflection.reflectedTarget p) 0
      (WordReflection.reflectedDisplacement d) := by
    simpa using WordReflection.reflected_lift 0 hd0
  have hc : (WordReflection.reflectedTarget p).IsCycle := by
    simpa only [WordReflection.reflectedTarget, WordReflection.reflection_inv] using
      hp.conj (g := WordReflection.reflection)
  have hs (i : Fin n) : |WordReflection.reflectedDisplacement d i| < (n : ℤ) := by
    simpa only [WordReflection.reflectedDisplacement, abs_neg] using hshort (WordReflection.reflection i)
  have hr : WordReflection.reflectedDisplacement d (WordReflection.reflection r) ≠ 0 := by
    simpa only [WordReflection.reflectedDisplacement, WordReflection.reflection_twice, neg_ne_zero] using hroot
  exact WordReflection.exists_left_closed_service hn r hd hshort hroot
    (cycle_root_reaches hc href hs (WordReflection.reflection r) hr)

#print axioms cycle_root_reaches
#print axioms single_cycle_right_service
#print axioms single_cycle_left_service
end LRX.RotationWords
