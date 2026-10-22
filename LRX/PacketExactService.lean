import LRX.PacketPortSymmetry

/-! Both incident exact services for a balanced root packet with several cycles. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem packet_exact_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hroot : d r ≠ 0) (hcover : PrunedLift.PacketCover p d r) :
    ∃ a : ExactService n, a.service.port=r ∧ a.service.target=p ∧ a.displacement=d ∧
      (BufferProgram.rotations a.service.word : ℤ)=
        (∑ i : Fin n, |d i|)-portLoad d r := by
  apply exists_exact_service hn r hd hshort hroot
  intro i hi
  exact PrunedLift.packet_cover_reaches _ _ _ (packet_cover_recenter p d r hcover) i hi

#print axioms packet_exact_service
end LRX.RotationWords
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem packet_exact_left_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ)) (r : Fin n)
    (hroot : d r ≠ 0) (hstar : PrunedLift.PacketCover p d r) :
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
  obtain ⟨a,ha,ht,hd',hprice⟩ := packet_exact_service hn href hs (reflection r) hr
    (packet_cover_reflected p d r hstar)
  refine ⟨mirrorExactService a,?_,?_,?_,?_⟩
  · simp only [mirrorExactService,mirrorService,ha,reflection_apply]; ring
  · simp only [mirrorExactService,mirrorService,ht,reflected_target_twice]
  · simp only [mirrorExactService,hd',reflected_displacement_twice]
  · simp only [mirrorExactService,mirrorService,mirror_rotations]
    rw [hprice,reflected_mass,port_load_reflected]

#print axioms packet_exact_left_service
end LRX.WordReflection
