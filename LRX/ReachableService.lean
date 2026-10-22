import LRX.ServiceSaturation

/-! Complete lifted service when the root reaches every nonzero displacement.
Reachability uses actual lifted arrow segments and target permutation cycles.
Rotation price is exact; affine reduction of X and the sharp total bound remain
separate obligations. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem complete_service_word (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (C : ServiceCertificate p d)
    (hcover : ∀ i : Fin n, d i ≠ 0 → i ∈ C.labels) :
    ∃ w : List Letter,
      eval w=p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i=(i : ℤ)+d i) ∧
      (rotations w : ℤ)=(∑ i : Fin n, |d i|)-
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) := by
  have hy (i : Fin n) : (logicalRun C.program initialLogical).coord i=
      PeriodicBuffer.contract (n : ℤ) ((i : ℤ)+d i) := by
    rw [C.coordinates i]
    by_cases hi : i ∈ C.labels
    · rw [ite_eq_left hi]
      dsimp [initialLogical, logicalDelta]
      ring
    · have hz : d i=0 := by by_contra hz; exact hi (hcover i hz)
      rw [ite_eq_right hi, hz]
      simp [initialLogical]
  have hb : (((logicalRun C.program initialLogical).buffer : ℤ)+
      d (logicalRun C.program initialLogical).buffer)%(n : ℤ)=0 := by
    have h := (hd.2 (logicalRun C.program initialLogical).buffer).eq
    simpa only [C.final_buffer, Fin.val_zero, Nat.cast_zero, add_zero, Int.zero_emod] using h
  have hhead := closed_head_of_complete_coordinates C.program hd hy
  have hm := compile_correct hn C.program (initial_matches hn) C.valid
  have hr : rotations (compile C.program)=∑ i : Fin n, (logicalDelta d i).natAbs := by
    rw [C.rotation_price]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hz : d i=0 := by by_contra hz; exact hi (hcover i hz)
    simp [logicalDelta, hz]
  refine ⟨compile C.program, completed_service_endpoint hn C.program hd C.valid hy hb,
    hm.1.trans hhead, compiled_exact_positions hn C.program hd C.valid hhead hy hb, ?_⟩
  rw [hr]
  simp only [Nat.cast_sum, Int.natCast_natAbs]
  have hn0 : 0 < (n : ℤ) := by exact_mod_cast (show 0 < n by omega)
  simpa only [logicalDelta, add_sub_cancel_left] using PeriodicBuffer.rotation_price
    (Finset.univ : Finset (Fin n)) hn0 (fun i => (i : ℤ)) (fun i => (i : ℤ)+d i)

/-- Finite saturation proves complete coverage; no recursive schedule, list of
cycles, valid-program witness, or coverage certificate is assumed as input. -/
theorem reachable_lift_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hroot : (p⁻¹) 0 ≠ 0)
    (hreach : ∀ i : Fin n, d i ≠ 0 → Relation.ReflTransGen (ServiceEdge p d) 0 i) :
    ∃ w : List Letter,
      eval w=p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i=(i : ℤ)+d i) ∧
      (rotations w : ℤ)=(∑ i : Fin n, |d i|)-
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) := by
  obtain ⟨C, hC⟩ := exists_saturated_service hd hroot
  exact complete_service_word hn hd C (fun i hi => saturated_reachable C hC (hreach i hi))

omit [NeZero n] in
/-- Short lifts cannot hide nonzero winding in a fixed singleton cycle. -/
theorem fixed_short_displacement {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i : Fin n)
    (hshort : |d i| < (n : ℤ)) (hfixed : (p⁻¹) i=i) : d i=0 := by
  have hm : Int.ModEq (n : ℤ) (d i) 0 := by
    have h := (hd.2 i).sub_right (i : ℤ)
    have hf : p.symm i=i := hfixed
    simpa only [hf, add_zero, add_sub_cancel_left, sub_self] using h
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (Int.modEq_zero_iff_dvd.mp hm)
  have hh : ((d i).natAbs : ℤ) < ((n : ℤ).natAbs : ℤ) := by
    simpa only [Int.natCast_natAbs, abs_of_nonneg (show (0 : ℤ) ≤ n by positivity)] using hshort
  exact_mod_cast hh

/-- In the short-lift domain it is enough to reach nontrivial cycles. The
singleton condition from the corrected source is derived, not assumed away. -/
theorem short_reachable_lift_service (hn : 2 ≤ n) {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, |d i| < (n : ℤ))
    (hroot : d 0 ≠ 0)
    (hreach : ∀ i : Fin n, (p⁻¹) i ≠ i → Relation.ReflTransGen (ServiceEdge p d) 0 i) :
    ∃ w : List Letter,
      eval w=p ∧
      (LiftedModel.run w (LiftedModel.initial (n := n))).cursor=0 ∧
      (∀ i, (LiftedModel.run w (LiftedModel.initial (n := n))).position i=(i : ℤ)+d i) ∧
      (rotations w : ℤ)=(∑ i : Fin n, |d i|)-
        ∑ i : Fin n, PeriodicBuffer.edgePassages (n : ℤ) (i : ℤ) ((i : ℤ)+d i) := by
  have hm (i : Fin n) (hi : d i ≠ 0) : (p⁻¹) i ≠ i :=
    fun hf => hi (fixed_short_displacement hd i (hshort i) hf)
  exact reachable_lift_service hn hd (hm 0 hroot) (fun i hi => hreach i (hm i hi))

#print axioms complete_service_word
#print axioms reachable_lift_service
#print axioms short_reachable_lift_service
end LRX.BufferProgram
