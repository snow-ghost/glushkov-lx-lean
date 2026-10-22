import LRX.WordReflection

/-! Reflection transports balanced phase lifts and preserves their affine price. -/
namespace LRX.WordReflection
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

@[simp] theorem reflection_inv : (reflection : State n)⁻¹=reflection := rfl

def reflectedTarget (p : State n) : State n := reflection*p*reflection

def reflectedDisplacement (d : Fin n → ℤ) (i : Fin n) : ℤ := -d (reflection i)

theorem reflected_target_inverse (p : State n) (i : Fin n) :
    (reflectedTarget p).symm i=reflection (p.symm (reflection i)) := by
  change (reflectedTarget p)⁻¹ i= _
  simp only [reflectedTarget, mul_inv_rev, reflection_inv, Equiv.Perm.mul_apply]
  rfl

theorem reflected_lift {p : State n} {d : Fin n → ℤ} (c : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    AffineLift.IsLift (reflectedTarget p) ((-c : Fin n) : ℤ) (reflectedDisplacement d) := by
  constructor
  · unfold reflectedDisplacement
    rw [Finset.sum_neg_distrib, Equiv.sum_comp reflection d, hd.1, neg_zero]
  · intro i
    apply (LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [Int.cast_add, Int.cast_natCast, Fin.cast_val_eq_self,
      reflected_target_inverse, reflectedDisplacement, Int.cast_neg, reflection_apply]
    have h := AffineLift.lift_residue hd (reflection i)
    simp only [Int.cast_natCast, Fin.cast_val_eq_self, reflection_apply] at h
    linear_combination -h

theorem reflected_mass (d : Fin n → ℤ) :
    (∑ i : Fin n, |reflectedDisplacement d i|)=∑ i : Fin n, |d i| := by
  simp only [reflectedDisplacement, abs_neg]
  exact Equiv.sum_comp reflection (fun i => |d i|)

theorem crossing_reflected (d : Fin n → ℤ) (i j : Fin n) :
    AffineLift.crossing (reflectedDisplacement d) i j=
      AffineLift.crossing d (reflection j) (reflection i) := by
  have hsub : reflection i-reflection j=j-i := by simp only [reflection_apply]; abel
  simp only [AffineLift.crossing, AffineLift.crossingNumerator, reflectedDisplacement, hsub]
  congr 2
  ring

theorem inversion_count_reflected {p : State n} {d : Fin n → ℤ} (c : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+reflectedDisplacement d i)=
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) := by
  have h1 := RotationWords.twice_inversion_count (reflected_lift c hd)
  have h2 := RotationWords.twice_inversion_count hd
  have he : (∑ i : Fin n, ∑ j : Fin n,
      (AffineLift.crossing (reflectedDisplacement d) i j).natAbs)=
      ∑ i : Fin n, ∑ j : Fin n, (AffineLift.crossing d i j).natAbs := by
    simp_rw [crossing_reflected]
    rw [Finset.sum_comm]
    have hi (i : Fin n) : (∑ j : Fin n,
        (AffineLift.crossing d (reflection i) (reflection j)).natAbs)=
        ∑ j : Fin n, (AffineLift.crossing d (reflection i) j).natAbs :=
      Equiv.sum_comp reflection (fun j => (AffineLift.crossing d (reflection i) j).natAbs)
    simp_rw [hi]
    exact Equiv.sum_comp reflection (fun i => ∑ j : Fin n, (AffineLift.crossing d i j).natAbs)
  rw [he] at h1
  omega

#print axioms reflected_lift
#print axioms inversion_count_reflected
end LRX.WordReflection
