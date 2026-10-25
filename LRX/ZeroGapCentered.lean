import LRX.RecenteredLift
import LRX.ZeroGapPair
import Mathlib

/-! Recenter the zero-gap pair and derive the required endpoint inequalities
from injectivity of the actual target permutation. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem centered_pair (d : Fin n → ℤ) (hd : ∑ i, d i=0) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n, 0 < RotationWords.localDisplacement d u 0 ∧
      RotationWords.localDisplacement d u v < 0 ∧ 0 < v.val ∧
      ∀ j, 0 < j.val → j.val < v.val → RotationWords.localDisplacement d u j=0 := by
  obtain ⟨u,w,hu,hw,hdist,hgap⟩ := exists_zero_gap d hd hne
  refine ⟨u,w-u,?_,?_,hdist,?_⟩
  · simpa only [RotationWords.local_displacement_zero] using hu
  · simpa [RotationWords.localDisplacement,AffineLift.rotation_power_apply] using hw
  · intro j hj hj'
    have he : distance u (j+u)=j.val := by simp [distance]
    have hz := hgap (j+u) (by omega) (by rw [he]; exact hj')
    simpa only [RotationWords.localDisplacement,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using hz

theorem fixed_source_of_fixed_target {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (i j : Fin n) (hj : d j=0) (he : p.symm i=j) : i=j := by
  have h := AffineLift.lift_residue hd j
  simp only [hj,Int.cast_zero,add_zero] at h
  exact p.symm.injective (he.trans h)

theorem positive_endpoint_length {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (v : Fin n) (hpos : 0 < d 0)
    (hgap : ∀ j : Fin n, 0 < j.val → j.val < v.val → d j=0) : (v : ℤ) ≤ d 0 := by
  by_contra h
  have hN : d 0 < (n : ℤ) := by have := v.isLt; omega
  let j : Fin n := ⟨(d 0).toNat,by omega⟩
  have hjval : (j : ℤ)=d 0 := by dsimp [j]; omega
  have hj := hgap j (by omega) (by omega)
  have he : p.symm 0=j := by
    have hres := AffineLift.lift_residue hd (0 : Fin n)
    have hc : (d 0 : Fin n)=j := by rw [← hjval]; simp
    simpa only [zero_add,Int.cast_zero,add_zero,hc] using hres.symm
  have heq := fixed_source_of_fixed_target hd 0 j hj he
  have hz := congrArg (fun i : Fin n => (i : ℤ)) heq
  simp only [Fin.val_zero,Int.natCast_zero] at hz
  omega

theorem negative_endpoint_length {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (v : Fin n) (hneg : d v < 0)
    (hgap : ∀ j : Fin n, 0 < j.val → j.val < v.val → d j=0) : (v : ℤ) ≤ -d v := by
  by_contra h
  have hN : (v : ℤ)+d v < (n : ℤ) := by have := v.isLt; omega
  let j : Fin n := ⟨((v : ℤ)+d v).toNat,by omega⟩
  have hjval : (j : ℤ)=(v : ℤ)+d v := by dsimp [j]; omega
  have hj := hgap j (by omega) (by omega)
  have he : p.symm v=j := by
    calc
      p.symm v = v+(d v : Fin n) := by simpa only [Int.cast_zero,add_zero] using (AffineLift.lift_residue hd v).symm
      _ = (((v : ℤ)+d v : ℤ) : Fin n) := by simp
      _ = j := by rw [← hjval]; simp
  have heq := fixed_source_of_fixed_target hd v j hj he
  have hz := congrArg (fun i : Fin n => (i : ℤ)) heq
  omega

#print axioms centered_pair
#print axioms positive_endpoint_length
#print axioms negative_endpoint_length
end LRX.ZeroGap
