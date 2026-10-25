import LRX.InversionCrossings
import LRX.RecenteredLift
import Mathlib

/-! Choosing a different root cyclically relabels crossing data and preserves
the exact affine exchange price. -/
namespace LRX.RotationWords
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem crossing_recentered (d : Fin n → ℤ) (r i j : Fin n) :
    AffineLift.crossing (localDisplacement d r) i j=
      AffineLift.crossing d ((L n^r.val) i) ((L n^r.val) j) := by
  have hsub : (L n^r.val) j-(L n^r.val) i=j-i := by
    simp only [AffineLift.rotation_power_apply, Fin.cast_val_eq_self]
    abel
  simp only [AffineLift.crossing, AffineLift.crossingNumerator, localDisplacement, hsub]

theorem twice_inversion_count {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p c d) :
    2*LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      ∑ i : Fin n, ∑ j : Fin n, (AffineLift.crossing d i j).natAbs := by
  rw [LiftedModel.inversion_count_crossings, two_mul]
  have hp (i j : Fin n) :
      (if i < j then (AffineLift.crossing d i j).natAbs else 0)+
      (if j < i then (AffineLift.crossing d j i).natAbs else 0)=
      (AffineLift.crossing d i j).natAbs := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · subst j; simp
    · rw [ite_eq_right (not_lt_of_ge (le_of_lt h)), ite_eq_left h, zero_add,
        AffineLift.crossing_antisymm hd i j, Int.natAbs_neg]
  calc
    _ = (∑ i : Fin n, ∑ j : Fin n, if i < j then (AffineLift.crossing d i j).natAbs else 0)+
        ∑ i : Fin n, ∑ j : Fin n, if j < i then (AffineLift.crossing d j i).natAbs else 0 := by
      congr 1
      exact Finset.sum_comm
    _ = ∑ i : Fin n, ∑ j : Fin n,
        ((if i < j then (AffineLift.crossing d i j).natAbs else 0)+
        (if j < i then (AffineLift.crossing d j i).natAbs else 0)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => hp i j))

theorem inversion_count_recentered {p : State n} {d : Fin n → ℤ} (c r : Fin n)
    (hd : AffineLift.IsLift p (c : ℤ) d) :
    LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+localDisplacement d r i)=
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i) := by
  have hlocal := twice_inversion_count (recentered_lift c r hd)
  have horiginal := twice_inversion_count hd
  have hsum : (∑ i : Fin n, ∑ j : Fin n,
      (AffineLift.crossing (localDisplacement d r) i j).natAbs)=
      ∑ i : Fin n, ∑ j : Fin n, (AffineLift.crossing d i j).natAbs := by
    simp_rw [crossing_recentered]
    have hinner (i : Fin n) : (∑ j : Fin n,
        (AffineLift.crossing d ((L n^r.val) i) ((L n^r.val) j)).natAbs)=
        ∑ j : Fin n, (AffineLift.crossing d ((L n^r.val) i) j).natAbs :=
      Equiv.sum_comp (L n^r.val) (fun j => (AffineLift.crossing d ((L n^r.val) i) j).natAbs)
    simp_rw [hinner]
    exact Equiv.sum_comp (L n^r.val) (fun i => ∑ j : Fin n, (AffineLift.crossing d i j).natAbs)
  rw [hsum] at hlocal
  omega

#print axioms twice_inversion_count
#print axioms inversion_count_recentered
end LRX.RotationWords
