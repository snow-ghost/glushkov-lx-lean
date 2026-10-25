import LRX.RecenteredCrossings
import LRX.ZeroGapCentered
import LRX.ZeroGapExchange
import LRX.ZeroGapInversionSum
import Mathlib

/-! Every nonzero short balanced lift has a genuine endpoint-transposition
step with exact displacement and affine-inversion decreases. -/
namespace LRX.ZeroGap
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem exchange_endpoints (d : Fin n → ℤ) (v : Fin n) (hv : v ≠ 0) :
    (fun i : Fin n => (i : ℤ)+exchange d v i)=swapEndpoints (fun i : Fin n => (i : ℤ)+d i) v := by
  funext i
  by_cases hi : i=0
  · subst i
    simp [exchange,swapEndpoints]
  · by_cases hiv : i=v
    · subst i
      simp [exchange,swapEndpoints,hv]
    · simp [exchange,swapEndpoints,hi,hiv,Equiv.swap_apply_of_ne_of_ne hi hiv]

theorem exchange_inversions {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ))
    (v : Fin n) (hv : 0 < v.val) (hpos : 0 < d 0) (hneg : d v < 0)
    (hgap : ∀ i : Fin n, 0 < i.val → i.val < v.val → d i=0) :
    LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+exchange d v i)+(2*v.val-1) := by
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have hA := positive_endpoint_length hd v hpos hgap
  have hB := negative_endpoint_length hd v hneg hgap
  have hs0 := hshort 0
  have hsv := hshort v
  rw [abs_of_pos hpos] at hs0
  rw [abs_of_neg hneg] at hsv
  rw [exchange_endpoints d v hv0]
  apply endpoint_swap_inversions (fun i : Fin n => (i : ℤ)+d i) v hv
  · simpa using hA
  · omega
  · simp only [Fin.val_zero,Int.natCast_zero,zero_add]
    omega
  · intro i hi hi'
    simp only [hgap i hi hi',add_zero]

theorem exists_descent {p : State n} {d : Fin n → ℤ}
    (hd : AffineLift.IsLift p 0 d) (hshort : ∀ i, 2*|d i| < (n : ℤ)) (hne : ∃ i, d i ≠ 0) :
    ∃ u v : Fin n,
      0 < v.val ∧ 0 < RotationWords.localDisplacement d u 0 ∧ RotationWords.localDisplacement d u v < 0 ∧
      (∀ i : Fin n, 0 < i.val → i.val < v.val → RotationWords.localDisplacement d u i=0) ∧
      AffineLift.IsLift (Equiv.swap 0 v*RotationWords.localTarget p 0 u) 0
        (exchange (RotationWords.localDisplacement d u) v) ∧
      (∀ i, 2*|exchange (RotationWords.localDisplacement d u) v i| < (n : ℤ)) ∧
      (∑ i : Fin n, |d i|)=(∑ i : Fin n, |exchange (RotationWords.localDisplacement d u) v i|)+2*(v : ℤ) ∧
      LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+d i)=
        LiftedModel.inversionCount (fun i : Fin n => (i : ℤ)+exchange (RotationWords.localDisplacement d u) v i)+
          (2*v.val-1) := by
  obtain ⟨u,v,hpos,hneg,hv,hgap⟩ := centered_pair d hd.1 hne
  have hv0 : v ≠ 0 := by intro h; subst v; simp at hv
  have hlocal := RotationWords.recentered_lift (0 : Fin n) u (by simpa using hd)
  have hs : ∀ i, 2*|RotationWords.localDisplacement d u i| < (n : ℤ) := by
    intro i
    exact hshort ((L n^u.val) i)
  have hA := positive_endpoint_length hlocal v hpos hgap
  have hB := negative_endpoint_length hlocal v hneg hgap
  refine ⟨u,v,hv,hpos,hneg,hgap,exchange_lift hlocal v hv0,exchange_short _ v hv0 hA hB hs,?_,?_⟩
  · have hm := exchange_mass (RotationWords.localDisplacement d u) v hv0 hA hB
    rw [RotationWords.local_displacement_mass] at hm
    omega
  · have h := exchange_inversions hlocal hs v hv hpos hneg hgap
    rw [RotationWords.inversion_count_recentered (0 : Fin n) u (by simpa using hd)] at h
    exact h

#print axioms exchange_inversions
#print axioms exists_descent
end LRX.ZeroGap
