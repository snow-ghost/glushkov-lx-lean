import LRX.MaximumZeroCut

namespace LRX.FiniteCuts
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
open RotationWords
variable {n : ℕ} [NeZero n]

theorem recentered_mem_support (p : State n) (r x : Fin n) :
    x ∈ (localTarget p 0 r).support ↔ x+r ∈ p.support := by
  rw [mem_support_inverse,mem_support_inverse]
  have hh := moving_recenter p r x
  simpa only [RotationWords.rotation,Equiv.Perm.inv_def,AffineLift.rotation_power_apply,Fin.cast_val_eq_self] using hh

/-- Cutting immediately before v makes a fixed open separator (u,v) the
outside gap: the new support starts at 0 and ends at u-v. -/
theorem recentered_separator_width (p : State n) (u v : Fin n)
    (huv : u.val < v.val) (hu : u ∈ p.support) (hv : v ∈ p.support)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → p x=x) :
    externalWidth (localTarget p 0 v)=v.val-u.val := by
  classical
  let q := localTarget p 0 v
  have hzero : (0 : Fin n) ∈ q.support := by
    apply (recentered_mem_support p v 0).mpr
    simpa only [zero_add] using hv
  have hu' : u-v ∈ q.support := by
    apply (recentered_mem_support p v (u-v)).mpr
    simpa only [sub_add_cancel] using hu
  have hne : q.support.Nonempty := ⟨0,hzero⟩
  have hmin : q.support.min' hne=0 := by
    apply Fin.ext
    have hh := Finset.min'_le q.support 0 hzero
    change (q.support.min' hne).val ≤ (0 : Fin n).val at hh
    simpa only [Fin.val_zero] using Nat.eq_zero_of_le_zero hh
  have hmaxbound (x : Fin n) (hx : x ∈ q.support) : x.val ≤ (u-v).val := by
    have hx' := (recentered_mem_support p v x).mp hx
    let j := x+v
    have hj : j.val ≤ u.val ∨ v.val ≤ j.val := by
      by_contra hh
      have hf := hgap j (by omega) (by omega)
      exact (Equiv.Perm.mem_support.mp hx') hf
    have he : x=j-v := by dsimp [j]; ring
    have huv' : u < v := huv
    rw [he,Fin.coe_sub_iff_lt.mpr huv']
    rcases hj with hj | hj
    · have hjv : j < v := by change j.val < v.val; omega
      rw [Fin.coe_sub_iff_lt.mpr hjv]
      omega
    · rw [Fin.sub_val_of_le hj]
      have := j.isLt
      omega
  have hmax : q.support.max' hne=u-v := by
    apply Fin.ext
    have h1 := hmaxbound _ (Finset.max'_mem q.support hne)
    have h2 := Finset.le_max' q.support (u-v) hu'
    change (u-v).val ≤ (q.support.max' hne).val at h2
    omega
  change externalWidth q=v.val-u.val
  rw [externalWidth,dif_pos hne,hmin,hmax,Fin.val_zero,Nat.add_zero,
    Fin.coe_sub_iff_lt.mpr (show u < v from huv)]
  have := v.isLt
  omega

#print axioms recentered_separator_width
end LRX.FiniteCuts
