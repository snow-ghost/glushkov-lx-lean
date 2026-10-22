import LX.ScanInversions

namespace LX.ForwardCarrier

/-- Physical target values during a forward sweep before the seam is reached. -/
def compareAt (F : ℕ → ℤ) (k j : ℕ) : ℤ :=
  if j = k then min (F k) (F (k+1))
  else if j = k+1 then max (F k) (F (k+1)) else F j

def sweepPrefix (F : ℕ → ℤ) : ℕ → ℕ → ℤ
  | 0 => F
  | k+1 => compareAt (sweepPrefix F k) k

theorem prefix_tail (F : ℕ → ℤ) (k j : ℕ) (hkj : k < j) : sweepPrefix F k j = F j := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [sweepPrefix, compareAt, ite_eq_right (by omega : j ≠ k), ite_eq_right (by omega : j ≠ k+1)]
    exact ih (by omega)

theorem carrier_step (F : ℕ → ℤ) (k : ℕ) :
    sweepPrefix F (k+1) (k+1) = max (sweepPrefix F k k) (F (k+1)) := by
  simp only [sweepPrefix, compareAt, ite_eq_right (by omega : k+1 ≠ k), ite_true]
  rw [prefix_tail F k (k+1) (by omega)]

/-- The actual carried target is the maximum of all targets already encountered. -/
theorem carrier_le_iff (F : ℕ → ℤ) (k : ℕ) (x : ℤ) :
    sweepPrefix F k k ≤ x ↔ ∀ j ≤ k, F j ≤ x := by
  induction k with
  | zero => simp [sweepPrefix]
  | succ k ih =>
    rw [carrier_step, max_le_iff, ih]
    constructor
    · rintro ⟨h, hx⟩ j hj
      by_cases he : j=k+1
      · simpa only [he] using hx
      · exact h j (by omega)
    · intro h
      exact ⟨fun j hj => h j (by omega), h (k+1) (by omega)⟩

theorem lt_carrier_iff (F : ℕ → ℤ) (k : ℕ) (x : ℤ) :
    x < sweepPrefix F k k ↔ ∃ j ≤ k, x < F j := by
  rw [← not_le, carrier_le_iff]
  push Not
  rfl

/-- If a token is the sweepPrefix maximum, it is carried until the first larger target. -/
theorem first_larger_drop (F : ℕ → ℤ) (i r : ℕ) (hir : i < r)
    (hprefix : ∀ j < r, F j ≤ F i) (hnext : F i < F r) :
    sweepPrefix F r (r-1) = F i := by
  have hr : 0 < r := by omega
  have hcarrier : sweepPrefix F (r-1) (r-1) = F i := by
    apply le_antisymm
    · exact (carrier_le_iff F (r-1) (F i)).mpr (fun j hj => hprefix j (by omega))
    · by_contra h
      have hh : sweepPrefix F (r-1) (r-1) < F i := by omega
      have hle := (carrier_le_iff F (r-1) (sweepPrefix F (r-1) (r-1))).mp le_rfl i (by omega)
      omega
  have he : r = (r-1)+1 := by omega
  rw [he]
  simp only [sweepPrefix, compareAt, hcarrier]
  rw [show r-1+1=r by omega, prefix_tail F (r-1) r (by omega)]
  rw [ite_eq_left rfl]
  exact min_eq_left (le_of_lt hnext)

#print axioms carrier_le_iff
#print axioms first_larger_drop
end LX.ForwardCarrier
