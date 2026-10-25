import Mathlib

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


#print axioms carrier_le_iff
end LX.ForwardCarrier
