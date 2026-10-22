import LRX.FiniteCutRegularity
import Research.CayleyPy.FiniteGapService

/-! A cut profile constructed from a real finite permutation. The left/right
values are maxima of actual cut loads; this is a scalar envelope, not a claim
that one closed service attains all those discounts. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

def leftPeak (p : State b) (y : ℕ) : ℕ := (Finset.range (y+1)).sup (halfLoad p)

def rightPeak (p : State b) (x : ℕ) : ℕ := (Finset.Icc x b).sup (halfLoad p)

def profile (p : State b) : FiniteGapService.CutProfile b where
  halfLoad e := (halfLoad p e : ℤ)
  nonneg e _ := by positivity
  upper e he := by
    exact_mod_cast half_load_capacity p e he
  leftLoad y := 2*(leftPeak p y : ℤ)
  rightLoad x := 2*(rightPeak p x : ℤ)
  left_available e y hey _ := by
    have h : halfLoad p e ≤ leftPeak p y := Finset.le_sup (Finset.mem_range.mpr (by omega))
    have hc : (halfLoad p e : ℤ) ≤ (leftPeak p y : ℤ) := by exact_mod_cast h
    linarith
  right_available x e hxe heb := by
    have h : halfLoad p e ≤ rightPeak p x := Finset.le_sup (Finset.mem_Icc.mpr ⟨hxe,heb⟩)
    have hc : (halfLoad p e : ℤ) ≤ (rightPeak p x : ℤ) := by exact_mod_cast h
    linarith

theorem profile_footrule (p : State b) :
    (profile p).footrule=∑ i : Fin b, |(p i : ℤ)-(i : ℤ)| := by
  exact (footrule p).symm

/-- The abstract finite-gap arithmetic now applies to cut data derived from
an arbitrary permutation, including both parities and the empty interval. -/
theorem finite_cut_charge_bound (p : State b) (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ b) :
    (∑ i : Fin b, |(p i : ℤ)-(i : ℤ)|)+
      min ((x : ℤ)+y-2*(leftPeak p y : ℤ))
        (2*(b : ℤ)-x-y-2*(rightPeak p x : ℤ)) ≤
      (b*b/2 : ℕ)+(b%2 : ℕ) := by
  have h := FiniteGapService.finite_gap_service (profile p) x y hxy hy
  rw [profile_footrule] at h
  exact h

#print axioms profile_footrule
#print axioms finite_cut_charge_bound
end LRX.FiniteCuts
