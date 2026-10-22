import LRX.WindowReversalComponents

namespace LRX.FiniteWindow
open FiniteCuts
variable {n b : ℕ} [NeZero n]

/-- A real reversed filling pays its local inversion deficit from the global reserve. -/
theorem reversal_filling_inversion_budget (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i))
    (hshort : ∀ i, 2*|displacement p i| < (n : ℤ)) (hwidth : b ≤ (n+1)/2) :
    (b.choose 2 : ℤ)-(inversionNumber f : ℤ) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  have hR := replace_strict_short W p f Fin.revPerm hmatch hshort hwidth
  have hcap := finite_strict_band_inversion_capacity (replace W p f Fin.revPerm) hR
  have hprice := replace_inversion_price W p f Fin.revPerm hmatch
  rw [inversion_number_reversal] at hprice
  have hz : (inversionNumber (replace W p f Fin.revPerm) : ℤ)+(inversionNumber f : ℤ)=
      (inversionNumber p : ℤ)+(b.choose 2 : ℤ) := by exact_mod_cast hprice
  omega

/-- For a large original component a narrow reversal pays one additional unit of reserve. -/
theorem reversal_filling_strict_inversion_budget (hn : 2 ≤ n)
    (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i))
    (hmaj : AffineLift.Majorized (displacement p)) (hwidth : b ≤ (n-1)/2)
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component (displacement p) a).card) :
    (b.choose 2 : ℤ)-(inversionNumber f : ℤ)+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let R := replace W p f Fin.revPerm
  have hshort := FiniteWindow.majorized_short (canonical_lift p) hmaj
  have hR : ∀ i, 2*|displacement R i| < (n : ℤ) :=
    replace_strict_short W p f Fin.revPerm hmatch hshort (by omega)
  obtain ⟨hneg,hpos⟩ := replace_extremes_inherited W p f Fin.revPerm hmatch
    (((n-1)/2 : ℕ) : ℤ) (by exact_mod_cast hwidth)
  have hc := Finset.card_le_card (replace_reversal_component_subset W p f hmatch a)
  change (CycleFootprint.component (displacement p) a).card ≤
    (CycleFootprint.component (displacement R) a).card at hc
  have hlargeR : n-n/2 < (CycleFootprint.component (displacement R) a).card := by omega
  have hcap := strict_capacity_of_large_component hn (canonical_lift p).1 hmaj
    (canonical_lift R) hR hneg hpos a hlargeR
  have hend : (fun i : Fin n => (i : ℤ)+displacement R i)=(fun i => (R i : ℤ)) := by
    funext i; unfold displacement; omega
  rw [hend,canonical_inversion_count] at hcap
  have hprice := replace_inversion_price W p f Fin.revPerm hmatch
  rw [inversion_number_reversal] at hprice
  have hz : (inversionNumber R : ℤ)+(inversionNumber f : ℤ)=
      (inversionNumber p : ℤ)+(b.choose 2 : ℤ) := by exact_mod_cast hprice
  omega

#print axioms reversal_filling_inversion_budget
#print axioms reversal_filling_strict_inversion_budget
end LRX.FiniteWindow
