import LRX.WindowReplacement

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n b : ℕ}

theorem outside_window_comparison (W : Window n b) (x y z : Fin n)
    (hx : ¬Contains W x) (hy : Contains W y) (hz : Contains W z) :
    (x.val<y.val ↔ x.val<z.val) ∧ (y.val<x.val ↔ z.val<x.val) := by
  unfold Contains at hx hy hz
  omega

/-- Inversions split pointwise between the outside action and an invariant contiguous filling. -/
theorem inversion_indicator_mul_window (W : Window n b) (p : State n) (f : State b)
    (hfix : ∀ i, p (embed W i)=embed W i) (i j : Fin n) :
    inversionIndicator (p*permutation W f) i j=
      inversionIndicator p i j+inversionIndicator (permutation W f) i j := by
  by_cases hi : Contains W i
  · obtain ⟨a,rfl⟩ := (contains_iff W i).mp hi
    by_cases hj : Contains W j
    · obtain ⟨c,rfl⟩ := (contains_iff W j).mp hj
      simp only [inversionIndicator,Equiv.Perm.mul_apply,permutation_embed,hfix]
      split_ifs <;> omega
    · have hwin : inversionIndicator (permutation W f) (embed W a) j=0 :=
        if_neg (no_outside_inversion W f (embed W a) j (Or.inr hj))
      have hcmp := (outside_window_comparison W (p j) (embed W (f a)) (embed W a)
        (fixes_window_outside W p hfix j hj) (contains_embed W _) (contains_embed W _)).1
      rw [hwin]
      simp only [inversionIndicator,Equiv.Perm.mul_apply,permutation_embed,
        permutation_outside W f j hj,hfix,add_zero]
      simp only [hcmp]
  · by_cases hj : Contains W j
    · obtain ⟨c,rfl⟩ := (contains_iff W j).mp hj
      have hwin : inversionIndicator (permutation W f) i (embed W c)=0 :=
        if_neg (no_outside_inversion W f i (embed W c) (Or.inl hi))
      have hcmp := (outside_window_comparison W (p i) (embed W (f c)) (embed W c)
        (fixes_window_outside W p hfix i hi) (contains_embed W _) (contains_embed W _)).2
      rw [hwin]
      simp only [inversionIndicator,Equiv.Perm.mul_apply,permutation_embed,
        permutation_outside W f i hi,hfix,add_zero]
      simp only [hcmp]
    · have hwin : inversionIndicator (permutation W f) i j=0 :=
        if_neg (no_outside_inversion W f i j (Or.inl hi))
      rw [hwin]
      simp only [inversionIndicator,Equiv.Perm.mul_apply,
        permutation_outside W f i hi,permutation_outside W f j hj,add_zero]

theorem inversion_number_mul_window (W : Window n b) (p : State n) (f : State b)
    (hfix : ∀ i, p (embed W i)=embed W i) :
    inversionNumber (p*permutation W f)=inversionNumber p+inversionNumber f := by
  have h : (inversionNumber (p*permutation W f) : ℤ)=
      (inversionNumber p : ℤ)+(inversionNumber f : ℤ) := by
    rw [← sum_inversion_indicator]
    simp_rw [inversion_indicator_mul_window W p f hfix,Finset.sum_add_distrib]
    rw [sum_inversion_indicator,sum_inversion_indicator,inversion_number_window]
  exact_mod_cast h

/-- The real replacement changes inversion count by exactly the change of its filling. -/
theorem replace_inversion_price (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) :
    inversionNumber (replace W p f g)+inversionNumber f=
      inversionNumber p+inversionNumber g := by
  have hf := inversion_number_mul_window W (outsideFactor W p f) f (outside_factor_embed W p f hmatch)
  have hg := inversion_number_mul_window W (outsideFactor W p f) g (outside_factor_embed W p f hmatch)
  rw [outside_factor_recover] at hf
  change inversionNumber (replace W p f g)=_ at hg
  omega

#print axioms inversion_number_mul_window
#print axioms replace_inversion_price
end LRX.FiniteWindow
