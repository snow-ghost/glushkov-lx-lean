import LRX.WindowComposition
import LRX.FiniteInversionBalance

namespace LRX.FiniteWindow
variable {n b : ℕ}

/-- Remove the actual filling, leaving a permutation that fixes the whole window. -/
def outsideFactor (W : Window n b) (p : State n) (f : State b) : State n :=
  p*(permutation W f)⁻¹

/-- Replace an invariant window filling f by g, retaining the original outside action. -/
def replace (W : Window n b) (p : State n) (f g : State b) : State n :=
  outsideFactor W p f*permutation W g

theorem outside_factor_embed (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (i : Fin b) :
    outsideFactor W p f (embed W i)=embed W i := by
  simp only [outsideFactor,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,permutation_symm,
    permutation_embed,hmatch,Equiv.apply_symm_apply]

theorem outside_factor_outside (W : Window n b) (p : State n) (f : State b)
    (i : Fin n) (hi : ¬Contains W i) : outsideFactor W p f i=p i := by
  simp only [outsideFactor,Equiv.Perm.mul_apply,Equiv.Perm.inv_def,permutation_symm,
    permutation_outside W f.symm i hi]

theorem outside_factor_disjoint (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) :
    (outsideFactor W p f).Disjoint (permutation W g) := by
  intro i
  by_cases hi : Contains W i
  · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
    exact Or.inl (outside_factor_embed W p f hmatch j)
  · exact Or.inr (permutation_outside W g i hi)

theorem outside_factor_recover (W : Window n b) (p : State n) (f : State b) :
    outsideFactor W p f*permutation W f=p := by
  unfold outsideFactor
  group

theorem replace_embed (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (i : Fin b) :
    replace W p f g (embed W i)=embed W (g i) := by
  rw [replace,Equiv.Perm.mul_apply,permutation_embed,outside_factor_embed W p f hmatch]

theorem replace_outside (W : Window n b) (p : State n) (f g : State b)
    (i : Fin n) (hi : ¬Contains W i) : replace W p f g i=p i := by
  rw [replace,Equiv.Perm.mul_apply,permutation_outside W g i hi,outside_factor_outside W p f i hi]

/-- A permutation fixing every point of the window cannot send an outside point into it. -/
theorem fixes_window_outside (W : Window n b) (p : State n)
    (hfix : ∀ i, p (embed W i)=embed W i) (j : Fin n) (hj : ¬Contains W j) :
    ¬Contains W (p j) := by
  intro hpj
  obtain ⟨i,hi⟩ := (contains_iff W (p j)).mp hpj
  have heq : p (embed W i)=p j := (hfix i).trans hi
  exact hj ((p.injective heq) ▸ contains_embed W i)

#print axioms replace_embed
#print axioms replace_outside
#print axioms outside_factor_disjoint
end LRX.FiniteWindow
