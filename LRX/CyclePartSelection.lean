import LRX.CyclePart
import LRX.WindowComposition
import Mathlib.GroupTheory.Perm.Cycle.Factors

/-! Products of selected disjoint cycles remain parts of the original target.
Window extension and inversion preserve this relation. -/
namespace LRX.CyclePart
variable {n b : ℕ}

theorem trans {a b c : State n} (hab : IsPart a b) (hbc : IsPart b c) : IsPart a c := by
  intro i hi
  have he := hab i hi
  exact he.trans (hbc i (by rwa [← he]))

theorem inverse {a b : State n} (h : IsPart a b) : IsPart a⁻¹ b⁻¹ := by
  intro i hi
  have hm : i ∈ a.support := by
    simpa only [Equiv.Perm.support_inv] using (Equiv.Perm.mem_support.mpr hi)
  exact (inverse_on_support a b h i hm).symm

theorem product (l : List (State n)) (p : State n)
    (hd : l.Pairwise Equiv.Perm.Disjoint) (hp : ∀ q ∈ l, IsPart q p) : IsPart l.prod p := by
  intro i hi
  obtain ⟨q,hq,hm⟩ := Equiv.Perm.exists_mem_support_of_mem_support_prod (Equiv.Perm.mem_support.mpr hi)
  exact (Equiv.Perm.eq_on_support_mem_disjoint hq hd i hm).symm.trans
    (hp q hq i (Equiv.Perm.mem_support.mp hm))

theorem cycle_factor {p q : State n} (hq : q ∈ p.cycleFactorsFinset) : IsPart q p := by
  intro i hi
  exact (Equiv.Perm.mem_cycleFactorsFinset_iff.mp hq).2 i (Equiv.Perm.mem_support.mpr hi)

theorem window (W : FiniteWindow.Window n b) {p q : State b} (h : IsPart q p) :
    IsPart (FiniteWindow.permutation W q) (FiniteWindow.permutation W p) := by
  intro j hj
  have hm : FiniteWindow.Contains W j := by
    by_contra hm
    exact hj (FiniteWindow.permutation_outside W q j hm)
  obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hm
  have hi : q i ≠ i := by intro hi; exact hj (by simp [hi])
  simp only [FiniteWindow.permutation_embed,h i hi]

theorem window_part (W : FiniteWindow.Window n b) (q : State b) (p : State n)
    (hmatch : ∀ i, p (FiniteWindow.embed W i)=FiniteWindow.embed W (q i)) :
    IsPart (FiniteWindow.permutation W q) p := by
  intro j hj
  have hm : FiniteWindow.Contains W j := by
    by_contra hm
    exact hj (FiniteWindow.permutation_outside W q j hm)
  obtain ⟨i,rfl⟩ := (FiniteWindow.contains_iff W j).mp hm
  rw [FiniteWindow.permutation_embed,hmatch]

#print axioms product
#print axioms window
#print axioms window_part
end LRX.CyclePart
