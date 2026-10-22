import LRX.FiniteWindowLoad
import Mathlib.Algebra.Group.End

/-! Extension through a window preserves products and disjointness, so a
local cycle decomposition supplies the same ambient target. -/
namespace LRX.FiniteWindow
variable {n b : ℕ}

@[simp] theorem permutation_one (W : Window n b) : permutation W (1 : State b)=1 :=
  Equiv.Perm.extendDomain_one (windowEquiv W)

theorem permutation_mul (W : Window n b) (p q : State b) :
    permutation W (p*q)=permutation W p*permutation W q :=
  (Equiv.Perm.extendDomain_mul (windowEquiv W) p q).symm

theorem permutation_list_prod (W : Window n b) (l : List (State b)) :
    permutation W l.prod=(l.map (permutation W)).prod := by
  induction l with
  | nil => simp
  | cons p l ih => simp [permutation_mul,ih]

theorem permutation_disjoint (W : Window n b) (p q : State b) (hd : p.Disjoint q) :
    (permutation W p).Disjoint (permutation W q) := by
  intro j
  by_cases hj : Contains W j
  · obtain ⟨i,rfl⟩ := (contains_iff W j).mp hj
    rcases hd i with hi | hi
    · left; simp [hi]
    · right; simp [hi]
  · exact Or.inl (permutation_outside W p j hj)

theorem permutation_pairwise (W : Window n b) (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (l.map (permutation W)).Pairwise Equiv.Perm.Disjoint :=
  List.pairwise_map.mpr (hd.imp (fun h => permutation_disjoint W _ _ h))

#print axioms permutation_list_prod
#print axioms permutation_pairwise
end LRX.FiniteWindow
