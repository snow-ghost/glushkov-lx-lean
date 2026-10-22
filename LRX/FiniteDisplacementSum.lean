import LRX.FiniteCycleLoads

/-! Displacements and their absolute mass add over disjoint finite cycles. -/
namespace LRX.FiniteCuts
open scoped BigOperators
variable {b : ℕ}

theorem displacement_mul (p q : State b) (h : p.Disjoint q) (i : Fin b) :
    displacement (p*q) i=displacement p i+displacement q i := by
  unfold displacement
  rcases h i with hi | hi
  · have hm : (p*q) i=q i := by rw [h.commute.eq]; simp [hi]
    rw [hm,hi]
    ring
  · have hm : (p*q) i=p i := by simp [hi]
    rw [hm,hi]
    ring

theorem abs_displacement_mul (p q : State b) (h : p.Disjoint q) (i : Fin b) :
    |displacement (p*q) i|=|displacement p i|+|displacement q i| := by
  rw [displacement_mul p q h i]
  rcases h i with hi | hi <;> simp [displacement,hi]

theorem displacement_list_prod (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) (i : Fin b) :
    displacement l.prod i=(l.map (fun p => displacement p i)).sum := by
  induction l with
  | nil => simp [displacement]
  | cons p l ih =>
    obtain ⟨hp, hl⟩ := List.pairwise_cons.mp hd
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [displacement_mul p l.prod (Equiv.Perm.disjoint_prod_right l hp), ih hl]

theorem displacement_mass_list_prod (l : List (State b))
    (hd : l.Pairwise Equiv.Perm.Disjoint) :
    (∑ i : Fin b, |displacement l.prod i|)=
      (l.map (fun p => ∑ i : Fin b, |displacement p i|)).sum := by
  induction l with
  | nil => simp [displacement]
  | cons p l ih =>
    obtain ⟨hp, hl⟩ := List.pairwise_cons.mp hd
    simp only [List.prod_cons, List.map_cons, List.sum_cons,
      abs_displacement_mul p l.prod (Equiv.Perm.disjoint_prod_right l hp)]
    rw [Finset.sum_add_distrib, ih hl]

#print axioms displacement_list_prod
#print axioms displacement_mass_list_prod
end LRX.FiniteCuts
