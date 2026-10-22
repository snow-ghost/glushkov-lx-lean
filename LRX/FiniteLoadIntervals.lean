import LRX.FiniteComponentExtrema

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

theorem finite_positive_port_before_end (p : State n) (r : Fin n)
    (hpos : 0 < RotationWords.portLoad (displacement p.symm) r) : r.val+1 < n := by
  have hz : halfLoad p.symm n=0 := by
    rw [forward_as_sum]
    apply Finset.sum_eq_zero
    intro i _
    apply if_neg
    have := (p.symm i).isLt
    omega
  have hr := r.isLt
  by_contra hh
  have he : r.val+1=n := by omega
  rw [port_load_eq_twice_half,he,hz] at hpos
  norm_num at hpos

theorem finite_loaded_step_unit (p : State n) (x y : Fin n)
    (he : CycleFootprint.LoadedStep (displacement p.symm) x y) :
    x.val+1=y.val ∨ y.val+1=x.val := by
  rcases he with ⟨hxy,hpos⟩ | ⟨hyx,hpos⟩
  · left
    rw [hxy,Fin.val_add_one_of_lt' (finite_positive_port_before_end p x hpos)]
  · right
    rw [hyx,Fin.val_add_one_of_lt' (finite_positive_port_before_end p y hpos)]

theorem finite_load_path_interval (p : State n) {a b : Fin n}
    (hp : CycleFootprint.LoadPath (displacement p.symm) a b)
    (x : Fin n) (hlo : min a.val b.val ≤ x.val) (hhi : x.val ≤ max a.val b.val) :
    CycleFootprint.LoadPath (displacement p.symm) a x := by
  induction hp generalizing x with
  | refl =>
    have he : x=a := by apply Fin.ext; omega
    subst x
    exact Relation.ReflTransGen.refl
  | @tail b c hpath hedge ih =>
    by_cases hxc : x=c
    · subst x; exact hpath.tail hedge
    · have hne : x.val ≠ c.val := fun h => hxc (Fin.ext h)
      have hu := finite_loaded_step_unit p b c hedge
      apply ih x <;> rcases hu with hu | hu <;> omega

theorem finite_component_interval (p : State n) (a : Fin n) :
    componentSet p a=Finset.Icc (componentLeft p a) (componentRight p a) := by
  ext x
  change x ∈ CycleFootprint.component (displacement p.symm) a ↔ _
  rw [CycleFootprint.mem_component,Finset.mem_Icc]
  constructor
  · intro hx
    exact ⟨component_left_bound p a x hx,component_right_bound p a x hx⟩
  · intro hx
    have hl := component_left_path p a
    have hr := component_right_path p a
    have hlr := component_left_bound p a (componentRight p a) hr
    exact hl.trans (finite_load_path_interval p ((CycleFootprint.load_path_symm _ hl).trans hr) x
      (by have hh : (componentLeft p a).val ≤ x.val := hx.1; omega)
      (by have hh : x.val ≤ (componentRight p a).val := hx.2; omega))

theorem ordered_component_extrema (p : State n) (a b : Fin n) (hab : a.val < b.val)
    (hnot : ¬CycleFootprint.LoadPath (displacement p.symm) a b) :
    (componentRight p a).val < (componentLeft p b).val := by
  have ha := component_right_path p a
  have hb := component_left_path p b
  have hmaxa : a.val ≤ (componentRight p a).val := component_right_bound p a a Relation.ReflTransGen.refl
  have hminb : (componentLeft p b).val ≤ b.val := component_left_bound p b b Relation.ReflTransGen.refl
  have har : (componentRight p a).val < b.val := by
    by_contra hn
    exact hnot (finite_load_path_interval p ha b (by omega) (by omega))
  by_contra hn
  have hba : CycleFootprint.LoadPath (displacement p.symm) b (componentRight p a) :=
    finite_load_path_interval p hb (componentRight p a) (by omega) (by omega)
  exact hnot (ha.trans (CycleFootprint.load_path_symm _ hba))

#print axioms finite_component_interval
#print axioms ordered_component_extrema
end LRX.FiniteCuts
