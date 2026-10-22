import LRX.TwoComponentGeometry

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

noncomputable def componentRoots (p : State n) : Finset (Fin n) := by
  classical
  exact p.support.filter (fun a => ∀ b ∈ p.support,
    CycleFootprint.LoadPath (displacement p.symm) a b → a.val ≤ b.val)

theorem mem_support_inverse (p : State n) (i : Fin n) : i ∈ p.support ↔ p.symm i ≠ i := by
  rw [← Equiv.Perm.support_inv p,Equiv.Perm.mem_support]
  rfl

theorem component_roots_cover (p : State n) (i : Fin n) (hi : p.symm i ≠ i) :
    ∃ r ∈ componentRoots p, CycleFootprint.LoadPath (displacement p.symm) r i := by
  classical
  let T := p.support.filter (fun x => CycleFootprint.LoadPath (displacement p.symm) i x)
  have hT : T.Nonempty := ⟨i,Finset.mem_filter.mpr
    ⟨(mem_support_inverse p i).mpr hi,Relation.ReflTransGen.refl⟩⟩
  let r := T.min' hT
  have hr : r ∈ T := Finset.min'_mem _ _
  obtain ⟨hrs,hir⟩ := Finset.mem_filter.mp hr
  refine ⟨r,?_,CycleFootprint.load_path_symm _ hir⟩
  apply Finset.mem_filter.mpr
  refine ⟨hrs,?_⟩
  intro b hb hrb
  exact Finset.min'_le T b (Finset.mem_filter.mpr ⟨hb,hir.trans hrb⟩)

theorem component_roots_unique (p : State n) {a b : Fin n}
    (ha : a ∈ componentRoots p) (hb : b ∈ componentRoots p)
    (hp : CycleFootprint.LoadPath (displacement p.symm) a b) : a=b := by
  classical
  obtain ⟨ha,hminA⟩ := Finset.mem_filter.mp ha
  obtain ⟨hb,hminB⟩ := Finset.mem_filter.mp hb
  have hab := hminA b hb hp
  have hba := hminB a ha (CycleFootprint.load_path_symm _ hp)
  apply Fin.ext
  omega

theorem ordered_component_roots (p : State n) {a b : Fin n}
    (ha : a ∈ componentRoots p) (hb : b ∈ componentRoots p) (hab : a.val < b.val) :
    (componentRight p a).val < (componentLeft p b).val := by
  apply ordered_component_extrema p a b hab
  intro hp
  have he := component_roots_unique p ha hb hp
  subst b
  omega

#print axioms component_roots_cover
#print axioms component_roots_unique

theorem component_nontrivial_width (p : State n) (a : Fin n) (ha : p.symm a ≠ a) :
    (componentLeft p a).val < (componentRight p a).val := by
  have hd : AffineLift.IsLift p 0 (displacement p.symm) := by simpa only [Equiv.symm_symm] using canonical_lift p.symm
  have h0 := component_left_bound p a a Relation.ReflTransGen.refl
  have h1 := component_right_bound p a a Relation.ReflTransGen.refl
  have hpath := CycleFootprint.arrow_target_load_path hd a
  have h2 := component_left_bound p a (p.symm a) hpath
  have h3 := component_right_bound p a (p.symm a) hpath
  have hne : (p.symm a).val ≠ a.val := fun he => ha (Fin.ext he)
  omega

theorem consecutive_component_gap_fixed (p : State n) (a b : Fin n)
    (ha : a ∈ componentRoots p) (hb : b ∈ componentRoots p)
    (hnext : ∀ c ∈ componentRoots p, ¬(a.val < c.val ∧ c.val < b.val))
    (x : Fin n) (hax : (componentRight p a).val < x.val)
    (hxb : x.val < (componentLeft p b).val) : p x=x := by
  by_contra hfix
  have hm : p.symm x ≠ x := by
    intro he
    exact hfix (by simpa only [Equiv.apply_symm_apply] using (congrArg p he).symm)
  obtain ⟨c,hc,hcx⟩ := component_roots_cover p x hm
  have hclo := component_left_bound p c x hcx
  have hchi := component_right_bound p c x hcx
  have hac : a.val < c.val := by
    by_contra h
    by_cases he : c=a
    · subst c; omega
    · have hne : c.val ≠ a.val := fun h => he (Fin.ext h)
      have horder := ordered_component_roots p hc ha (by omega)
      have habound := component_left_bound p a (componentRight p a) (component_right_path p a)
      omega
  have hcb : c.val < b.val := by
    by_contra h
    by_cases he : c=b
    · subst c; omega
    · have hne : c.val ≠ b.val := fun h => he (Fin.ext h)
      have horder := ordered_component_roots p hb hc (by omega)
      have hbbound := component_left_bound p b (componentRight p b) (component_right_path p b)
      omega
  exact hnext c hc ⟨hac,hcb⟩

#print axioms component_nontrivial_width
#print axioms consecutive_component_gap_fixed
end LRX.FiniteCuts
