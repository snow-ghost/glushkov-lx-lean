import LRX.CanonicalWindowRightRoute

namespace LRX.FiniteWindow
open scoped BigOperators
open RotationWords
variable {n b : ℕ} [NeZero n]

theorem canonical_window_contains_iff (p : State n) (W : Window n b) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) (x : Fin n) :
    Contains W (p.symm x) ↔ Contains W x := by
  constructor
  · intro hx
    obtain ⟨j,hj⟩ := (contains_iff W _).mp hx
    have hh : p.symm (embed W (filling.symm j))=p.symm x := by
      rw [hmatch,Equiv.apply_symm_apply]
      exact hj
    have he := p.symm.injective hh
    exact he ▸ contains_embed W (filling.symm j)
  · intro hx
    obtain ⟨j,rfl⟩ := (contains_iff W _).mp hx
    rw [hmatch]
    exact contains_embed W (filling j)

theorem canonical_window_half_load (p : State n) (W : Window n b) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) :
    FiniteCuts.halfLoad p.symm W.offset=FiniteCuts.halfLoad p.symm (W.offset+b) := by
  rw [FiniteCuts.forward_as_sum,FiniteCuts.forward_as_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := canonical_window_contains_iff p W filling hmatch i
  unfold Contains at hi
  have he : (i.val < W.offset ∧ W.offset ≤ (p.symm i).val) ↔
      (i.val < W.offset+b ∧ W.offset+b ≤ (p.symm i).val) := by omega
  simp only [he]

theorem canonical_window_boundary_load (p : State n) (W : Window n b) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (u v : Fin n) (hoff : W.offset=u.val+1) (hedge : W.offset+b=v.val) :
    portLoad (FiniteCuts.displacement p.symm) u=portLoad (FiniteCuts.displacement p.symm) (v-1) := by
  have hv0 : v ≠ 0 := by
    intro h
    rw [h,Fin.val_zero] at hedge
    omega
  have hv : (v-1 : Fin n).val+1=v.val := by
    rw [Fin.val_sub_one_of_ne_zero hv0]
    have := Fin.val_ne_zero_iff.mpr hv0
    omega
  rw [FiniteCuts.port_load_eq_twice_half,FiniteCuts.port_load_eq_twice_half,hv,← hoff,← hedge]
  rw [canonical_window_half_load p W filling hmatch]

#print axioms canonical_window_boundary_load
end LRX.FiniteWindow
