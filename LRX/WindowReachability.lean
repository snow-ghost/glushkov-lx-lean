import LRX.PacketCoverage
import LRX.FiniteWindowLoad

/-! An invariant window with canonical finite arrows is closed under service
reachability. A root outside it cannot lie in the same strong component. -/
namespace LRX.FiniteWindow
variable {n b : ℕ}

theorem periodic_copy_unique (j : Fin n) (k : ℤ)
    (hlo : 0 ≤ (j : ℤ)+k*(n : ℤ)) (hhi : (j : ℤ)+k*(n : ℤ) < (n : ℤ)) : k=0 := by
  have hj := j.isLt
  have hn : 0 < (n : ℤ) := by omega
  by_contra h
  rcases lt_or_gt_of_ne h with hk | hk
  · have hm := mul_le_mul_of_nonneg_right (show k ≤ -1 by omega) (le_of_lt hn)
    nlinarith
  · have hm := mul_le_mul_of_nonneg_right (show 1 ≤ k by omega) (le_of_lt hn)
    nlinarith

theorem inverse_inside (W : Window n b) (p : State n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) (i : Fin n)
    (hi : Contains W i) : Contains W (p.symm i) := by
  obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
  rw [hmatch]
  exact contains_embed W _

theorem same_cycle_inside (W : Window n b) (p : State n) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i)) {i j : Fin n}
    (hi : Contains W i) (hc : (p⁻¹).SameCycle i j) : Contains W j := by
  obtain ⟨k,rfl⟩ := hc.exists_nat_pow_eq
  clear hc
  induction k with
  | zero => simpa using hi
  | succ k ih =>
    rw [pow_succ',Equiv.Perm.mul_apply]
    exact inverse_inside W p filling hmatch _ ih

theorem service_edge_inside (W : Window n b) (p : State n) (d : Fin n → ℤ) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    {i j : Fin n} (hi : Contains W i) (he : BufferProgram.ServiceEdge p d i j) : Contains W j := by
  rcases he with hc | ⟨_,k,hlo,hhi⟩
  · exact same_cycle_inside W p filling hmatch hi hc
  · obtain ⟨a,rfl⟩ := (contains_iff W i).mp hi
    have hend : (embed W a : ℤ)+d (embed W a)=(embed W (filling a) : ℤ) := by
      rw [hfinite]
      simp [embed,FiniteCuts.displacement]
    rw [hend] at hlo hhi
    have hs := contains_embed W a
    have ht := contains_embed W (filling a)
    unfold Contains at hs ht ⊢
    have hfit := W.fits
    have hlow : 0 ≤ (j : ℤ)+k*(n : ℤ) := by omega
    have hhigh : (j : ℤ)+k*(n : ℤ) < (n : ℤ) := by omega
    have hk := periodic_copy_unique j k hlow hhigh
    subst k
    simp only [zero_mul,add_zero] at hlo hhi
    omega

theorem reaches_inside (W : Window n b) (p : State n) (d : Fin n → ℤ) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    {i j : Fin n} (hi : Contains W i) (hpath : PrunedLift.Reaches p d i j) : Contains W j := by
  induction hpath with
  | refl => exact hi
  | tail hpath he ih => exact service_edge_inside W p d filling hmatch hfinite ih he

theorem core_outside_window (W : Window n b) (p : State n) (d : Fin n → ℤ) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (root : Fin n) (hroot : ¬Contains W root) (i : Fin n)
    (hback : PrunedLift.Reaches p d i root) : ¬Contains W i := by
  intro hi
  exact hroot (reaches_inside W p d filling hmatch hfinite hi hback)

theorem selected_window_keeps_core (W : Window n b) (p selected : State n) (d : Fin n → ℤ) (filling : State b)
    (hmatch : ∀ i, p.symm (embed W i)=embed W (filling i))
    (hfinite : ∀ i, d (embed W i)=FiniteCuts.displacement filling i)
    (root : Fin n) (hroot : ¬Contains W root)
    (hselected : ∀ i ∈ selected.support, Contains W i) :
    PrunedLift.KeepsCore p d root selected.supportᶜ := by
  intro i _ hback
  apply Finset.mem_compl.mpr
  intro hi
  exact core_outside_window W p d filling hmatch hfinite root hroot i hback (hselected i hi)

#print axioms service_edge_inside
#print axioms reaches_inside
#print axioms core_outside_window
end LRX.FiniteWindow
