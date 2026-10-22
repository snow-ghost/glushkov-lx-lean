import LRX.PrunedLift

/-! A root star remains connected after deleting any union of leaf cycles.
The intermediate vertices stay in the root or the retained target cycle. -/
namespace LRX.PrunedLift
variable {n : ℕ}

theorem inverse_mem_iff (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (i : Fin n) : p.symm i ∈ S ↔ i ∈ S := by
  simpa using (hS (p.symm i)).symm

theorem inverse_pow_mem (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (a : Fin n) (ha : a ∈ S) (k : ℕ) :
    ((p⁻¹)^k) a ∈ S := by
  induction k with
  | zero => simpa using ha
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    exact (inverse_mem_iff p S hS _).mpr ih

theorem same_cycle_mem (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) {a b : Fin n} (ha : a ∈ S)
    (hc : (p⁻¹).SameCycle a b) : b ∈ S := by
  obtain ⟨k, rfl⟩ := hc.exists_nat_pow_eq
  exact inverse_pow_mem p S hS a ha k

theorem inverse_pow_eq (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (a : Fin n) (ha : a ∈ S) (k : ℕ) :
    (((permutation p S hS)⁻¹)^k) a=((p⁻¹)^k) a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
    exact ite_eq_left (inverse_pow_mem p S hS a ha k)

theorem same_cycle (p : State n) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) {a b : Fin n} (ha : a ∈ S)
    (hc : (p⁻¹).SameCycle a b) : ((permutation p S hS)⁻¹).SameCycle a b := by
  obtain ⟨k, rfl⟩ := hc.exists_nat_pow_eq
  rw [← inverse_pow_eq p S hS a ha k]
  exact Equiv.Perm.SameCycle.pow_right (Equiv.Perm.SameCycle.refl _ _)

theorem service_edge (p : State n) (d : Fin n → ℤ) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) {a b : Fin n} (ha : a ∈ S) (hb : b ∈ S)
    (he : BufferProgram.ServiceEdge p d a b) :
    BufferProgram.ServiceEdge (permutation p S hS) (displacement S d) a b := by
  rcases he with hc | ⟨hm, k, hlo, hhi⟩
  · exact Or.inl (same_cycle p S hS ha hc)
  · right
    refine ⟨?_, k, ?_, ?_⟩
    · simpa only [Equiv.Perm.inv_def, permutation_symm_apply, ite_eq_left hb] using hm
    · simpa only [displacement, ite_eq_left ha] using hlo
    · simpa only [displacement, ite_eq_left ha] using hhi

/-- Each target cycle is touched directly by some arrow of the root cycle. -/
def RootStar (p : State n) (d : Fin n → ℤ) (root : Fin n) : Prop :=
  ∀ i, d i ≠ 0 → ∃ a j,
    (p⁻¹).SameCycle root a ∧ BufferProgram.ServiceEdge p d a j ∧ (p⁻¹).SameCycle j i

theorem root_star_pruned (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (hstar : RootStar p d root) (S : Finset (Fin n))
    (hS : ∀ i, p i ∈ S ↔ i ∈ S) (hroot : root ∈ S) :
    RootStar (permutation p S hS) (displacement S d) root := by
  intro i hi
  have hiS : i ∈ S := by by_contra h; exact hi (by simp [displacement,h])
  have hdi : d i ≠ 0 := by simpa [displacement,hiS] using hi
  obtain ⟨a,j,ha,he,hj⟩ := hstar i hdi
  have haS := same_cycle_mem p S hS hroot ha
  have hjS := same_cycle_mem p S hS hiS hj.symm
  exact ⟨a,j,same_cycle p S hS hroot ha,service_edge p d S hS haS hjS he,
    same_cycle p S hS hjS hj⟩

theorem root_star_reaches (p : State n) (d : Fin n → ℤ) (root : Fin n)
    (hstar : RootStar p d root) (i : Fin n) (hi : d i ≠ 0) :
    Relation.ReflTransGen (BufferProgram.ServiceEdge p d) root i := by
  obtain ⟨a,j,ha,he,hj⟩ := hstar i hi
  have h1 : Relation.ReflTransGen (BufferProgram.ServiceEdge p d) root a :=
    Relation.ReflTransGen.single (Or.inl ha)
  have h2 : Relation.ReflTransGen (BufferProgram.ServiceEdge p d) a j :=
    Relation.ReflTransGen.single he
  exact h1.trans (h2.trans (Relation.ReflTransGen.single (Or.inl hj)))

#print axioms root_star_pruned
#print axioms root_star_reaches
end LRX.PrunedLift
