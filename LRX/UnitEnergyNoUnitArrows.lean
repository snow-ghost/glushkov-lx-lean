import LRX.UnitEnergyUnitPeak

namespace LRX.FiniteCuts
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- Saturation at epsilon=1 with two fixed positions forces equal sign counts. -/
theorem unit_energy_two_fixed_sign_counts (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hf : n-p.support.card=2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1) :
    (Finset.univ.filter (fun i : Fin n => 0 < displacement p.symm i)).card=n/2-1 ∧
    (Finset.univ.filter (fun i : Fin n => displacement p.symm i < 0)).card=n/2-1 := by
  classical
  let P := Finset.univ.filter (fun i : Fin n => 0 < displacement p.symm i)
  let N := Finset.univ.filter (fun i : Fin n => displacement p.symm i < 0)
  let m : ℤ := (n/2 : ℕ)
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hn : (n : ℤ)=2*m := by dsimp only [m]; omega
  have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
  have hdis : Disjoint P N := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hp := (Finset.mem_filter.mp hi).2
    have hn := (Finset.mem_filter.mp hj).2
    omega
  have hunion : P ∪ N = p.support := by
    ext i
    simp only [P,N,Finset.mem_union,Finset.mem_filter,Finset.mem_univ,true_and,mem_support_inverse]
    constructor
    · intro h hh
      simp only [displacement,hh,sub_self,lt_self_iff_false,or_self] at h
    · intro h
      have hv : (p.symm i).val ≠ i.val := fun hh => h (Fin.ext hh)
      unfold displacement
      omega
  have hcount : P.card+N.card=p.support.card := by
    rw [← hunion,Finset.card_union_of_disjoint hdis]
  have hd := canonical_lift p.symm
  have hpos := AffineLift.selected_positive_residual (displacement p.symm) hd.1 hmaj
    ∅ (Finset.empty_subset P)
  have hneg := AffineLift.original_selected_negative_residual hd.1 hmaj
    (Function.Embedding.refl (Fin n)) (displacement p.symm) (fun _ => rfl) hd.1
    ∅ (Finset.empty_subset N)
  simp only [Finset.sum_empty,mul_zero,zero_add,Finset.sdiff_empty] at hpos hneg
  change (∑ i, |displacement p.symm i|) ≤ (P.card : ℤ)*((n : ℤ)-P.card) at hpos
  change (∑ i, |displacement p.symm i|) ≤ (N.card : ℤ)*((n : ℤ)-N.card) at hneg
  change m*((n : ℤ)-m)-(∑ i, |displacement p.symm i|)=1 at he
  rw [hn] at he hpos hneg
  have hp : m-1 ≤ (P.card : ℤ) := by
    by_contra hh
    have hsq := sq_nonneg ((P.card : ℤ)-m+2)
    nlinarith only [he,hpos,hsq,show (P.card : ℤ) ≤ m-2 by omega]
  have hne : m-1 ≤ (N.card : ℤ) := by
    by_contra hh
    have hsq := sq_nonneg ((N.card : ℤ)-m+2)
    nlinarith only [he,hneg,hsq,show (N.card : ℤ) ≤ m-2 by omega]
  change P.card=n/2-1 ∧ N.card=n/2-1
  dsimp only [m] at hn hp hne
  omega

/-- In the actual epsilon=1,f=2 map every nonzero arrow has length at least two.
A hypothetical unit arrow leaves only m-2 arrows of its sign, whose majorized
capacity misses the actual mass by one. -/
theorem unit_energy_two_fixed_no_unit_arrow (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hf : n-p.support.card=2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1)
    (i : Fin n) : |displacement p.symm i| ≠ 1 := by
  classical
  intro hi
  obtain ⟨hP,hN⟩ := unit_energy_two_fixed_sign_counts p hmaj hf he
  have hn4 := unit_energy_reserve_size_mod_four p he
  let m : ℤ := (n/2 : ℕ)
  have hn : (n : ℤ)=2*m := by dsimp only [m]; omega
  have hd := canonical_lift p.symm
  have hcases : displacement p.symm i=1 ∨ displacement p.symm i= -1 := by
    by_cases hh : 0 ≤ displacement p.symm i
    · exact Or.inl ((abs_of_nonneg hh).symm.trans hi)
    · right
      have hhabs := abs_of_neg (show displacement p.symm i < 0 by omega)
      rw [hhabs] at hi
      omega
  have hm : 2 ≤ n/2 := by
    have hs : p.support.card ≤ n := by simpa using Finset.card_le_univ p.support
    have hnon : p.support.card ≠ 0 := by
      intro hz
      have hc : p.support=∅ := Finset.card_eq_zero.mp hz
      have hip : i ∈ p.support := by
        rw [mem_support_inverse]
        intro hh
        simp only [displacement,hh,sub_self,abs_zero] at hi
        omega
      rw [hc] at hip
      exact Finset.notMem_empty i hip
    omega
  have hsubcast : ((n/2-1-1 : ℕ) : ℤ)=m-2 := by dsimp only [m]; omega
  change m*((n : ℤ)-m)-(∑ j, |displacement p.symm j|)=1 at he
  rw [hn] at he
  rcases hcases with hpos | hneg
  · have hsub : {i} ⊆ Finset.univ.filter (fun j : Fin n => 0 < displacement p.symm j) := by
      simpa only [Finset.singleton_subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,hpos] using (show (0 : ℤ)<1 by omega)
    have hcap := AffineLift.selected_positive_residual (displacement p.symm) hd.1 hmaj {i} hsub
    rw [Finset.card_sdiff_of_subset hsub,hP] at hcap
    simp only [Finset.sum_singleton,Finset.card_singleton,hi] at hcap
    rw [hsubcast,hn] at hcap
    nlinarith only [he,hcap]
  · have hsub : {i} ⊆ Finset.univ.filter (fun j : Fin n => displacement p.symm j < 0) := by
      simpa only [Finset.singleton_subset_iff,Finset.mem_filter,Finset.mem_univ,true_and,hneg] using (show (-1 : ℤ)<0 by omega)
    have hcap := AffineLift.original_selected_negative_residual hd.1 hmaj
      (Function.Embedding.refl (Fin n)) (displacement p.symm) (fun _ => rfl) hd.1 {i} hsub
    rw [Finset.card_sdiff_of_subset hsub,hN] at hcap
    simp only [Finset.sum_singleton,Finset.card_singleton,hi] at hcap
    rw [hsubcast,hn] at hcap
    nlinarith only [he,hcap]

/-- Equality of the isolated and fixed counts leaves no fixed point inside
any nontrivial physical component. -/
theorem component_support_of_all_fixed_isolated (p : State n)
    (hfixed : isolatedVertices p=p.supportᶜ) (root : Fin n)
    (hc : 2 ≤ (componentSet p root).card) : componentSet p root ⊆ p.support := by
  classical
  intro i hi
  by_contra hnot
  have hiso : i ∈ isolatedVertices p := by rw [hfixed]; exact Finset.mem_compl.mpr hnot
  have hcard := (mem_isolated_vertices p i).mp hiso
  have he : componentSet p root=componentSet p i :=
    CycleFootprint.component_eq_of_path _ ((CycleFootprint.mem_component _ _ _).mp hi)
  rw [he] at hc
  omega

/-- In an unpaid epsilon=1,f=2 peak with U>=3, the bridge count forces
all fixed positions to be isolated. Both rigidity hypotheses hold on every
nontrivial actual component. -/
theorem two_component_unit_energy_high_peak_structure (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm)) (hmax : MaximalZeroCut p)
    (hc : (componentRoots p).card=1+1) (hpos : 1 ≤ peakExcess p hc)
    (hf : n-p.support.card=2)
    (he : ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)=1)
    (hU : 3 ≤ sourceHalfPeak p) :
    bridgeBudget (componentBridges p hc)=2 ∧ isolatedVertices p=p.supportᶜ ∧
    ∀ root : Fin n, 2 ≤ (componentSet p root).card →
      ∀ i ∈ componentSet p root, 2 ≤ |displacement p.symm i| := by
  classical
  have hsub : isolatedVertices p ⊆ p.supportᶜ := by
    intro i hi
    exact Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (isolated_vertex_fixed p i hi))
  have hcard : p.supportᶜ.card=2 := by simpa only [Finset.card_compl,Fintype.card_fin] using hf
  have ha : (isolatedVertices p).card ≤ 2 := by
    have hh := Finset.card_le_card hsub
    omega
  have hB := two_component_twice_bridge_budget hn p hmax hc
  have hact := unpaid_two_component_activity hn p hmaj hmax hc hpos
  have hn4 := unit_energy_reserve_size_mod_four p he
  have hp : n%2=0 := by omega
  dsimp only at hact
  rw [he,hf,hp] at hact
  have hBeq : bridgeBudget (componentBridges p hc)=2 := by omega
  have haeq : (isolatedVertices p).card=2 := by omega
  have hfixed : isolatedVertices p=p.supportᶜ := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨hBeq,hfixed,?_⟩
  intro root hroot i hi
  have him := component_support_of_all_fixed_isolated p hfixed root hroot hi
  have hmove : p.symm i ≠ i := (mem_support_inverse p i).mp him
  have hnon : displacement p.symm i ≠ 0 := by
    intro hz
    apply hmove
    apply Fin.ext
    unfold displacement at hz
    omega
  have hunit := unit_energy_two_fixed_no_unit_arrow p hmaj hf he i
  have hapos := abs_pos.mpr hnon
  omega

#print axioms unit_energy_two_fixed_sign_counts
#print axioms unit_energy_two_fixed_no_unit_arrow
#print axioms component_support_of_all_fixed_isolated
#print axioms two_component_unit_energy_high_peak_structure
end LRX.FiniteCuts
