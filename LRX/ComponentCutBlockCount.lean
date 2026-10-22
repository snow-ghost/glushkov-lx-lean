import LRX.ComponentCutSingletonCount

namespace LRX.FiniteCuts
open RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n k : ℕ} [NeZero n]

theorem component_cut_component_image (p : State n) (root i : Fin n) :
    (componentSet (localTarget p 0 (componentLeft p root)) i).image
      (fun x => x+componentLeft p root) = componentSet p (i+componentLeft p root) := by
  classical
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hz := component_left_port_zero p root
  have hd : AffineLift.IsLift p ((0 : Fin n) : ℤ) (displacement p.symm) := by
    simpa only [Fin.val_zero,Nat.cast_zero,Equiv.symm_symm] using canonical_lift p.symm
  have hcan := phase_zero_cut_canonical 0 (componentLeft p root-1) hd hz
  have hr : componentLeft p root-1+1=r := by dsimp [r]; ring
  rw [hr] at hcan
  have hpath (x : Fin n) : x ∈ componentSet q i ↔ x+r ∈ componentSet p (i+r) := by
    simp only [componentSet,CycleFootprint.mem_component]
    rw [← hcan]
    exact load_path_recenter _ r i x
  change (componentSet q i).image (fun x => x+r)=componentSet p (i+r)
  ext j
  constructor
  · intro hj
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hj
    exact (hpath x).mp hx
  · intro hj
    apply Finset.mem_image.mpr
    refine ⟨j-r,?_,sub_add_cancel j r⟩
    apply (hpath _).mpr
    simpa only [sub_add_cancel] using hj

theorem component_cut_nontrivial_count (p : State n) (root : Fin n) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root)) 0).card =
      (nontrivialSuffixComponents p 0).card := by
  classical
  let r := componentLeft p root
  let q := localTarget p 0 r
  have hinj : Function.Injective (fun x : Fin n => x+r) := fun _ _ h => add_right_cancel h
  change (nontrivialSuffixComponents q 0).card = _
  apply Finset.card_bij (fun C _ => C.image (fun x => x+r))
  · intro C hC
    obtain ⟨hC,hsize⟩ := Finset.mem_filter.mp hC
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hC
    change (componentSet q i).image (fun x => x+r) ∈ nontrivialSuffixComponents p 0
    rw [component_cut_component_image]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨i+r,by simp,rfl⟩,?_⟩
    have hh := (component_recenter_cut p root).2 i
    change (componentSet q i).card = (componentSet p (i+r)).card at hh
    change 2 ≤ (componentSet q i).card at hsize
    change 2 ≤ (componentSet p (i+r)).card
    omega
  · intro C _ D _ he
    exact Finset.image_injective hinj he
  · intro D hD
    obtain ⟨hD,hsize⟩ := Finset.mem_filter.mp hD
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hD
    refine ⟨componentSet q (j-r),?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_image.mpr ⟨j-r,by simp,rfl⟩,?_⟩
      have hh := (component_recenter_cut p root).2 (j-r)
      change (componentSet q (j-r)).card = (componentSet p (j-r+r)).card at hh
      rw [sub_add_cancel] at hh
      change 2 ≤ (componentSet p j).card at hsize
      omega
    · rw [component_cut_component_image]
      simp only [r,sub_add_cancel]
      rfl

/-- The exterior count t at the component cut equals the number of bridges
in the original routed map. -/
theorem component_cut_external_count (p : State n) (root : Fin n)
    (hsize : 2 ≤ (componentSet p root).card) :
    (nontrivialSuffixComponents (localTarget p 0 (componentLeft p root))
      (componentSet p root).card).card+1 = (componentRoots p).card := by
  let r := componentLeft p root
  let q := localTarget p 0 r
  let L := (componentSet p root).card
  have hzero : (componentSet q 0).card=L := by
    have hh := (component_recenter_cut p root).2 0
    simp only [zero_add] at hh
    have he : componentSet p root=componentSet p r :=
      CycleFootprint.component_eq_of_path _ (component_left_path p root)
    change (componentSet q 0).card=(componentSet p r).card at hh
    rwa [← he] at hh
  have hc := prefix_component_root_count q L (by omega)
    (fun i => by rw [zero_component_prefix,hzero])
  have hcounts := component_cut_nontrivial_count p root
  rw [component_roots_card_eq_blocks] at hc ⊢
  change (nontrivialSuffixComponents q 0).card = (nontrivialSuffixComponents p 0).card at hcounts
  change (nontrivialSuffixComponents q L).card+1 = _
  omega

/-- Both bridge hypotheses of the scalar cutoff, with actual normalized a,t
and a real bridge certificate for the original maximal-cut map. -/
theorem maximal_cut_component_bridge_bounds (hn : 2 ≤ n) (p : State n)
    (hmax : MaximalZeroCut p) (hm : 2 ≤ (componentRoots p).card)
    (root : Fin n) (hsize : 2 ≤ (componentSet p root).card) :
    let q := localTarget p 0 (componentLeft p root)
    let L := (componentSet p root).card
    let t := (nontrivialSuffixComponents q L).card
    let a : ℤ := (singletonSuffixComponents q L).card
    ∃ hc : (componentRoots p).card=t+1,
      let B : ℤ := bridgeBudget (componentBridges p hc)
      (a=0 → B ≤ (t : ℤ)) ∧ (1 ≤ a → B ≤ a+(t : ℤ)-1) := by
  dsimp only
  have hcount := component_cut_external_count p root hsize
  refine ⟨hcount.symm,?_⟩
  exact maximal_bridge_bounds_at_component_cut hn p hmax hcount.symm (by omega) root hsize

#print axioms maximal_cut_component_bridge_bounds
#print axioms component_cut_nontrivial_count
#print axioms component_cut_external_count
end LRX.FiniteCuts
