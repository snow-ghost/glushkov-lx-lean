import LRX.LoadComponentPartition
import LRX.LargeComponentCrossReserve

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n : ℕ} [NeZero n]

def suffixVertices (n L : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => L ≤ i.val)

@[simp] theorem mem_suffix_vertices (L : ℕ) (i : Fin n) :
    i ∈ suffixVertices n L ↔ L ≤ i.val := by simp [suffixVertices]

noncomputable def suffixComponents (p : State n) (L : ℕ) : Finset (Finset (Fin n)) :=
  CycleFootprint.componentBlocks (displacement p.symm) (suffixVertices n L)

theorem invariant_suffix_closed (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    ∀ a ∈ suffixVertices n L, ∀ b,
      CycleFootprint.LoadPath (displacement p.symm) a b → b ∈ suffixVertices n L := by
  intro a ha b hp
  rw [mem_suffix_vertices] at ha ⊢
  by_cases hL : L = 0
  · omega
  · let r : Fin n := ⟨L-1,by omega⟩
    have hz : portLoad (displacement p.symm) r = 0 :=
      invariant_cut_port_zero p L (by omega) hLn hcut
    have hs := zero_port_path_side p r hz hp
    have hr : r.val = L-1 := rfl
    omega

theorem suffix_vertices_image (L : ℕ) (hLn : L ≤ n) :
    suffixVertices n L = Finset.univ.image
      (fun i : Fin (n-L) => (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)) := by
  ext i
  simp only [mem_suffix_vertices,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · intro hi
    refine ⟨⟨i.val-L,by have := i.isLt; omega⟩,?_⟩
    apply Fin.ext
    dsimp
    omega
  · rintro ⟨j,rfl⟩
    exact Nat.le_add_right _ _

theorem sum_suffix_vertices (L : ℕ) (hLn : L ≤ n) (g : Fin n → ℤ) :
    (∑ i ∈ suffixVertices n L, g i) =
      ∑ i : Fin (n-L), g ⟨L+i.val,by have := i.isLt; omega⟩ := by
  rw [suffix_vertices_image L hLn]
  apply Finset.sum_image
  intro i _ j _ hij
  apply Fin.ext
  have h := congrArg Fin.val hij
  dsimp at h
  omega

theorem suffix_components_capacity (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    (∑ i : Fin (n-L), (((componentSet p (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)).card : ℤ)-1)) =
      2 * ∑ C ∈ suffixComponents p L, (C.card.choose 2 : ℤ) := by
  have h := CycleFootprint.component_blocks_capacity_sum (displacement p.symm)
    (suffixVertices n L) (invariant_suffix_closed p L hLn hcut)
  rw [sum_suffix_vertices L hLn] at h
  exact h

/-- The cross reserve in component form, derived from the original large-component input. -/
theorem large_component_reserve_by_sizes (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hm : 2 ≤ (componentRoots p).card) (a : Fin n)
    (hlarge : (n+1)/2 < (componentSet p a).card) :
    let q := localTarget p 0 (componentLeft p a)
    let L := (componentSet p a).card
    ((positiveSourceFamily q n).map FillingWindow.deficit).sum + 1 +
      ((n-L).choose 2 : ℤ) - (∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let q := localTarget p 0 (componentLeft p a)
  let L := (componentSet p a).card
  have hLn : L ≤ n := (component_card_lt_of_multiple_roots p hm a).le
  have hcut := (component_recenter_cut p a).1
  have hcap := suffix_components_capacity q L hLn hcut
  have h := large_component_cross_reserve hn p hmaj hm a hlarge
  change 2*(((positiveSourceFamily q n).map FillingWindow.deficit).sum+1) +
    2*((n-L).choose 2 : ℤ) -
    (∑ i : Fin (n-L), (((componentSet q (⟨L+i.val,by have := i.isLt; omega⟩ : Fin n)).card : ℤ)-1)) ≤ _ at h
  rw [hcap] at h
  change ((positiveSourceFamily q n).map FillingWindow.deficit).sum+1+
    ((n-L).choose 2 : ℤ)-(∑ C ∈ suffixComponents q L, (C.card.choose 2 : ℤ)) ≤ _
  linarith

#print axioms suffix_components_capacity
#print axioms large_component_reserve_by_sizes
end LRX.FiniteCuts
