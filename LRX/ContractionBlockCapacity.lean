import LRX.ContractionArrowSigns
import LRX.FiniteCoordinateCapacity

namespace LRX.ContractionBlocks.System
open scoped BigOperators
variable {m k : ℕ} {P : State m} {q : State k}

def labels (B : System P q) (i : Fin k) : Finset (Fin m) := (B.nodes i).toFinset

theorem labels_nonempty (B : System P q) (i : Fin k) : (B.labels i).Nonempty :=
  ⟨B.firstLabel i, List.mem_toFinset.mpr (List.head_mem (B.nonempty i))⟩

theorem labels_interval (B : System P q) (i : Fin k) :
    B.labels i = Finset.Icc ((B.labels i).min' (B.labels_nonempty i))
      ((B.labels i).max' (B.labels_nonempty i)) := by
  ext x
  rw [Finset.mem_Icc]
  constructor
  · intro hx
    exact ⟨Finset.min'_le _ _ hx,Finset.le_max' _ _ hx⟩
  · intro hx
    apply List.mem_toFinset.mpr
    exact B.block_interval i _ _ x
      (List.mem_toFinset.mp (Finset.min'_mem _ _))
      (List.mem_toFinset.mp (Finset.max'_mem _ _)) hx.1 hx.2

/-- Coordinates of every block occupy exactly an integer interval of its
cardinality. This fact follows from the path system, rather than being assumed. -/
theorem labels_coordinates (B : System P q) (i : Fin k) :
    ∃ lo : ℤ, ∀ x ∈ B.labels i, lo ≤ (x : ℤ) ∧ (x : ℤ) < lo+(B.labels i).card := by
  let l := (B.labels i).min' (B.labels_nonempty i)
  let u := (B.labels i).max' (B.labels_nonempty i)
  have hc : (B.labels i).card=u.val+1-l.val := by
    conv_lhs => rw [B.labels_interval i]
    exact Fin.card_Icc _ _
  have hlu : l.val ≤ u.val := by
    change l ≤ u
    exact Finset.min'_le _ _ (Finset.max'_mem _ _)
  refine ⟨(l : ℤ),?_⟩
  intro x hx
  have hl : l.val ≤ x.val := Finset.min'_le _ _ hx
  have hu : x.val ≤ u.val := Finset.le_max' _ _ hx
  constructor <;> omega

/-- Distinct sources and targets in one block give the exact subset capacity
used in the rank-length estimate (29). -/
theorem block_difference_capacity (B : System P q) (i : Fin k) (S : Finset (Fin m))
    (hsel : S ⊆ B.selected) (hblock : S ⊆ B.labels i) :
    (∑ x ∈ S, ((P x : ℤ)-(x : ℤ))) ≤ (S.card : ℤ)*((B.labels i).card-S.card) := by
  obtain ⟨lo,hlo⟩ := B.labels_coordinates i
  have ht : ∀ x ∈ S, P x ∈ B.labels i := by
    intro x hx
    exact List.mem_toFinset.mpr (B.selected_target_in_block i x
      (List.mem_toFinset.mp (hblock hx)) (hsel hx))
  have hf : Function.Injective (fun x : Fin m => (x : ℤ)-lo) := by
    intro x y he
    change (x : ℤ)-lo=(y : ℤ)-lo at he
    apply Fin.ext
    have hv : (x : ℤ)=(y : ℤ) := by omega
    exact_mod_cast hv
  have hg : Function.Injective (fun x : Fin m => (P x : ℤ)-lo) := hf.comp P.injective
  have hc := FiniteCoordinates.sum_coordinate_difference S
    (fun x => (x : ℤ)-lo) (fun x => (P x : ℤ)-lo) ((B.labels i).card : ℤ)
    hf.injOn hg.injOn (fun x hx => by have := (hlo x (hblock hx)).1; omega)
    (fun x hx => by have := (hlo (P x) (ht x hx)).2; omega)
  simpa only [sub_sub_sub_cancel_right] using hc

theorem block_reverse_difference_capacity (B : System P q) (i : Fin k) (S : Finset (Fin m))
    (hsel : S ⊆ B.selected) (hblock : S ⊆ B.labels i) :
    (∑ x ∈ S, ((x : ℤ)-(P x : ℤ))) ≤ (S.card : ℤ)*((B.labels i).card-S.card) := by
  obtain ⟨lo,hlo⟩ := B.labels_coordinates i
  have ht : ∀ x ∈ S, P x ∈ B.labels i := by
    intro x hx
    exact List.mem_toFinset.mpr (B.selected_target_in_block i x
      (List.mem_toFinset.mp (hblock hx)) (hsel hx))
  have hf : Function.Injective (fun x : Fin m => (x : ℤ)-lo) := by
    intro x y he
    change (x : ℤ)-lo=(y : ℤ)-lo at he
    apply Fin.ext
    have hv : (x : ℤ)=(y : ℤ) := by omega
    exact_mod_cast hv
  have hg : Function.Injective (fun x : Fin m => (P x : ℤ)-lo) := hf.comp P.injective
  have hc := FiniteCoordinates.sum_coordinate_difference S
    (fun x => (P x : ℤ)-lo) (fun x => (x : ℤ)-lo) ((B.labels i).card : ℤ)
    hg.injOn hf.injOn (fun x hx => by have := (hlo (P x) (ht x hx)).1; omega)
    (fun x hx => by have := (hlo x (hblock hx)).2; omega)
  simpa only [sub_sub_sub_cancel_right] using hc

#print axioms block_difference_capacity
#print axioms block_reverse_difference_capacity
end LRX.ContractionBlocks.System
