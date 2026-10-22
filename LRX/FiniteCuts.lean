import LRX.Graph

/-! Real cut crossings of a finite permutation. Forward and backward crossings
balance, and the half-load is bounded by the two side capacities. -/
namespace LRX.FiniteCuts
variable {b : ℕ}

def left (e : ℕ) : Finset (Fin b) := Finset.univ.filter (fun i => i.val < e)

def targetLeft (p : State b) (e : ℕ) : Finset (Fin b) :=
  (left e).map p.symm.toEmbedding

def forward (p : State b) (e : ℕ) : Finset (Fin b) := left e \ targetLeft p e

def backward (p : State b) (e : ℕ) : Finset (Fin b) := targetLeft p e \ left e

def halfLoad (p : State b) (e : ℕ) : ℕ := (forward p e).card

@[simp] theorem mem_left (e : ℕ) (i : Fin b) : i ∈ left e ↔ i.val < e := by simp [left]

@[simp] theorem mem_target_left (p : State b) (e : ℕ) (i : Fin b) :
    i ∈ targetLeft p e ↔ (p i).val < e := by
  simp [targetLeft, Finset.mem_map_equiv]

@[simp] theorem mem_forward (p : State b) (e : ℕ) (i : Fin b) :
    i ∈ forward p e ↔ i.val < e ∧ e ≤ (p i).val := by
  simp [forward]

@[simp] theorem mem_backward (p : State b) (e : ℕ) (i : Fin b) :
    i ∈ backward p e ↔ (p i).val < e ∧ e ≤ i.val := by
  simp [backward]

theorem left_card (e : ℕ) (he : e ≤ b) : (left (b := b) e).card=e := by
  simpa only [left, Fin.card_filter_val_lt, min_eq_right he] using
    (Fin.card_filter_val_lt (n := b) (m := e))

theorem cut_balance (p : State b) (e : ℕ) : (forward p e).card=(backward p e).card := by
  apply Finset.card_sdiff_comm
  simp [targetLeft]

theorem half_load_capacity (p : State b) (e : ℕ) (he : e ≤ b) :
    halfLoad p e ≤ min e (b-e) := by
  have hleft : (forward p e).card ≤ e := by
    have h := Finset.card_le_card (Finset.sdiff_subset : forward p e ⊆ left e)
    simpa only [forward, left_card e he] using h
  have hs : (forward p e).image p ⊆ Finset.univ \ left (b := b) e := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, by
      simpa only [mem_left, not_lt] using (mem_forward p e i).mp hi |>.2⟩
  have hright := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ p.injective,
    Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Fintype.card_fin, left_card e he] at hright
  exact le_min hleft hright

@[simp] theorem half_load_zero (p : State b) : halfLoad p 0=0 := by
  have h := half_load_capacity p 0 (Nat.zero_le _)
  omega

@[simp] theorem half_load_end (p : State b) : halfLoad p b=0 := by
  have h := half_load_capacity p b le_rfl
  omega

#print axioms cut_balance
#print axioms half_load_capacity
end LRX.FiniteCuts
