import LRX.BufferProgram

/-! Compile any signed integer buffer displacement into paid moves. This is an
executable construction for arbitrary distances, with exact logical and physical
semantics. The head ledger accounts for all nested operations. -/
namespace LRX.BufferProgram
open scoped BigOperators
variable {n : ℕ}

def shift (t : Logical n) (d : ℤ) : Logical n :=
  ⟨t.buffer, Function.update t.coord t.buffer (t.coord t.buffer+d), t.head+d⟩

@[simp] theorem shift_zero (t : Logical n) : shift t 0 = t := by
  cases t
  simp [shift]

@[simp] theorem shift_shift (t : Logical n) (a b : ℤ) :
    shift (shift t a) b = shift t (a+b) := by
  simp [shift, add_assoc]

theorem logical_forward (t : Logical n) : logicalStep .forward t = shift t 1 := rfl

theorem logical_backward (t : Logical n) : logicalStep .backward t = shift t (-1) := by
  simp [logicalStep, shift, sub_eq_add_neg]

theorem run_forward (k : ℕ) (t : Logical n) :
    logicalRun (List.replicate k (.forward : Command n)) t = shift t (k : ℤ) := by
  induction k generalizing t with
  | zero => simp [logicalRun]
  | succ k ih =>
    rw [List.replicate_succ, logicalRun, logical_forward, ih, shift_shift]
    congr 1
    omega

theorem run_backward (k : ℕ) (t : Logical n) :
    logicalRun (List.replicate k (.backward : Command n)) t = shift t (-(k : ℤ)) := by
  induction k generalizing t with
  | zero => simp [logicalRun]
  | succ k ih =>
    rw [List.replicate_succ, logicalRun, logical_backward, ih, shift_shift]
    congr 1
    omega

def move (d : ℤ) : List (Command n) :=
  if 0 ≤ d then List.replicate d.natAbs .forward else List.replicate d.natAbs .backward

theorem move_valid (d : ℤ) (t : Logical n) : Valid (move (n := n) d) t := by
  have hf (k : ℕ) (s : Logical n) : Valid (List.replicate k (.forward : Command n)) s := by
    induction k generalizing s with
    | zero => trivial
    | succ k ih => exact ⟨True.intro, ih _⟩
  have hb (k : ℕ) (s : Logical n) : Valid (List.replicate k (.backward : Command n)) s := by
    induction k generalizing s with
    | zero => trivial
    | succ k ih => exact ⟨True.intro, ih _⟩
  unfold move
  split <;> first | exact hf _ _ | exact hb _ _

theorem run_move (d : ℤ) (t : Logical n) : logicalRun (move (n := n) d) t = shift t d := by
  unfold move
  split_ifs with hd
  · rw [run_forward, Int.natCast_natAbs, abs_of_nonneg hd]
  · rw [run_backward, Int.natCast_natAbs, abs_of_nonpos (by omega : d ≤ 0), neg_neg]

/-- Exact physical implementation of an arbitrary signed logical motion. -/
theorem move_correct [NeZero n] (hn : 2 ≤ n) (d : ℤ)
    {s : LiftedModel.Configuration n} {t : Logical n} (hm : Matches s t) :
    Matches (LiftedModel.run (compile (move (n := n) d)) s) (shift t d) := by
  have h := compile_correct hn (move (n := n) d) hm (move_valid d t)
  simpa only [run_move] using h

theorem move_rotation_price (d : ℤ) : rotations (compile (move (n := n) d)) = d.natAbs := by
  rw [rotations_compile]
  unfold move
  split <;> simp [rotationCost]

theorem move_exchange_price (d : ℤ) : exchanges (compile (move (n := n) d)) = d.natAbs := by
  rw [exchanges_compile]
  unfold move
  split <;> simp

theorem move_length (d : ℤ) : (compile (move (n := n) d)).length = 2*d.natAbs := by
  rw [length_compile]
  unfold move
  split <;> simp [rotationCost, two_mul]

theorem sum_update (f : Fin n → ℤ) (b : Fin n) (z : ℤ) :
    ∑ i, Function.update f b z i = (∑ i, f i)-f b+z := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ b)]
  have h := Finset.sum_erase_add Finset.univ f (Finset.mem_univ b)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem step_head_ledger (c : Command n) (t : Logical n) :
    (logicalStep c t).head-t.head =
      (∑ i, (logicalStep c t).coord i) - ∑ i, t.coord i := by
  cases c <;> simp [logicalStep, sum_update]
  omega

/-- The change of the head is the sum of all token-coordinate changes. A nested
call therefore carries its entire subtree winding, not just its root cycle. -/
theorem head_ledger (cs : List (Command n)) (t : Logical n) :
    (logicalRun cs t).head-t.head = (∑ i, (logicalRun cs t).coord i) - ∑ i, t.coord i := by
  induction cs generalizing t with
  | nil => simp [logicalRun]
  | cons c cs ih =>
    have hs := step_head_ledger c t
    have ht := ih (logicalStep c t)
    change (logicalRun cs (logicalStep c t)).head-t.head =
      (∑ i, (logicalRun cs (logicalStep c t)).coord i) - ∑ i, t.coord i
    omega

#print axioms move_correct
#print axioms move_rotation_price
#print axioms head_ledger
end LRX.BufferProgram
