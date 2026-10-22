import LRX.ContractionCutCounts

namespace LRX.ContractionBlocks
open scoped BigOperators
variable {m : ℕ}

/-- Rank coordinates with nonnegative physical holes between consecutive ranks. -/
def position (holes : Fin m → ℤ) (x : Fin (m+1)) : ℤ :=
  (x : ℤ)+∑ j, if j.val < x.val then holes j else 0

theorem position_difference (holes : Fin m → ℤ) (x y : Fin (m+1)) (hxy : x ≤ y) :
    position holes y-position holes x = (y : ℤ)-(x : ℤ)+
      ∑ j, if x.val ≤ j.val ∧ j.val < y.val then holes j else 0 := by
  have he : ∀ j : Fin m,
      (if j.val < y.val then holes j else 0)-(if j.val < x.val then holes j else 0)=
        if x.val ≤ j.val ∧ j.val < y.val then holes j else 0 := by
    intro j
    have hv : x.val ≤ y.val := hxy
    split_ifs <;> omega
  unfold position
  rw [show (y : ℤ)+(∑ j, if j.val < y.val then holes j else 0)-
      ((x : ℤ)+(∑ j, if j.val < x.val then holes j else 0)) =
      (y : ℤ)-(x : ℤ)+((∑ j, if j.val < y.val then holes j else 0)-
        (∑ j, if j.val < x.val then holes j else 0)) by ring]
  simp only [← Finset.sum_sub_distrib,he]

theorem position_mono (holes : Fin m → ℤ) (hholes : ∀ j, 0 ≤ holes j) :
    Monotone (position holes) := by
  intro x y hxy
  have he := position_difference holes x y hxy
  have hs : (0 : ℤ) ≤ ∑ j, if x.val ≤ j.val ∧ j.val < y.val then holes j else 0 := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> simp [hholes]
  have hv : x.val ≤ y.val := hxy
  omega

/-- Every increasing integer placement has this form up to translation. -/
theorem placement_from_holes (f : Fin (m+1) → ℤ) :
    ∀ x : Fin (m+1),
      position (fun j : Fin m => f j.succ-f j.castSucc-1) x=f x-f 0 := by
  intro x
  induction x using Fin.induction with
  | zero => simp [position]
  | succ i ih =>
    have hd := position_difference (fun j : Fin m => f j.succ-f j.castSucc-1)
      i.castSucc i.succ (by simp [Fin.le_def])
    have hs : (∑ j : Fin m, if i.castSucc.val ≤ j.val ∧ j.val < i.succ.val
        then f j.succ-f j.castSucc-1 else 0)=f i.succ-f i.castSucc-1 := by
      have hp : ∀ j : Fin m, i.castSucc.val ≤ j.val ∧ j.val < i.succ.val ↔ j=i := by
        intro j
        simp only [Fin.val_castSucc,Fin.val_succ]
        constructor
        · intro h; apply Fin.ext; omega
        · intro h; subst j; omega
      simp only [hp]
      simp
    rw [hs] at hd
    simp only [Fin.val_castSucc,Fin.val_succ,Nat.cast_add,Nat.cast_one] at hd
    omega

#print axioms placement_from_holes
end LRX.ContractionBlocks
