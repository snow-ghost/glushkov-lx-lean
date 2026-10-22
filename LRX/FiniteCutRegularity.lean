import LRX.FiniteCutLoad

/-! Moving a cut past one source and one target changes half-load by at most one. -/
namespace LRX.FiniteCuts
variable {b : ℕ}

theorem half_load_succ_upper (p : State b) (e : ℕ) (he : e < b) :
    halfLoad p (e+1) ≤ halfLoad p e+1 := by
  let k : Fin b := ⟨e,he⟩
  have hs : forward p (e+1) ⊆ insert k (forward p e) := by
    intro i hi
    obtain ⟨hleft, hright⟩ := (mem_forward p (e+1) i).mp hi
    by_cases hie : i.val < e
    · exact Finset.mem_insert_of_mem ((mem_forward p e i).mpr ⟨hie, by omega⟩)
    · have hik : i=k := Fin.ext (by dsimp [k]; omega)
      exact Finset.mem_insert.mpr (Or.inl hik)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

theorem half_load_succ_lower (p : State b) (e : ℕ) (he : e < b) :
    halfLoad p e ≤ halfLoad p (e+1)+1 := by
  let k : Fin b := ⟨e,he⟩
  have hs : forward p e ⊆ insert (p.symm k) (forward p (e+1)) := by
    intro i hi
    obtain ⟨hleft, hright⟩ := (mem_forward p e i).mp hi
    by_cases hpe : e+1 ≤ (p i).val
    · exact Finset.mem_insert_of_mem ((mem_forward p (e+1) i).mpr ⟨by omega, hpe⟩)
    · have hip : p i=k := Fin.ext (by dsimp [k]; omega)
      have hik : i=p.symm k := by rw [← hip, p.symm_apply_apply]
      exact Finset.mem_insert.mpr (Or.inl hik)
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)

theorem half_load_step (p : State b) (e : ℕ) (he : e < b) :
    |(halfLoad p (e+1) : ℤ)-(halfLoad p e : ℤ)| ≤ 1 := by
  have hu := half_load_succ_upper p e he
  have hl := half_load_succ_lower p e he
  rw [abs_le]
  omega

#print axioms half_load_step
end LRX.FiniteCuts
