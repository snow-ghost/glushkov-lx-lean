import LRX.TwoBlockCutRoute

namespace LRX

theorem eval_inverse_word {n : ℕ} [NeZero n] (w : List Letter) :
    eval (w.reverse.map Letter.inverse)=(eval (n := n) w)⁻¹ := by
  simp only [eval,List.map_map,List.map_reverse,Function.comp_def,Letter.eval_inverse,List.prod_inv_reverse]

namespace FiniteCuts
variable {n : ℕ} [NeZero n]

/-- The opposite order through the same boundary has exactly the same price. -/
theorem two_block_cut_reverse_internal_word (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨a+((n-a)/2-1),by omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨(a-1)/2,by omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ) := by
  have hcutInv : ∀ i : Fin n, (p⁻¹ i).val < a ↔ i.val < a := by
    intro i
    have h := hcut (p⁻¹ i)
    simpa only [Equiv.Perm.inv_def,Equiv.apply_symm_apply] using h.symm
  obtain ⟨w,he,hl⟩ := two_block_cut_internal_word a ha hb p⁻¹ hcutInv
  refine ⟨w.reverse.map Letter.inverse,?_,?_⟩
  · rw [eval_inverse_word,he]
    simp only [mul_inv_rev,inv_inv,mul_assoc]
  · simp only [List.length_map,List.length_reverse]
    rwa [inversion_number_inverse] at hl

#print axioms two_block_cut_reverse_internal_word
end FiniteCuts
end LRX
