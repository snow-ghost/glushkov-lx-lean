import LRX.TwoWindowRankUpper
import LRX.FiniteWindowRestriction

namespace LRX.FiniteCuts
open FiniteWindow
variable {n : ℕ} [NeZero n]

/-- The two fillings are extracted from the invariant cut itself. -/
theorem two_block_cut_internal_word (a : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ n-a)
    (p : State n) (hcut : ∀ i : Fin n, (p i).val < a ↔ i.val < a) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨(a-1)/2,by omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨a+((n-a)/2-1),by omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(a.choose 2 : ℤ)+((n-a).choose 2 : ℤ) := by
  let A : Window n a := ⟨0,by omega⟩
  let B : Window n (n-a) := ⟨a,by omega⟩
  have hA : ∀ i, Contains A i → Contains A (p i) := by
    intro i hi
    change 0 ≤ i.val ∧ i.val < 0+a at hi
    change 0 ≤ (p i).val ∧ (p i).val < 0+a
    have hp := (hcut i).mpr (by omega : i.val < a)
    constructor <;> omega
  have hB : ∀ i, Contains B i → Contains B (p i) := by
    intro i hi
    change a ≤ i.val ∧ i.val < a+(n-a) at hi
    change a ≤ (p i).val ∧ (p i).val < a+(n-a)
    have hs := hcut i
    have hn := (p i).isLt
    constructor <;> omega
  obtain ⟨f,hf⟩ := exists_restriction_of_inverse_closed A p.symm
    (by simpa only [Equiv.symm_symm] using hA)
  obtain ⟨g,hg⟩ := exists_restriction_of_inverse_closed B p.symm
    (by simpa only [Equiv.symm_symm] using hB)
  simp only [Equiv.symm_symm] at hf hg
  have h := two_block_internal_word (by omega) A B ha hb rfl (by dsimp [A,B]; omega) (by dsimp [B]; omega) p f g hf hg
  simpa only [A,B,Nat.zero_add] using h

#print axioms two_block_cut_internal_word
end LRX.FiniteCuts
