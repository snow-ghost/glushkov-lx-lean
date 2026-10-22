import LRX.WindowReplacementRank
import LRX.TwoWindowInternalRoute

namespace LRX.FiniteWindow
open FiniteRankOrder
variable {n a b : ℕ} [NeZero n]

/-- Two actual complementary invariant fillings are below the product of their reversals. -/
theorem below_two_window_reversals (A : Window n a) (B : Window n b)
    (hA : A.offset=0) (hadj : B.offset=A.offset+a) (hcover : B.offset+b=n)
    (p : State n) (f : State a) (g : State b)
    (hf : ∀ i, p (embed A i)=embed A (f i))
    (hg : ∀ i, p (embed B i)=embed B (g i)) :
    Below p (permutation A Fin.revPerm*permutation B Fin.revPerm) := by
  have hab (i : Fin n) (hi : Contains A i) : ¬Contains B i := by
    unfold Contains at hi ⊢
    omega
  have hba (i : Fin n) (hi : Contains B i) : ¬Contains A i := by
    unfold Contains at hi ⊢
    omega
  let P := replace A p f Fin.revPerm
  have hgP : ∀ i, P (embed B i)=embed B (g i) := by
    intro i
    dsimp only [P]
    rw [replace_outside A p f Fin.revPerm (embed B i) (hba _ (contains_embed B i)),hg]
  let Q := replace B P g Fin.revPerm
  have hQ : Q=permutation A Fin.revPerm*permutation B Fin.revPerm := by
    apply Equiv.ext
    intro i
    by_cases hi : Contains A i
    · have hout := hab i hi
      obtain ⟨j,rfl⟩ := (contains_iff A i).mp hi
      dsimp only [Q]
      rw [replace_outside B P g Fin.revPerm _ hout]
      dsimp only [P]
      rw [replace_embed A p f Fin.revPerm hf,
        Equiv.Perm.mul_apply,permutation_outside B Fin.revPerm _ hout,permutation_embed]
    · have hiB : Contains B i := by
        unfold Contains at hi ⊢
        have := i.isLt
        omega
      obtain ⟨j,rfl⟩ := (contains_iff B i).mp hiB
      dsimp only [Q]
      rw [replace_embed B P g Fin.revPerm hgP,Equiv.Perm.mul_apply,permutation_embed,
        permutation_outside A Fin.revPerm _ (hba _ (contains_embed B _))]
  have h1 := below_reversal_replacement A p f hf
  have h2 := below_reversal_replacement B P g hgP
  have h := below_trans h1 h2
  rwa [show replace B P g Fin.revPerm=Q from rfl,hQ] at h

/-- The internal two-block word now uses an actual target and its two fillings. -/
theorem two_block_internal_word (hn : 2 ≤ n) (A : Window n a) (B : Window n b)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hA : A.offset=0)
    (hadj : B.offset=A.offset+a) (hcover : B.offset+b=n)
    (p : State n) (f : State a) (g : State b)
    (hf : ∀ i, p (embed A i)=embed A (f i))
    (hg : ∀ i, p (embed B i)=embed B (g i)) :
    ∃ w : List Letter,
      eval w=(RotationWords.rotation (⟨A.offset+(a-1)/2,by have := A.fits; omega⟩ : Fin n))⁻¹*p*
        RotationWords.rotation (⟨B.offset+(b/2-1),by have := B.fits; omega⟩ : Fin n) ∧
      (w.length : ℤ) ≤ (FiniteCuts.inversionNumber p : ℤ)+(a.choose 2 : ℤ)+(b.choose 2 : ℤ) :=
  two_window_internal_word hn A B ha hb hadj p (below_two_window_reversals A B hA hadj hcover p f g hf hg)

#print axioms below_two_window_reversals
#print axioms two_block_internal_word
end LRX.FiniteWindow
