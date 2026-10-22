import LRX.UniqueAdjacentReflection
import LRX.FiniteWindowRestriction

namespace LRX.FiniteCuts
variable {n b : ℕ}

/-- The reflection criterion applies to an invariant finite window, even with fixed points outside. -/
theorem window_unique_adjacent_reflection (p : State n) (W : FiniteWindow.Window n b)
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p)
    (hclosed : ∀ j, FiniteWindow.Contains W j → FiniteWindow.Contains W (p j))
    (hfixed : ∀ j, FiniteWindow.Contains W j → p j ≠ j)
    (hunique : ∀ a b : Fin n, a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin b, p (FiniteWindow.embed W i)=FiniteWindow.embed W i.rev := by
  obtain ⟨q,hmatch⟩ := FiniteWindow.exists_restriction_of_inverse_closed W p.symm
    (by simpa only [Equiv.symm_symm] using hclosed)
  simp only [Equiv.symm_symm] at hmatch
  have hinjq := FiniteWindow.embed_injective W
  have hqinv : Function.Involutive q := by
    intro i
    apply hinjq
    rw [← hmatch, ← hmatch, hinv]
  have hqnc : NoncrossingPairs q := by
    intro a b c d hab hbc hcd hac hbd
    have h1 : p (FiniteWindow.embed W a)=FiniteWindow.embed W c := by rw [hmatch,hac]
    have h2 : p (FiniteWindow.embed W b)=FiniteWindow.embed W d := by rw [hmatch,hbd]
    apply hnc (FiniteWindow.embed W a) (FiniteWindow.embed W b)
      (FiniteWindow.embed W c) (FiniteWindow.embed W d) ?_ ?_ ?_ h1 h2
    all_goals dsimp [FiniteWindow.embed]; omega
  have hqfixed : ∀ i, q i ≠ i := by
    intro i heq
    apply hfixed (FiniteWindow.embed W i) (FiniteWindow.contains_embed W i)
    rw [hmatch,heq]
  have hqunique : ∀ a b : Fin b, a.val+1=(q a).val → b.val+1=(q b).val → a=b := by
    intro a b ha hb
    apply hinjq
    apply hunique
    · rw [hmatch]
      dsimp [FiniteWindow.embed]
      omega
    · rw [hmatch]
      dsimp [FiniteWindow.embed]
      omega
  have href := unique_adjacent_matching_reflection q hqinv hqnc hqfixed hqunique
  intro i
  rw [hmatch,href]

/-- After cutting at the sole fixed point, the remaining matching is the linear reversal. -/
theorem sole_zero_fixed_matching_reflection (p : State (n+1))
    (hinv : Function.Involutive p) (hnc : NoncrossingPairs p) (hzero : p 0=0)
    (hfixed : ∀ i : Fin (n+1), p i=i → i=0)
    (hunique : ∀ a b : Fin (n+1), a.val+1=(p a).val → b.val+1=(p b).val → a=b) :
    ∀ i : Fin (n+1), i ≠ 0 → i.val+(p i).val=n+1 := by
  let W : FiniteWindow.Window (n+1) n := ⟨1,by omega⟩
  have hclosed : ∀ j, FiniteWindow.Contains W j → FiniteWindow.Contains W (p j) := by
    intro j hj
    have hjne : j ≠ 0 := by intro heq; subst j; change 1 ≤ 0 ∧ _ at hj; omega
    have hpne : p j ≠ 0 := by intro heq; exact hjne (p.injective (heq.trans hzero.symm))
    have hpval : (p j).val ≠ 0 := fun heq => hpne (Fin.ext heq)
    have hpbound := (p j).isLt
    change 1 ≤ (p j).val ∧ (p j).val < 1+n
    omega
  have hnfix : ∀ j, FiniteWindow.Contains W j → p j ≠ j := by
    intro j hj heq
    have hz := hfixed j heq
    subst j
    change 1 ≤ 0 ∧ _ at hj
    omega
  have href := window_unique_adjacent_reflection p W hinv hnc hclosed hnfix hunique
  intro i hi
  have hiv : i.val ≠ 0 := fun h => hi (Fin.ext h)
  have hiW : FiniteWindow.Contains W i := by
    change 1 ≤ i.val ∧ i.val < 1+n
    have := i.isLt
    omega
  obtain ⟨j,rfl⟩ := (FiniteWindow.contains_iff W i).mp hiW
  rw [href]
  dsimp [FiniteWindow.embed,W]
  have := j.isLt
  omega

#print axioms window_unique_adjacent_reflection
#print axioms sole_zero_fixed_matching_reflection
end LRX.FiniteCuts
