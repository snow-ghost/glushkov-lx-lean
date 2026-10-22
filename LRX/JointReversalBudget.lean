import LRX.ReversalWindowFamily

namespace LRX.FiniteWindow
open FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Sum all local filling deficits before applying the global strict capacity.
Only the original map is required to be majorized. -/
theorem joint_reversal_strict_inversion_budget (hn : 2 ≤ n)
    (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p)
    (hapart : As.Pairwise FillingWindow.Apart)
    (hwidth : ∀ A ∈ As, A.size ≤ (n-1)/2)
    (hmaj : AffineLift.Majorized (displacement p))
    (a : Fin n) (hlarge : n-n/2 < (CycleFootprint.component (displacement p) a).card) :
    (As.map FillingWindow.deficit).sum + 1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ) := by
  let R := reverseWindows As p
  obtain ⟨hprice,hshort,hneg,hpos,hpaths⟩ := reverse_windows_spec As p hmatch hapart hwidth
    (FiniteWindow.majorized_short (canonical_lift p) hmaj)
  have hsubset : CycleFootprint.component (displacement p) a ⊆
      CycleFootprint.component (displacement R) a := by
    intro i hi
    exact (CycleFootprint.mem_component _ _ _).mpr
      (hpaths a i ((CycleFootprint.mem_component _ _ _).mp hi))
  have hc := Finset.card_le_card hsubset
  have hlargeR : n-n/2 < (CycleFootprint.component (displacement R) a).card := by omega
  have hcap := strict_capacity_of_large_component hn (canonical_lift p).1 hmaj
    (canonical_lift R) hshort hneg hpos a hlargeR
  have hend : (fun i : Fin n => (i : ℤ)+displacement R i) = (fun i => (R i : ℤ)) := by
    funext i
    unfold displacement
    omega
  rw [hend,canonical_inversion_count] at hcap
  change (inversionNumber R : ℤ) = _ at hprice
  omega

#print axioms joint_reversal_strict_inversion_budget
end LRX.FiniteWindow
