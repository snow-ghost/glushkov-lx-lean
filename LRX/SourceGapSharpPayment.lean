import LRX.SelectedSourceGapWord

namespace LRX.FiniteCuts
open scoped BigOperators
open FiniteWindow RotationWords
variable {n k : ℕ} [NeZero n]

theorem majorized_canonical_energy (p : State n)
    (hm : AffineLift.Majorized (displacement p.symm)) :
    (∑ i, |displacement p.symm i|) ≤ ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ)) := by
  have hd := canonical_lift p.symm
  have h := AffineLift.balanced_subset_energy hd.1 hm Finset.univ (by simpa using hd.1)
  simpa only [Finset.card_univ,Fintype.card_fin] using h

theorem choose_two_half_identity (n : ℕ) :
    (n.choose 2 : ℤ) = 2*((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ) := by
  have hc := twice_choose_two_int n
  have he : (n : ℤ) = 2*((n/2 : ℕ) : ℤ)+(n%2 : ℕ) := by omega
  have hp : n%2 = 0 ∨ n%2 = 1 := by omega
  rcases hp with hp | hp <;> rw [hp] at he <;> simp only [Nat.cast_zero,Nat.cast_one,add_zero] at he <;> nlinarith

/-- The extracted joint bridge reserve pays the actual internal-gap word. -/
theorem selected_source_gap_sharp_word (hn : 2 ≤ n) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (hc : (componentRoots p).card = k+1) (hk : 0 < k)
    (hreserve : ((positiveSourceFamily p n).map FillingWindow.deficit).sum+
      2*(bridgeBudget (componentBridges p hc) : ℤ)+1 ≤
      ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(n/2 : ℕ)-(inversionNumber p : ℤ))
    (u : {u // u ∈ positiveSourceGapStarts p n}) (start finish : Fin n)
    (hsu : u.val.val ≤ start.val) (hsv : start.val < FiniteGaps.next (sourcePackets p) u.val)
    (hfu : u.val.val ≤ finish.val) (hfv : finish.val < FiniteGaps.next (sourcePackets p) u.val) :
    ∃ w : List Letter, eval w = (rotation start)⁻¹*p*rotation finish ∧ w.length ≤ n.choose 2 := by
  obtain ⟨w,he,hl⟩ := selected_source_gap_word hn p hc hk u start finish hsu hsv hfu hfv
  have hmass := majorized_canonical_energy p hmaj
  have hchoose := choose_two_half_identity n
  have hlen : (w.length : ℤ) ≤ (n.choose 2 : ℤ) := by nlinarith
  exact ⟨w,he,by exact_mod_cast hlen⟩

#print axioms majorized_canonical_energy
#print axioms selected_source_gap_sharp_word
end LRX.FiniteCuts
