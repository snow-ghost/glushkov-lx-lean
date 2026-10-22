import LRX.SuffixComponentWindowFamily
import LRX.SourceGapReversalFamily
import LRX.WindowFamilyAreaDeficit

namespace LRX.FiniteCuts
open FiniteWindow
open scoped BigOperators
variable {n : ℕ} [NeZero n]

/-- The actual internal positive gaps and exterior nontrivial components. -/
noncomputable def areaWindowFamily (p : State n) (L : ℕ) : List (FillingWindow n) :=
  positiveSourceFamily p L ++ suffixComponentFamily p L

theorem area_window_family_spec (p : State n) (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    (∀ A ∈ areaWindowFamily p L, A.Matches p.symm) ∧
      (areaWindowFamily p L).Pairwise FillingWindow.Apart := by
  obtain ⟨hm,hd,he,_⟩ := positive_source_family_spec p L
  obtain ⟨hm',hd',hs⟩ := suffix_component_family_spec p L hLn hcut
  constructor
  · intro A hA
    rcases List.mem_append.mp hA with h | h
    · exact hm A h
    · exact hm' A h
  · apply List.pairwise_append.mpr
    refine ⟨hd,hd',?_⟩
    intro A hA B hB i hi hj
    have ha := he A hA
    have hb := hs B hB
    unfold Contains at hi hj
    omega

/-- C9 with the window family extracted from the original map and cut. -/
theorem actual_window_area_deficit (p : State n)
    (hmaj : AffineLift.Majorized (displacement p.symm))
    (L : ℕ) (hLn : L ≤ n)
    (hcut : ∀ i : Fin n, (p i).val < L ↔ i.val < L) :
    let As := areaWindowFamily p L
    let V := (As.map (fun A => A.size)).sum
    let a := ((familyPositions As ∪ Equiv.Perm.support p.symm)ᶜ).card
    let f := n-(Equiv.Perm.support p.symm).card
    let ε := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p.symm i|)
    (V : ℤ)^2-2*(As.map (fun A => (A.size : ℤ)^2)).sum+
      2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
      2*(2*ε+(n%2 : ℕ)-(f : ℤ)) := by
  obtain ⟨hm,hd⟩ := area_window_family_spec p L hLn hcut
  exact window_family_area_deficit (areaWindowFamily p L) p.symm hmaj hm hd

#print axioms area_window_family_spec
#print axioms actual_window_area_deficit
end LRX.FiniteCuts
