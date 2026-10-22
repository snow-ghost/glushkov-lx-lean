import LRX.WindowFamilySelectedEnergy

namespace LRX.FiniteCuts
variable {n : ℕ}

theorem fixed_count_selected_partition (p : State n) (S : Finset (Fin n)) :
    (S \ p.support).card+((S ∪ p.support)ᶜ).card = n-p.support.card := by
  classical
  have he : (S \ p.support) ∪ (S ∪ p.support)ᶜ = p.supportᶜ := by
    ext i
    simp only [Finset.mem_union,Finset.mem_sdiff,Finset.mem_compl]
    tauto
  have hd : Disjoint (S \ p.support) (S ∪ p.support)ᶜ := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_compl.mp hj) (Finset.mem_union.mpr (Or.inl (Finset.mem_sdiff.mp hi).1))
  have h := Finset.card_union_of_disjoint hd
  rw [he,Finset.card_compl,Fintype.card_fin] at h
  exact h.symm
end LRX.FiniteCuts

namespace LRX.FiniteWindow
open scoped BigOperators
open FiniteCuts
variable {n : ℕ}

/-- C9 for a real family of disjoint invariant windows. All counts refer to
actual selected positions and original fixed points, not free numeric data. -/
theorem window_family_area_deficit (As : List (FillingWindow n)) (p : State n)
    (hmaj : AffineLift.Majorized (displacement p))
    (hm : ∀ A ∈ As, A.Matches p) (hd : As.Pairwise FillingWindow.Apart) :
    let V := (As.map (fun A => A.size)).sum
    let a := ((familyPositions As ∪ p.support)ᶜ).card
    let f := n-p.support.card
    let ε := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p i|)
    (V : ℤ)^2-2*(As.map (fun A => (A.size : ℤ)^2)).sum+
      2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤
      2*(2*ε+(n%2 : ℕ)-(f : ℤ)) := by
  let S := familyPositions As
  let V := (As.map (fun A => A.size)).sum
  let a := ((S ∪ p.support)ᶜ).card
  let f := n-p.support.card
  let ε : ℤ := ((n/2 : ℕ) : ℤ)*((n : ℤ)-(n/2 : ℕ))-(∑ i, |displacement p i|)
  obtain ⟨hcard,hbalance,henergy⟩ := window_family_selected_energy As p hm hd
  have harea := balanced_subset_area_deficit p hmaj S hbalance
  have hfixed : ((S \ p.support).card : ℤ)+(a : ℤ) = (f : ℤ) := by
    exact_mod_cast fixed_count_selected_partition p S
  change S.card = V at hcard
  change ((S.card : ℤ)+(a : ℤ))^2 ≤
    4*(ε+(∑ i ∈ S, |displacement p i|))+(n%2 : ℕ) at harea
  rw [hcard] at harea
  change 2*(∑ i ∈ S, |displacement p i|)+((S \ p.support).card : ℤ) ≤
    (As.map (fun A => (A.size : ℤ)^2)).sum at henergy
  change (V : ℤ)^2-2*(As.map (fun A => (A.size : ℤ)^2)).sum+
    2*((V : ℤ)-1)*(a : ℤ)+(a : ℤ)^2+(n%2 : ℕ) ≤ 2*(2*ε+(n%2 : ℕ)-(f : ℤ))
  nlinarith

#print axioms window_family_area_deficit
end LRX.FiniteWindow
