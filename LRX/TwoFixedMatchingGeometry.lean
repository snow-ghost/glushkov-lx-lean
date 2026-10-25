import LRX.LinearMatchingGeometry
import Mathlib

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- Without adjacent pairs, every pair must surround the second fixed point. -/
theorem no_adjacent_pair_straddles_fixed (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) :
    a.val < t.val ∧ t.val < b.val := by
  have hane : p a ≠ a := by rw [hpab]; intro h; have := congrArg Fin.val h; omega
  have hbne : p b ≠ b := by
    have hba : p b=a := by rw [← hpab]; exact hinv a
    rw [hba]; intro h; have := congrArg Fin.val h; omega
  have ha0 : a ≠ 0 := fun h => hane ((hfixed a).mpr (Or.inl h))
  have hat : a ≠ t := fun h => hane ((hfixed a).mpr (Or.inr h))
  have hbt : b ≠ t := fun h => hbne ((hfixed b).mpr (Or.inr h))
  have ha0v : a.val ≠ 0 := fun h => ha0 (Fin.ext h)
  have hatv : a.val ≠ t.val := fun h => hat (Fin.ext h)
  have hbtv : b.val ≠ t.val := fun h => hbt (Fin.ext h)
  by_contra h
  have hnofix : ∀ i : Fin n, a.val ≤ i.val → i.val ≤ b.val → p i ≠ i := by
    intro i hai hib hpi
    rcases (hfixed i).mp hpi with hi | hi
    · have hv := congrArg Fin.val hi
      change i.val=0 at hv
      omega
    · have hv := congrArg Fin.val hi
      omega
  obtain ⟨x,y,hx,hy,hxy,hp⟩ := noncrossing_pair_contains_adjacent p hinv hnc a b hab hpab hnofix
  exact hnoadj x (by rw [hp]; exact hxy)

/-- The two fixed vertices divide equal-sized arcs. -/
theorem two_fixed_matching_midpoint (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) : 2*t.val=n := by
  have hp0 : p 0=0 := (hfixed 0).mpr (Or.inl rfl)
  have moved (x : Fin n) (hx0 : 0<x.val) (hxt : x.val ≠ t.val) : p x ≠ x := by
    intro h
    rcases (hfixed x).mp h with h | h
    · have := congrArg Fin.val h; change x.val=0 at this; omega
    · exact hxt (congrArg Fin.val h)
  have side (x : Fin n) (hx : p x ≠ x) :
      (x.val < t.val ∧ t.val < (p x).val) ∨ ((p x).val < t.val ∧ t.val < x.val) := by
    have hne : (p x).val ≠ x.val := fun h => hx (Fin.ext h)
    by_cases hlt : x.val < (p x).val
    · exact Or.inl (no_adjacent_pair_straddles_fixed p hinv hnc t hfixed hnoadj x (p x) hlt rfl)
    · exact Or.inr (no_adjacent_pair_straddles_fixed p hinv hnc t hfixed hnoadj (p x) x (by omega) (hinv x))
  have hcard : (Finset.Ioo (0 : Fin n) t).card=(Finset.Ioi t).card := by
    refine Finset.card_bij (fun x _ => p x) ?_ ?_ ?_
    · intro x hx
      have hh := Finset.mem_Ioo.mp hx
      have hx0 : 0<x.val := hh.1
      have hxt : x.val<t.val := hh.2
      have hs := side x (moved x hx0 (by omega))
      apply Finset.mem_Ioi.mpr
      change t.val < (p x).val
      omega
    · intro x hx y hy hxy
      exact p.injective hxy
    · intro y hy
      have hty : t<y := Finset.mem_Ioi.mp hy
      change t.val<y.val at hty
      have hs := side y (moved y (by omega) (by omega))
      have hpne : p y ≠ 0 := by
        intro h
        have hy0 := p.injective (h.trans hp0.symm)
        have hv := congrArg Fin.val hy0
        change y.val=0 at hv
        omega
      have hpv : (p y).val ≠ 0 := fun h => hpne (Fin.ext h)
      refine ⟨p y,Finset.mem_Ioo.mpr ⟨?_,?_⟩,hinv y⟩
      · change 0 < (p y).val; omega
      · change (p y).val < t.val; omega
  rw [Fin.card_Ioo,Fin.card_Ioi,Fin.val_zero] at hcard
  have := t.isLt
  omega

#print axioms no_adjacent_pair_straddles_fixed
#print axioms two_fixed_matching_midpoint
end LRX.FiniteCuts
