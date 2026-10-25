import LRX.TwoFixedMatchingGeometry
import Mathlib

namespace LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem two_fixed_pair_endpoint_sum (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val)
    (a b : Fin n) (hab : a.val < b.val) (hpab : p a=b) : a.val+b.val=n := by
  have habt := no_adjacent_pair_straddles_fixed p hinv hnc t hfixed hnoadj a b hab hpab
  have hpba : p b=a := by rw [← hpab]; exact hinv a
  have hp0 : p 0=0 := (hfixed 0).mpr (Or.inl rfl)
  have ha0 : a ≠ 0 := by
    intro h
    have heq := hpab
    rw [h,hp0] at heq
    have hv := congrArg Fin.val heq
    have hv' := congrArg Fin.val h
    change 0=b.val at hv
    change a.val=0 at hv'
    omega
  have ha0v : 0<a.val := by have hne : a.val ≠ 0 := fun h => ha0 (Fin.ext h); omega
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
  have leftside (x : Fin n) (hx0 : 0<x.val) (hxa : x.val<a.val) : b.val < (p x).val := by
    have hs := side x (moved x hx0 (by omega))
    have hpgt : a.val < (p x).val := by omega
    have hne : (p x).val ≠ b.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpab.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    exact hnc x a (p x) b hxa hpgt (by omega) rfl hpab
  have rightside (y : Fin n) (hby : b.val<y.val) : (p y).val < a.val := by
    have hs := side y (moved y (by omega) (by omega))
    have hplt : (p y).val < b.val := by omega
    have hne : (p y).val ≠ a.val := by
      intro h
      have he := p.injective ((Fin.ext h).trans hpba.symm)
      have := congrArg Fin.val he
      omega
    by_contra h
    exact hnc a (p y) b y (by omega) hplt hby hpab (hinv y)
  have hcard : (Finset.Ioo (0 : Fin n) a).card=(Finset.Ioi b).card := by
    refine Finset.card_bij (fun x _ => p x) ?_ ?_ ?_
    · intro x hx
      have hh := Finset.mem_Ioo.mp hx
      apply Finset.mem_Ioi.mpr
      exact leftside x hh.1 hh.2
    · intro x hx y hy hxy
      exact p.injective hxy
    · intro y hy
      have hby : b<y := Finset.mem_Ioi.mp hy
      have hs := rightside y hby
      have hpne : p y ≠ 0 := by
        intro h
        have hy0 := p.injective (h.trans hp0.symm)
        have hv := congrArg Fin.val hy0
        change y.val=0 at hv
        change b.val<y.val at hby
        omega
      have hpv : (p y).val ≠ 0 := fun h => hpne (Fin.ext h)
      refine ⟨p y,Finset.mem_Ioo.mpr ⟨?_,hs⟩,hinv y⟩
      change 0 < (p y).val
      omega
  rw [Fin.card_Ioo,Fin.card_Ioi,Fin.val_zero] at hcard
  have := b.isLt
  omega

/-- The even equality matching, cut at a fixed point, is circular reflection. -/
theorem two_fixed_matching_reflection (p : State n) (hinv : Function.Involutive p)
    (hnc : NoncrossingPairs p) (t : Fin n) (ht : 0<t.val)
    (hfixed : ∀ i, p i=i ↔ i=0 ∨ i=t)
    (hnoadj : ∀ i : Fin n, i.val+1 ≠ (p i).val) :
    ∀ i : Fin n, i ≠ 0 → i.val+(p i).val=n := by
  have hmid := two_fixed_matching_midpoint p hinv hnc t ht hfixed hnoadj
  intro i hi
  by_cases hit : i=t
  · subst i
    rw [(hfixed t).mpr (Or.inr rfl)]
    omega
  · have hm : p i ≠ i := by
      intro h
      rcases (hfixed i).mp h with h | h
      · exact hi h
      · exact hit h
    have hne : (p i).val ≠ i.val := fun h => hm (Fin.ext h)
    by_cases hlt : i.val < (p i).val
    · exact two_fixed_pair_endpoint_sum p hinv hnc t hfixed hnoadj i (p i) hlt rfl
    · have h := two_fixed_pair_endpoint_sum p hinv hnc t hfixed hnoadj (p i) i (by omega) (hinv i)
      omega

#print axioms two_fixed_pair_endpoint_sum
#print axioms two_fixed_matching_reflection
end LRX.FiniteCuts
