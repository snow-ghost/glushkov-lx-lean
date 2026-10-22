import LRX.TwoComponentBridgeWord
import LRX.FiniteLoadIntervals

namespace LRX.FiniteCuts
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Two distinct finite load components are ordered by any ordered pair of
representatives. Their actual extremal bridge and source packet give a literal
word, with no assumed arrow order, fixed gap or service coverage. -/
theorem separate_two_component_bridge_word (hn : 2 ≤ n) (p : State n)
    (a b : CycleFootprint.Active p) (hab : a.val.val < b.val.val)
    (hsep : ¬CycleFootprint.LoadPath (displacement p.symm) a.val b.val)
    (hcomponents : ∀ i, p.symm i ≠ i →
      CycleFootprint.LoadPath (displacement p.symm) a.val i ∨
      CycleFootprint.LoadPath (displacement p.symm) b.val i)
    (start finish : Fin n) :
    ∃ (r : Fin n) (w : List Letter), CycleFootprint.LoadPath (displacement p.symm) a.val r ∧
      eval w=(RotationWords.rotation start)⁻¹*p*RotationWords.rotation finish ∧
      (w.length : ℤ) ≤ (inversionNumber p : ℤ)+(∑ i, |displacement p.symm i|)+
        2*((componentLeft p b.val : ℤ)-(componentRight p a.val : ℤ))-
        RotationWords.portLoad (displacement p.symm) r+
        (min (r-start).val (n-(r-start).val)+min (finish-r).val (n-(finish-r).val) : ℕ) :=
  two_component_bridge_word hn p a b (ordered_component_extrema p a.val b.val hab hsep)
    hcomponents start finish

#print axioms separate_two_component_bridge_word
theorem fixed_gap_budget (p : State n) (u v : Fin n)
    (hgap : ∀ x : Fin n, u.val < x.val → x.val < v.val → p x=x) :
    v.val-u.val ≤ n-p.support.card+1 := by
  have hsub : Finset.Ioo u v ⊆ p.supportᶜ := by
    intro x hx
    obtain ⟨hlo,hhi⟩ := Finset.mem_Ioo.mp hx
    apply Finset.mem_compl.mpr
    simp only [Equiv.Perm.mem_support,not_not]
    exact hgap x hlo hhi
  have hc := Finset.card_le_card hsub
  simp only [Fin.card_Ioo,Finset.card_compl,Fintype.card_fin] at hc
  omega

theorem two_component_separator_budget (p : State n) (a b : CycleFootprint.Active p)
    (hcomponents : ∀ i, p.symm i ≠ i →
      CycleFootprint.LoadPath (displacement p.symm) a.val i ∨
      CycleFootprint.LoadPath (displacement p.symm) b.val i) :
    (componentLeft p b.val).val-(componentRight p a.val).val ≤ n-p.support.card+1 :=
  fixed_gap_budget p _ _ (two_components_gap_fixed p a b hcomponents)

#print axioms two_component_separator_budget
end LRX.FiniteCuts
