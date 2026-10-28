import LX.CompleteMapping
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

theorem complete_good_anchor_two (p : State n) (hp : CompleteMapping p) (h : ℕ)
    (hn : n=2*h+1) (hh : 3 ≤ h) :
    ∃ a : Fin n, 0 < a.val ∧ a.val+h ≤ (p a).val+2 ∧
      3 ≤ a.val+(n-(p a).val) := by
  let P := Finset.univ.filter (fun i : Fin n => i.val < (p i).val)
  let δ := fun i : Fin n => (p i).val-i.val
  have hcard : P.card=h := complete_positive_count p hp h hn
  have hinj : Set.InjOn δ P := by
    intro i hi j hj he
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    apply hp
    have hcast := congrArg (fun k : ℕ => (k : Fin n)) he
    simpa only [δ,Nat.cast_sub (Nat.le_of_lt hi'),Nat.cast_sub (Nat.le_of_lt hj'),
      Fin.cast_val_eq_self] using hcast
  by_contra hnone
  push Not at hnone
  let T := Finset.Icc (n-2) (n-2)
  have hTcard : T.card ≤ 1 := by simp [T]
  let S : Finset ℕ := (Finset.Icc 1 (h-3) ∪ T) ∪ {δ 0}
  have hsub : P.image δ ⊆ S := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    have hpa := (Finset.mem_filter.mp ha).2
    have hpn := (p a).isLt
    by_cases ha0 : a=0
    · subst a
      simp [S]
    · have hap : 0 < a.val := Fin.pos_iff_ne_zero.mpr ha0
      by_cases hlo : δ a ≤ h-3
      · have hδpos : 0 < δ a := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        exact Or.inl (Or.inl ⟨hδpos,hlo⟩)
      · have hforward : a.val+h ≤ (p a).val+2 := by dsimp [δ] at hlo; omega
        have hnot := hnone a hap hforward
        have hδhi : n-2 ≤ δ a ∧ δ a ≤ n-2 := by dsimp [δ]; omega
        simp only [S,Finset.mem_union,Finset.mem_Icc,Finset.mem_singleton]
        apply Or.inl
        apply Or.inr
        exact Finset.mem_Icc.mpr hδhi
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_iff.mpr hinj,hcard] at hc
  have hcu := Finset.card_union_le (Finset.Icc 1 (h-3) ∪ T) {δ 0}
  have hcu' := Finset.card_union_le (Finset.Icc 1 (h-3)) T
  change S.card ≤ _ at hcu
  simp only [Nat.card_Icc,Finset.card_singleton] at hcu hcu'
  omega


#print axioms complete_good_anchor_two
end LX.AnchoredPhases
