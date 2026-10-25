import LRX.BalancedSubsetEnergy
import Mathlib

namespace LRX.AffineLift
open scoped BigOperators
variable {n : ℕ}

/-- Majorization bounds the multiplicity of any level within the half-size range. -/
theorem majorized_level_count {d : Fin n → ℤ} (hm : Majorized d) (h : ℤ)
    (hh : 2*h ≤ (n : ℤ)) :
    ((Finset.univ.filter (fun i => d i=h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  classical
  let S := Finset.univ.filter (fun i => d i=h)
  have hb := hm S
  have hs : (∑ i ∈ S, d i)=(S.card : ℤ)*h := by
    calc
      _ = ∑ _i ∈ S, h := Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp hi).2)
      _ = _ := by simp
  rw [hs] at hb
  change (S.card : ℤ) ≤ (n : ℤ)-2*h
  by_cases he : S.card=0
  · rw [he]; omega
  · have hp : (0 : ℤ) < S.card := by exact_mod_cast Nat.pos_of_ne_zero he
    nlinarith

theorem majorized_negative_level_count {d : Fin n → ℤ}
    (hd : ∑ i, d i=0) (hm : Majorized d) (h : ℤ) (hh : 2*h ≤ (n : ℤ)) :
    ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  have hb := majorized_level_count (majorized_neg hd hm) h hh
  simpa only [neg_eq_iff_eq_neg] using hb

/-- Filling may change other coordinates; preserving negative extremes suffices here. -/
theorem inherited_negative_level_count {d e : Fin n → ℤ}
    (hd : ∑ i, d i=0) (hm : Majorized d) (h : ℤ) (hh : 2*h ≤ (n : ℤ))
    (hinherit : ∀ i, e i= -h → d i= -h) :
    ((Finset.univ.filter (fun i => e i= -h)).card : ℤ) ≤ (n : ℤ)-2*h := by
  have hs : Finset.univ.filter (fun i => e i= -h) ⊆
      Finset.univ.filter (fun i => d i= -h) := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinherit i (Finset.mem_filter.mp hi).2⟩
  have hc : ((Finset.univ.filter (fun i => e i= -h)).card : ℤ) ≤
      ((Finset.univ.filter (fun i => d i= -h)).card : ℤ) := by exact_mod_cast Finset.card_le_card hs
  exact hc.trans (majorized_negative_level_count hd hm h hh)

#print axioms inherited_negative_level_count
end LRX.AffineLift
