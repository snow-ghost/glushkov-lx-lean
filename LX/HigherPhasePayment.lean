import LX.EvenSecondFewFixed
import LX.ReserveAwareAnchorPrice
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]


/-- The exact word price at height n/2. The terminal allowance must pay
the strip reserve, with no hidden assumption of majorization. -/
theorem even_higher_anchor_reserve_price (p : State n) (b : Fin n)
    (hn4 : 4 ≤ n) (hn : n=2*height p b)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((b.val : ℤ)+((-p b).val : ℤ)-anchorReserve p b) := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p b (by omega) (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p b : ℤ) := by exact_mod_cast hn
  nlinarith


#print axioms even_higher_anchor_reserve_price

/-- At the odd maximal height, retain the full exchange reserve in the
same literal word construction. -/
theorem odd_higher_anchor_reserve_price (p : State n) (b : Fin n)
    (hn4 : 4 ≤ n) (hn : n=2*height p b+1)
    (hhead : p 0 ≠ p b-b)
    (hlast : ∀ i : Fin n,p i-i=p b-b → i.val ≤ b.val)
    (hcount : depthCount (displacement p b) (height p b-1) ≤ b.val+(-p b).val) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((b.val : ℤ)+((-p b).val : ℤ)-height p b-anchorReserve p b)+1 := by
  obtain ⟨w,hw,hprice⟩ := aligned_anchor_exact_word p b (by omega) (by omega) hhead hlast hcount
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p b : ℤ)+1 := by exact_mod_cast hn
  nlinarith

/-- A majorized odd maximal-height source has one fixed position. -/
theorem odd_higher_fixed_unique (p : State n) (b : Fin n)
    (hm : Majorized (displacement p b)) (hn : n=2*height p b+1) :
    (LRX.FiniteCuts.fixedPositions (permutation p b)).card=1 := by
  have hc := top_depth_count (is_lift p b) hm (height p b) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p b).2 i)
  rw [top_depth_count_eq_fixed] at hc
  have hp : 0 < (LRX.FiniteCuts.fixedPositions (permutation p b)).card := Finset.card_pos.mpr
    ⟨b,(LRX.FiniteCuts.mem_fixedPositions _ _).mpr (permutation_anchor p b)⟩
  omega


#print axioms odd_higher_anchor_reserve_price
#print axioms odd_higher_fixed_unique
end LX.AnchoredPhases
