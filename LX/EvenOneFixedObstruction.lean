import LX.ReserveAwareAnchorPrice
import LX.EvenTwoFixedPayment

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

/-- A unique fixed position is the only maximum-depth position, so its
physical index supplies the last-in-fiber premise of the exact price. -/
theorem one_fixed_last_offset (p : State n) (a : Fin n)
    (hf : (fixedPositions (permutation p a)).card=1) :
    ∀ i : Fin n,p i-i=p a-a → i=a := by
  intro i hi
  have hfix : permutation p a i=i := by
    change p i+(a-p a)=i
    linear_combination hi
  exact Finset.card_le_one.mp hf.le i ((mem_fixedPositions _ _).mpr hfix)
    a ((mem_fixedPositions _ _).mpr (permutation_anchor p a))

/-- Away from the head and the small terminal corner, any still-unpaid
one-fixed global phase must make a backward jump exceeding its entire
exchange reserve by at least 31. This is a necessary condition on the
actual input, derived from a literal LX word. -/
theorem even_one_fixed_unpaid_backward_gap {p : State n} {a : Fin n}
    (hn4 : 4 ≤ n) (m : ℕ) (hn : n=2*m) (ha : GlobalMinimum p a)
    (hf : (fixedPositions (permutation p a)).card=1) (ha0 : a ≠ 0)
    (hcorner : 8 ≤ a.val+(-p a).val)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    0 < (p a).val ∧ (p a).val < a.val ∧
      (m : ℤ)*(m-1)-inversions (displacement p a)+31 ≤ (a.val : ℤ)-(p a).val := by
  have hh := even_unpaid_global_height hn4 m hn ha hunpaid
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
  have hh' : (height p a : ℤ)+1=m := by exact_mod_cast hh
  have hdelta : 0 ≤ (m : ℤ)*(m-1)-inversions (displacement p a) := by nlinarith
  have hupper := even_unpaid_reserve_upper hn4 m hn ha hunpaid
  have hpos : 2 ≤ height p a := by omega
  have hlast := one_fixed_last_offset p a hf
  have hhead : p 0 ≠ p a-a := by
    intro he
    have hz : (0 : Fin n)=a := hlast 0 (by simpa only [sub_zero] using he)
    exact ha0 hz.symm
  have hc := next_depth_count (is_lift p a) (global_minimum_majorized ha)
    (height p a) (by omega) (by omega)
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
  have hcount : depthCount (displacement p a) (height p a-1) ≤ a.val+(-p a).val := by omega
  obtain ⟨w,hw,hprice⟩ := even_anchor_reserve_price p a hpos (by omega) hhead
    (fun i hi => by rw [hlast i hi]) hcount
  have hnot : ¬4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := fun hp => hunpaid ⟨w,hw,hp⟩
  have hres : anchorReserve p a=(m : ℤ)*(m-1)-inversions (displacement p a) := by
    unfold anchorReserve
    nlinarith
  rw [hres] at hprice
  have hfinish : (n : ℤ)+(m : ℤ)*(m-1)-inversions (displacement p a)+31 ≤
      (a.val : ℤ)+((-p a).val : ℤ) := by omega
  have hne : p a ≠ 0 := by
    intro he
    rw [he,neg_zero,Fin.val_zero,Nat.cast_zero,add_zero] at hfinish
    have hi := a.isLt
    omega
  have hpa : 0 < (p a).val := Fin.pos_iff_ne_zero.mpr hne
  have hneg : (-p a).val=n-(p a).val := by simp [Fin.val_neg,hne]
  rw [hneg,Nat.cast_sub (Nat.le_of_lt (p a).isLt)] at hfinish
  exact ⟨hpa,by omega,by omega⟩

/-- The even residual problem now has a selected real source with one
fixed position and one of three explicit positional obstructions. -/
theorem even_unpaid_one_fixed_geometry (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card=1 ∧
      (a=0 ∨ a.val+(-p a).val < 8 ∨
        (0 < (p a).val ∧ (p a).val < a.val ∧
          (m : ℤ)*(m-1)-inversions (displacement p a)+31 ≤ (a.val : ℤ)-(p a).val)) := by
  obtain ⟨a,ha,hh,hf⟩ := even_unpaid_one_fixed_minimum hn4 p m hn hunpaid
  refine ⟨a,ha,hh,hf,?_⟩
  by_cases ha0 : a=0
  · exact Or.inl ha0
  · by_cases hcorner : a.val+(-p a).val < 8
    · exact Or.inr (Or.inl hcorner)
    · exact Or.inr (Or.inr (even_one_fixed_unpaid_backward_gap hn4 m hn ha hf ha0 (by omega) hunpaid))

#print axioms even_one_fixed_unpaid_backward_gap
#print axioms even_unpaid_one_fixed_geometry
end LX.AnchoredPhases
