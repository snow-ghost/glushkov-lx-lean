import LX.NearTopFixedArc
import Mathlib

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.Core.FiniteCuts
variable {n : ℕ} [NeZero n]

private theorem zero_in_wrapping_arc (i q : Fin n)
    (hq : 0 < q.val) (hqi : q.val < i.val) :
    0 < ((0 : Fin n)-i).val ∧ ((0 : Fin n)-i).val < (q-i).val := by
  have hi0 : ¬i ≤ (0 : Fin n) := by change ¬i.val ≤ 0; omega
  have hiq : ¬i ≤ q := not_le.mpr hqi
  have h0 := Fin.intCast_val_sub_eq_sub_add_ite (0 : Fin n) i
  have h1 := Fin.intCast_val_sub_eq_sub_add_ite q i
  simp only [hi0,hiq,ite_false,Fin.val_zero,Nat.cast_zero] at h0 h1
  have hz : ((0 : Fin n).val : ℤ)=0 := by simp
  have := i.isLt
  omega

private theorem tail_in_zero_arc (i j : Fin n) (hi : 0 < i.val)
    (hij : i.val < j.val) :
    0 < (j-i).val ∧ (j-i).val < ((0 : Fin n)-i).val := by
  have hi0 : ¬i ≤ (0 : Fin n) := by change ¬i.val ≤ 0; omega
  have hij' : i ≤ j := le_of_lt hij
  have h0 := Fin.intCast_val_sub_eq_sub_add_ite (0 : Fin n) i
  have h1 := Fin.intCast_val_sub_eq_sub_add_ite j i
  simp only [hi0,hij',ite_false,ite_true,Fin.val_zero,Nat.cast_zero,add_zero] at h0 h1
  have hz : ((0 : Fin n).val : ℤ)=0 := by simp
  have := j.isLt
  omega

/-- With at least two descending arrows, a nonfixed head prevents any
descending arrow in a prefix whose depths are all at least `h-1`. -/
theorem near_top_prefix_nondecreasing (p : State n) (a : Fin n) (r : ℕ)
    (hh : 2 ≤ height p a) (hhead : permutation p a 0 ≠ 0)
    (hpre : ∀ i : Fin n,i.val < r → height p a-1 ≤ backwardDepth (displacement p a) i) :
    ∀ i : Fin n,i.val < r → i.val ≤ (permutation p a i).val := by
  classical
  let q := permutation p a
  have harc (i : Fin n) (hir : i.val < r) (hmove : q i ≠ i) :
      ∀ j : Fin n,0 < (j-i).val → (j-i).val < (q i-i).val → q j=j := by
    have hmax : backwardDepth (displacement p a) i ≤ height p a := by
      exact_mod_cast (candidate_price_components p a).2 i
    have hne : backwardDepth (displacement p a) i ≠ height p a := by
      intro he
      exact hmove ((depth_eq_height_iff_fixed p a i).mp he)
    exact (near_top_open_arc_fixed p a i (by omega) (by have := hpre i hir; omega)).2
  have htarget (i : Fin n) (hir : i.val < r) (hdesc : (q i).val < i.val) : q i=0 := by
    by_contra hn
    have hp : 0 < (q i).val := Fin.pos_iff_ne_zero.mpr hn
    have hz := zero_in_wrapping_arc i (q i) hp hdesc
    have hi : q i ≠ i := by intro he; rw [he] at hdesc; omega
    exact hhead (harc i hir hi 0 hz.1 hz.2)
  intro i hir
  by_contra hnot
  change ¬i.val ≤ (q i).val at hnot
  have hdesc : (q i).val < i.val := by omega
  have hi0 : 0 < i.val := by omega
  have hi : q i ≠ i := by intro he; rw [he] at hdesc; omega
  have hqi := htarget i hir hdesc
  have hsub : descendingPositions q ⊆ {i} := by
    intro j hj
    have hjdesc := (mem_descendingPositions q j).mp hj
    by_cases hji : j.val ≤ i.val
    · have hj0 := htarget j (by omega) hjdesc
      exact Finset.mem_singleton.mpr (q.injective (hj0.trans hqi.symm))
    · have hz := tail_in_zero_arc i j hi0 (by omega)
      rw [← hqi] at hz
      have hjfix := harc i hir hi j hz.1 hz.2
      rw [hjfix] at hjdesc
      omega
  have hc := Finset.card_le_card hsub
  rw [Finset.card_singleton] at hc
  change height p a ≤ 1 at hc
  omega

#print axioms near_top_prefix_nondecreasing
end LX.AnchoredPhases
