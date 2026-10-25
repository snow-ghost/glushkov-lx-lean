import LX.EvenSecondFewFixed
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem strict_width_crossing_le_one (d : Fin n → ℤ)
    (hw : ∀ i j,d i-d j < (n : ℤ)) (i j : Fin n) : crossing d i j ≤ 1 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hnum : -(n : ℤ) ≤ crossingNumerator d i j := by
    have hh := hw i j
    have hdist : (0 : ℤ) ≤ ((j-i : Fin n) : ℤ) := by positivity
    unfold crossingNumerator
    omega
  have hq := (Int.le_ediv_iff_mul_le hn).mpr (show (-1 : ℤ)*n ≤ crossingNumerator d i j by omega)
  unfold crossing
  omega

end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.AffineLift LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

private theorem open_arc_card (i r : Fin n) :
    (Finset.univ.filter fun j : Fin n => 0 < (j-i).val ∧ (j-i).val < r.val).card=r.val-1 := by
  have hc : (Finset.univ.filter fun j : Fin n => 0 < (j-i).val ∧ (j-i).val < r.val).card=
      (Finset.Ioo (0 : Fin n) r).card := by
    apply Finset.card_bij (fun j _ => j-i)
    · intro j hj
      exact Finset.mem_Ioo.mpr (Finset.mem_filter.mp hj).2
    · intro j _ k _ he
      have hh := congrArg (fun x : Fin n => x+i) he
      simpa only [sub_add_cancel] using hh
    · intro k hk
      refine ⟨k+i,?_,by ring⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hh := Finset.mem_Ioo.mp hk
      change 0 < k.val ∧ k.val < r.val at hh
      simpa only [add_sub_cancel_right] using hh
  rw [hc,Fin.card_Ioo,Fin.val_zero]
  omega

/-- A token one level below the maximum can jump only over fixed
positions. Its next moving position is its own image on the circle. -/
theorem near_top_open_arc_fixed (p : State n) (a i : Fin n) (hh : 0 < height p a)
    (hi : backwardDepth (displacement p a) i=height p a-1) :
    permutation p a i ≠ i ∧
      ∀ j : Fin n,0 < (j-i).val → (j-i).val < (permutation p a i-i).val → permutation p a j=j := by
  classical
  let d := displacement p a
  let r := cyclicOffset p a i
  let A := Finset.univ.filter fun j : Fin n => 0 < crossing d i j
  let B := Finset.univ.filter fun j : Fin n => 0 < (j-i).val ∧ (j-i).val < r.val
  have hmax (j : Fin n) : backwardDepth d j ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 j
  have hfixed (j : Fin n) (hj : j ∈ A) : permutation p a j=j := by
    have hpos := (Finset.mem_filter.mp hj).2
    have hlt := crossing_pos_depth_lt d i j hpos
    have hjmax := hmax j
    change backwardDepth d i=height p a-1 at hi
    have he : backwardDepth (displacement p a) j=height p a := by
      change backwardDepth d j=height p a
      omega
    exact (depth_eq_height_iff_fixed p a j).mp he
  have hsub : A ⊆ B := by
    intro j hj
    have hpos : 0 < crossing d i j := (Finset.mem_filter.mp hj).2
    have hneq : j ≠ i := by intro he; subst j; simp at hpos
    have hdistpos : 0 < (j-i).val := Fin.pos_iff_ne_zero.mpr (sub_ne_zero.mpr hneq)
    have hjfixed := hfixed j hj
    have hdj : d j= -(height p a : ℤ) :=
      fixed_source_displacement p a j ((mem_fixedPositions _ _).mpr hjfixed)
    have hdi : d i=(r : ℤ)-height p a := displacement_offset p a i
    have hnum : crossingNumerator d i j=((j-i : Fin n) : ℤ)-(r : ℤ) := by
      unfold crossingNumerator
      rw [hdj,hdi]
      ring
    have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have hdistr : (j-i).val < r.val := by
      by_contra hnot
      have hq := Int.ediv_nonneg (show 0 ≤ ((j-i : Fin n) : ℤ)-(r : ℤ) by omega) (le_of_lt hnpos)
      simp only [crossing,hnum] at hpos
      omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdistpos,hdistr⟩
  have hterm (j : Fin n) : ((crossing d i j).toNat : ℤ)=if 0 < crossing d i j then 1 else 0 := by
    have hc := strict_width_crossing_le_one d (displacement_strict_width p a) i j
    split_ifs <;> omega
  have hsum : (∑ j : Fin n,((crossing d i j).toNat : ℤ))=(A.card : ℤ) := by
    simp only [hterm,Finset.sum_boole,A]
  have hrow := displacement_add_depth (is_lift p a) i
  change d i+(backwardDepth d i : ℤ)=∑ j,((crossing d i j).toNat : ℤ) at hrow
  rw [hi,hsum] at hrow
  have hdi : d i=(r : ℤ)-height p a := displacement_offset p a i
  rw [hdi] at hrow
  have hcA : A.card=r.val-1 := by omega
  have hcB : B.card=r.val-1 := open_arc_card i r
  have heq : A=B := Finset.eq_of_subset_of_card_le hsub (by omega)
  refine ⟨?_,?_⟩
  · intro hf
    have htop := (depth_eq_height_iff_fixed p a i).mpr hf
    omega
  · intro j hj0 hjr
    apply hfixed j
    rw [heq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hj0,?_⟩
    simpa only [r,cyclic_offset_normalized] using hjr

#print axioms near_top_open_arc_fixed
end LX.AnchoredPhases
