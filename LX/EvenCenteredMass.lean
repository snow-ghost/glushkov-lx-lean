import LX.OddCenteredMass
import Mathlib.Algebra.Order.Floor.BigOperators

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

private theorem sum_mod_add (A : ℤ) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m,(A+i)%(m : ℤ))=∑ i ∈ Finset.range m,(i : ℤ) := by
  have he (i : ℕ) : (A+i)%(m : ℤ)=A+i-(m : ℤ)*((A+i)/(m : ℤ)) := by
    have hh := Int.mul_ediv_add_emod (A+i) (m : ℤ)
    omega
  simp only [he,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Int.sum_range_add_ediv A hm,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  ring

private theorem sum_mod_sub (A : ℤ) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ Finset.range m,(A-i)%(m : ℤ))=∑ i ∈ Finset.range m,(i : ℤ) := by
  rw [← Finset.sum_range_reflect]
  calc
    _ = ∑ i ∈ Finset.range m,((A-((m-1 : ℕ) : ℤ))+i)%(m : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hil := Finset.mem_range.mp hi
      have he : A-((m-1-i : ℕ) : ℤ)=A-((m-1 : ℕ) : ℤ)+i := by omega
      rw [he]
    _ = _ := sum_mod_add _ m hm

theorem even_reflection_board_formula (m : ℕ) (hm : 0 < m) (hn : n=2*m)
    (C : ℤ) (i : Fin n) :
    reflectionBoard m C i=
      2*(((C+m)/2-(i : ℤ))%(m : ℤ))+(C+m)%2-m := by
  have hm' : (0 : ℤ) < m := by omega
  have hn' : (n : ℤ)=2*m := by omega
  have hA := Int.ediv_mul_add_emod (C+m) 2
  have hdiv := Int.ediv_mul_add_emod ((C+m)/2-(i : ℤ)) (m : ℤ)
  have hr := Int.emod_nonneg ((C+m)/2-(i : ℤ)) (ne_of_gt hm')
  have hrhi := Int.emod_lt_of_pos ((C+m)/2-(i : ℤ)) hm'
  have he : C-2*(i : ℤ)+m=2*(m : ℤ)*(((C+m)/2-(i : ℤ))/(m : ℤ))+
      (2*(((C+m)/2-(i : ℤ))%(m : ℤ))+(C+m)%2) := by nlinarith
  have hb0 : 0 ≤ 2*(((C+m)/2-(i : ℤ))%(m : ℤ))+(C+m)%2 := by omega
  have hbn : 2*(((C+m)/2-(i : ℤ))%(m : ℤ))+(C+m)%2 < 2*(m : ℤ) := by omega
  unfold reflectionBoard center
  rw [hn',he,Int.add_emod]
  simp only [Int.mul_emod_right,zero_add,Int.emod_eq_of_lt hb0 hbn]

theorem even_reflection_board_sum (m : ℕ) (hm : 0 < m) (hn : n=2*m) (C : ℤ) :
    (∑ i : Fin n,reflectionBoard m C i)=(n : ℤ)*((C+m)%2-1) := by
  have hmod : (∑ i : Fin n,(((C+m)/2-(i : ℤ))%(m : ℤ)))=
      2*∑ i ∈ Finset.range m,(i : ℤ) := by
    change (∑ i : Fin n,(fun k : ℕ => ((C+(m : ℤ))/2-(k : ℤ))%(m : ℤ)) i.val)=_
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => ((C+(m : ℤ))/2-(k : ℤ))%(m : ℤ)) n,
      show n=m+m by omega,Finset.sum_range_add]
    have htail : (∑ i ∈ Finset.range m,((C+m)/2-((m+i : ℕ) : ℤ))%(m : ℤ))=
        ∑ i ∈ Finset.range m,((C+m)/2-(i : ℤ))%(m : ℤ) := by
      apply Finset.sum_congr rfl
      intro i _
      have he : (C+m)/2-((m+i : ℕ) : ℤ)=((C+m)/2-(i : ℤ))-(m : ℤ) := by push_cast; ring
      rw [he]
      simp only [Int.sub_emod,Int.emod_self,sub_zero,Int.emod_emod]
    rw [htail,sum_mod_sub _ m hm]
    ring
  have hid : (∑ i ∈ Finset.range m,(i : ℤ))*2=(m : ℤ)*((m-1 : ℕ) : ℤ) := by
    have hh := congrArg (fun k : ℕ => (k : ℤ)) (Finset.sum_range_id_mul_two m)
    convert hh using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  rw [hm1] at hid
  simp only [even_reflection_board_formula m hm hn,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,hmod]
  have hn' : (n : ℤ)=2*m := by omega
  nlinarith

/-- The transposition of ranks 1 and 2 still leaves centered mass at
least -n. Its only possible downward wrap occurs when the base mass is zero. -/
theorem even_perturbed_board_mass (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m) (C : ℤ) :
    -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C (Equiv.swap 1 2) i := by
  let ρ : State n := Equiv.swap 1 2
  let e : Fin n → ℤ := reflectionBoard m C
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have h12 : (1 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; omega
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))-
      (if i=2 ∧ e 2=(n : ℤ)-m-1 then (n : ℤ) else 0) ≤ perturbedBoard m C ρ i := by
    have hex : C-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=C-(ρ i : ℤ)-(i : ℤ) := by ring
    by_cases hi2 : i=2
    · subst i
      have hh := center_perturb_lower (n := n) m (C-2*(2 : Fin n).val)
        ((2 : Fin n).val-(ρ 2 : ℤ)) (by simp only [ρ,Equiv.swap_apply_right,hv1,hv2]; omega)
      rw [hex] at hh
      convert hh using 1 <;>
        simp only [true_and,Nat.cast_ite,Nat.cast_zero,e,reflectionBoard,perturbedBoard] <;> rfl
    · have hδ : (i : ℤ)-(ρ i : ℤ) ≤ 0 := by
        by_cases hi1 : i=1
        · subst i; simp only [ρ,Equiv.swap_apply_left,hv1,hv2]; omega
        · simp only [ρ,Equiv.swap_apply_of_ne_of_ne hi1 hi2,sub_self,le_refl]
      have hb := center_bounds (n := n) m (C-2*(i : ℤ))
      have hh := le_center_of_below_top (n := n) m (e i+((i : ℤ)-(ρ i : ℤ))) (by
        have hbe : e i < (n : ℤ)-m := hb.2
        linarith)
      dsimp only [e,reflectionBoard] at hh
      rw [← center_add] at hh
      rw [hex] at hh
      simpa only [hi2,false_and,ite_false,sub_zero,e,reflectionBoard,perturbedBoard] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have hsum : (∑ i : Fin n,e i)=(n : ℤ)*((C+m)%2-1) := even_reflection_board_sum m (by omega) hn C
  have hloss : (∑ i : Fin n,if i=2 ∧ e 2=(n : ℤ)-m-1 then (n : ℤ) else 0)=
      if e 2=(n : ℤ)-m-1 then n else 0 := by simp [ite_and]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hδ,hsum,hloss,add_zero] at hs
  change -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C ρ i
  by_cases htop : e 2=(n : ℤ)-m-1
  · have hformula := even_reflection_board_formula m (by omega) hn C (2 : Fin n)
    change e 2=_ at hformula
    rw [htop] at hformula
    have hpar : (C+m)%2=1 := by omega
    rw [hpar,ite_eq_left htop] at hs
    norm_num at hs
    exact hs
  · rw [ite_eq_right htop,Nat.cast_zero,sub_zero] at hs
    have hr : 0 ≤ (C+m)%2 := Int.emod_nonneg _ (by decide)
    have hp := mul_nonneg (show (0 : ℤ) ≤ n by positivity) hr
    nlinarith

#print axioms even_perturbed_board_mass
end LX.CenteredLift
