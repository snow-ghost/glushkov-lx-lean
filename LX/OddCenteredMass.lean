import LX.CenteredLiftSelection
import LX.WordMetric
import Mathlib

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def reflectionResidue (m : ℕ) (C : ℤ) (i : Fin n) : Fin n := (C+m : ℤ)-2*i
def reflectionBoard (m : ℕ) (C : ℤ) (i : Fin n) : ℤ := center (n := n) m (C-2*(i : ℤ))
def perturbedBoard (m : ℕ) (C : ℤ) (ρ : State n) (i : Fin n) : ℤ :=
  center (n := n) m (C-(ρ i : ℤ)-(i : ℤ))

theorem reflection_board_eq_val (m : ℕ) (C : ℤ) (i : Fin n) :
    reflectionBoard m C i=(reflectionResidue m C i : ℤ)-m := by
  have he : reflectionResidue m C i=(((C-2*(i : ℤ)+m : ℤ)) : Fin n) := by
    simp only [reflectionResidue,Int.cast_add,Int.cast_sub,Int.cast_mul,Int.cast_ofNat,
      Int.cast_natCast,Fin.cast_val_eq_self]
    ring
  rw [he]
  have hr := Int.emod_nonneg (C-2*(i : ℤ)+m) (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  simp only [reflectionBoard,center,Fin.val_intCast,Int.toNat_of_nonneg hr]

theorem odd_reflection_residue_bijective (m : ℕ) (hn : n=2*m+1) (C : ℤ) :
    Function.Bijective (reflectionResidue (n := n) m C) := by
  have htwo : (m+1 : Fin n)*2=1 := by
    have he := congrArg (fun k : ℕ => (k : Fin n)) hn
    rw [Fin.natCast_self] at he
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at he
    linear_combination -he
  have hi : Function.Injective (reflectionResidue (n := n) m C) := by
    intro i j hij
    have hlin : (2 : Fin n)*(i-j)=0 := by
      dsimp only [reflectionResidue] at hij
      linear_combination -hij
    have hh := congrArg (fun z : Fin n => ((m : Fin n)+1)*z) hlin
    rw [← mul_assoc,htwo,one_mul,mul_zero] at hh
    exact sub_eq_zero.mp hh
  exact ⟨hi,Finite.surjective_of_injective hi⟩

theorem odd_reflection_board_injective (m : ℕ) (hn : n=2*m+1) (C : ℤ) :
    Function.Injective (reflectionBoard (n := n) m C) := by
  intro i j hij
  rw [reflection_board_eq_val,reflection_board_eq_val] at hij
  apply (odd_reflection_residue_bijective m hn C).1
  apply Fin.ext
  omega

theorem odd_reflection_board_sum (m : ℕ) (hn : n=2*m+1) (C : ℤ) :
    ∑ i : Fin n,reflectionBoard m C i=0 := by
  let p : State n := Equiv.ofBijective (reflectionResidue m C) (odd_reflection_residue_bijective m hn C)
  have hs := Equiv.sum_comp p (fun i : Fin n => (i : ℤ))
  change (∑ i : Fin n,(reflectionResidue m C i : ℤ))=∑ i : Fin n,(i : ℤ) at hs
  have ht : (∑ i : Fin n,(i : ℤ))*2=(n : ℤ)*((n-1 : ℕ) : ℤ) := by
    rw [Fin.sum_univ_eq_sum_range]
    have hc := congrArg (fun k : ℕ => (k : ℤ)) (Finset.sum_range_id_mul_two n)
    convert hc using 1 <;> simp only [Nat.cast_mul,Nat.cast_sum,Nat.cast_ofNat] <;> rfl
  have hn1 : ((n-1 : ℕ) : ℤ)=2*m := by omega
  rw [hn1] at ht
  have hval : (∑ i : Fin n,(i : ℤ))=(n : ℤ)*m := by nlinarith
  simp only [reflection_board_eq_val,Finset.sum_sub_distrib,hs,hval,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,sub_self]

/-- A perturbation moving each rank back by at most one can lose at most
one period from the centered mass in odd size. -/
theorem odd_perturbed_board_mass (m : ℕ) (hn : n=2*m+1) (C : ℤ) (ρ : State n)
    (hr : ∀ i : Fin n,(i : ℤ)-(ρ i : ℤ) ≤ 1) :
    -(n : ℤ) ≤ ∑ i : Fin n,perturbedBoard m C ρ i := by
  let e : Fin n → ℤ := reflectionBoard m C
  let S := Finset.univ.filter fun i : Fin n => e i=(n : ℤ)-m-1
  have hc : S.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    apply odd_reflection_board_injective m hn C
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    exact hi'.trans hj'.symm
  have hp (i : Fin n) :
      e i+((i : ℤ)-(ρ i : ℤ))-(if e i=(n : ℤ)-m-1 then n else 0) ≤ perturbedBoard m C ρ i := by
    have hh := center_perturb_lower (n := n) m (C-2*(i : ℤ)) ((i : ℤ)-(ρ i : ℤ)) (hr i)
    have he : C-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=C-(ρ i : ℤ)-(i : ℤ) := by ring
    rw [he] at hh
    exact hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have he : (∑ i : Fin n,e i)=0 := odd_reflection_board_sum m hn C
  have hS : (∑ i : Fin n,if e i=(n : ℤ)-m-1 then (n : ℤ) else 0)=(n : ℤ)*S.card := by
    simp only [Finset.sum_ite,Finset.sum_const,Finset.sum_const_zero,add_zero,smul_eq_mul,S]
    ring
  simp only [Nat.cast_ite,Nat.cast_zero,Finset.sum_sub_distrib,Finset.sum_add_distrib,
    he,hδ,hS,zero_add,zero_sub] at hs
  have hc' : (S.card : ℤ) ≤ 1 := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hc' (show (0 : ℤ) ≤ n by positivity)
  nlinarith

#print axioms odd_perturbed_board_mass
end LX.CenteredLift
