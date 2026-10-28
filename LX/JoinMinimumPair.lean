import LX.LiftedModel
import LX.WordMetric
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.Core.AffineLift
variable {n : ℕ} [NeZero n]

/-- The balanced lift obtained by joining two fixed positions of an odd
three-fixed-point source and shifting the final phase back by one. -/
def joinMinima (d : Fin n → ℤ) (u v : Fin n) (i : Fin n) : ℤ :=
  d i-1+(if i=u then 1 else 0)+(if i=v then (n : ℤ)-1 else 0)

theorem join_minima_balance (d : Fin n → ℤ) (u v : Fin n) (hb : ∑ i,d i=0) :
    ∑ i,joinMinima d u v i=0 := by
  simp [joinMinima,Finset.sum_add_distrib,Finset.sum_sub_distrib,hb]

theorem join_minima_subset_sum (d : Fin n → ℤ) (u v : Fin n) (S : Finset (Fin n)) :
    (∑ i ∈ S,joinMinima d u v i)=(∑ i ∈ S,d i)-(S.card : ℤ)+
      (if u ∈ S then 1 else 0)+(if v ∈ S then (n : ℤ)-1 else 0) := by
  simp [joinMinima,Finset.sum_add_distrib,Finset.sum_sub_distrib]

/-- Full majorization is preserved. The potentially increasing subsets are
paid by deleting the one or two known minimum coordinates before applying the
original subset inequality. -/
theorem join_minima_majorized (d : Fin n → ℤ) (u v : Fin n) (hne : u ≠ v)
    (hb : ∑ i,d i=0) (hm : Majorized d) (h : ℕ) (hn : n=2*h+3)
    (hu : d u= -(h : ℤ)) (hv : d v= -(h : ℤ)) :
    Majorized (joinMinima d u v) := by
  intro S
  have hs := join_minima_subset_sum d u v S
  have hn' : (n : ℤ)=2*(h : ℤ)+3 := by exact_mod_cast hn
  have hk0 : (0 : ℤ) ≤ S.card := Nat.cast_nonneg _
  by_cases hvs : v ∈ S
  · by_cases hus : u ∈ S
    · by_cases hfull : S=Finset.univ
      · subst S
        rw [join_minima_balance d u v hb]
        simp
      · have hue : u ∈ S.erase v := Finset.mem_erase.mpr ⟨hne,hus⟩
        have he1 := Finset.sum_erase_add S d hvs
        have he2 := Finset.sum_erase_add (S.erase v) d hue
        rw [hu] at he2
        rw [hv] at he1
        have hk2 : 2 ≤ S.card := by
          have hc := Finset.card_pos.mpr (show (S.erase v).Nonempty from ⟨u,hue⟩)
          rw [Finset.card_erase_of_mem hvs] at hc
          omega
        have hcard : ((S.erase v).erase u).card=S.card-2 := by
          rw [Finset.card_erase_of_mem hue,Finset.card_erase_of_mem hvs]
          omega
        have hm' := hm ((S.erase v).erase u)
        rw [hcard,Nat.cast_sub hk2] at hm'
        norm_num only [Nat.cast_ofNat] at hm'
        have hkn : S.card < n := by
          have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ S,hfull⟩)
          simpa using hc
        have hkn' : (S.card : ℤ) ≤ (n : ℤ)-1 := by omega
        rw [hs,ite_eq_left hus,ite_eq_left hvs]
        nlinarith
    · have he := Finset.sum_erase_add S d hvs
      rw [hv] at he
      have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨v,hvs⟩
      have hm' := hm (S.erase v)
      rw [Finset.card_erase_of_mem hvs,Nat.cast_sub hk] at hm'
      norm_num only [Nat.cast_ofNat] at hm'
      rw [hs,ite_eq_right hus,ite_eq_left hvs]
      nlinarith
  · have hm' := hm S
    rw [hs,ite_eq_right hvs]
    by_cases hus : u ∈ S
    · rw [ite_eq_left hus]
      have hk : 1 ≤ S.card := Finset.card_pos.mpr ⟨u,hus⟩
      nlinarith
    · rw [ite_eq_right hus]
      nlinarith

theorem join_minima_cast (d : Fin n → ℤ) (u v i : Fin n) :
    (joinMinima d u v i : Fin n)=(d i : Fin n)-1+
      (if i=u then 1 else 0)-(if i=v then 1 else 0) := by
  unfold joinMinima
  split_ifs <;> simp only [Int.cast_add,Int.cast_sub,Int.cast_one,Int.cast_zero,
    Int.cast_natCast,Fin.natCast_self] <;> ring

/-- The joined vector belongs to the input with the two neighboring positions
transposed, and has final phase c-1. This includes a pair across the seam. -/
theorem join_minima_lift {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p.symm c d) (u v : Fin n) (hne : u ≠ v)
    (hv : v=u+1) (he : d u=d v) :
    IsLift (p*Equiv.swap u v).symm (c-1) (joinMinima d u v) := by
  refine ⟨join_minima_balance d u v hd.1,?_⟩
  intro i
  apply (LX.Core.LiftedModel.cast_eq_iff_modEq _ _).mp
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast,Int.cast_one,Fin.cast_val_eq_self,
    Equiv.symm_symm,Equiv.Perm.mul_apply,join_minima_cast]
  by_cases hiu : i=u
  · subst i
    simp only [ite_true,ite_eq_right hne,Equiv.swap_apply_left]
    have hh := lift_residue hd v
    simp only [Equiv.symm_symm] at hh
    rw [← he] at hh
    rw [hv] at hh ⊢
    linear_combination hh
  · by_cases hiv : i=v
    · subst i
      simp only [ite_true,ite_eq_right hiu,Equiv.swap_apply_right]
      have hh := lift_residue hd u
      simp only [Equiv.symm_symm] at hh
      rw [he] at hh
      rw [hv] at hh ⊢
      linear_combination hh
    · simp only [ite_eq_right hiu,ite_eq_right hiv,Equiv.swap_apply_of_ne_of_ne hiu hiv]
      have hh := lift_residue hd i
      simp only [Equiv.symm_symm] at hh
      linear_combination hh

#print axioms join_minima_balance
#print axioms join_minima_majorized
#print axioms join_minima_lift
end LX.AffineScan
