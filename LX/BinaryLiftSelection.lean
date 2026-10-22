import LX.BoundedGreedyNormalForm

namespace LX.BinaryLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

def residue (p : State n) (c i : Fin n) : Fin n := p.symm i+c-i

/-- A selected position takes the negative representative of its residue. -/
def displacement (p : State n) (c : Fin n) (S : Finset (Fin n)) (i : Fin n) : ℤ :=
  (residue p c i : ℤ)-(if i ∈ S then (n : ℤ) else 0)

def ValidSelection (p : State n) (c : Fin n) (S : Finset (Fin n)) : Prop :=
  (∀ i ∈ S,residue p c i ≠ 0) ∧
    (∑ i : Fin n,(residue p c i : ℤ))=(n : ℤ)*S.card

theorem selected_lift (p : State n) (c : Fin n) (S : Finset (Fin n))
    (hS : ValidSelection p c S) : IsLift p (c : ℤ) (displacement p c S) := by
  constructor
  · unfold displacement
    rw [Finset.sum_sub_distrib,hS.2]
    have hs : (∑ i : Fin n,if i ∈ S then (n : ℤ) else 0)=(n : ℤ)*S.card := by
      simp [mul_comm]
    rw [hs,sub_self]
  · intro i
    apply (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp
    simp only [displacement,Int.cast_add,Int.cast_sub,Int.cast_ite,Int.cast_natCast,
      Fin.natCast_self,Int.cast_zero,Fin.cast_val_eq_self,ite_self,sub_zero,residue]
    ring

theorem selected_bound (p : State n) (c : Fin n) (S : Finset (Fin n))
    (hS : ValidSelection p c S) (i : Fin n) : |displacement p c S i| ≤ (n : ℤ)-1 := by
  have hr := (residue p c i).isLt
  have hr0 : 0 ≤ (residue p c i : ℤ) := by positivity
  unfold displacement
  rw [abs_le]
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    have hnz : (residue p c i).val ≠ 0 := fun h => hS.1 i hi (Fin.ext h)
    omega
  · rw [ite_eq_right hi]
    omega

/-- The displacement bound leaves exactly the positive and negative
representatives. In particular zero cannot wind by a full turn. -/
theorem bounded_representatives (p : State n) (c : Fin n) (d : Fin n → ℤ)
    (hd : IsLift p (c : ℤ) d) (hb : ∀ i,|d i| ≤ (n : ℤ)-1) (i : Fin n) :
    d i=(residue p c i : ℤ) ∨ d i=(residue p c i : ℤ)-n := by
  have hr : (d i : Fin n)=residue p c i := by
    have hh := lift_residue hd i
    simp only [Int.cast_natCast,Fin.cast_val_eq_self] at hh
    unfold residue
    linear_combination hh
  have hm : Int.ModEq (n : ℤ) (d i) (residue p c i : ℤ) :=
    (LRX.LiftedModel.cast_eq_iff_modEq _ _).mp (by simpa using hr)
  have hnpos : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hri : (residue p c i : ℤ) < n := by exact_mod_cast (residue p c i).isLt
  have hr0 : 0 ≤ (residue p c i : ℤ) := by positivity
  change d i % (n : ℤ)=(residue p c i : ℤ) % (n : ℤ) at hm
  rw [Int.emod_eq_of_lt hr0 hri] at hm
  have hb' := (abs_le.mp (hb i))
  by_cases hpos : 0 ≤ d i
  · left
    rwa [Int.emod_eq_of_lt hpos (by omega)] at hm
  · right
    have hq : d i/(n : ℤ)= -1 := by
      apply LRX.PeriodicBuffer.quotient_eq_of_bounds hnpos <;> omega
    have he := Int.ediv_mul_add_emod (d i) (n : ℤ)
    rw [hq,hm] at he
    omega

/-- Every bounded lift is represented by a valid finite selection; the
balance equation fixes the number of negative representatives. -/
theorem bounded_lift_selection (p : State n) (c : Fin n) (d : Fin n → ℤ)
    (hd : IsLift p (c : ℤ) d) (hb : ∀ i,|d i| ≤ (n : ℤ)-1) :
    ∃ S : Finset (Fin n),ValidSelection p c S ∧ displacement p c S=d := by
  classical
  let S := Finset.univ.filter fun i => d i < 0
  have hm (i : Fin n) : i ∈ S ↔ d i < 0 := by simp [S]
  have he (i : Fin n) : displacement p c S i=d i := by
    have hr := bounded_representatives p c d hd hb i
    have hri := (residue p c i).isLt
    have hr0 : 0 ≤ (residue p c i : ℤ) := by positivity
    unfold displacement
    by_cases hi : i ∈ S
    · rw [ite_eq_left hi]
      have := (hm i).mp hi
      omega
    · rw [ite_eq_right hi]
      have : ¬d i < 0 := fun h => hi ((hm i).mpr h)
      omega
  have hnonzero (i : Fin n) (hi : i ∈ S) : residue p c i ≠ 0 := by
    have hh := he i
    have hbound := abs_le.mp (hb i)
    unfold displacement at hh
    rw [ite_eq_left hi] at hh
    intro hz
    rw [hz] at hh
    norm_num at hh
    omega
  have hs : (∑ i : Fin n,displacement p c S i)=0 := by simp_rw [he]; exact hd.1
  have hsum : (∑ i : Fin n,(residue p c i : ℤ))=(n : ℤ)*S.card := by
    unfold displacement at hs
    rw [Finset.sum_sub_distrib] at hs
    have hc : (∑ i : Fin n,if i ∈ S then (n : ℤ) else 0)=(n : ℤ)*S.card := by simp [mul_comm]
    rw [hc] at hs
    omega
  exact ⟨S,⟨hnonzero,hsum⟩,funext he⟩

#print axioms selected_lift
#print axioms bounded_lift_selection
end LX.BinaryLift
