import LX.EvenStrictPhases

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- In every nonexceptional balanced phase, a smallest token is either
at the initial head or far enough along the circle to pay the target. -/
theorem even_strict_minimum_location (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) (hpar : (c.val+m)%2=0) :
    d 0=1-(m : ℤ) ∨ ∃ j : Fin n,m+2 ≤ j.val ∧ d j=1-(m : ℤ) := by
  have he := even_strict_lift_unique m (by omega) hn c hd hlo
  have hcne := even_strict_phase_ne_boundary m hm hn hd hlo
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hn' : (n : ℤ)=2*m := by omega
  have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
  by_cases hcm : c.val=m
  · left
    rw [he]
    have h01 : (0 : Fin n) ≠ 1 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv1] at this; omega
    have h02 : (0 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; simp only [Fin.val_zero,hv2] at this; omega
    unfold evenStrictBase perturbedBoard
    rw [Equiv.swap_apply_of_ne_of_ne h01 h02]
    simp only [Fin.val_zero,Nat.cast_zero,sub_zero,hcm]
    apply center_eq_of_translate (m-1) _ _ 1
    · omega
    · constructor <;> omega
  · have hcm2 : c.val ≠ m+2 := by
      intro hh
      apply hcne
      apply Fin.ext
      have hval : (((m+2 : ℕ)) : Fin n).val=m+2 := Nat.mod_eq_of_lt (by omega)
      omega
    let k : ℕ := (c.val+m)/2
    have hk : 2*k=c.val+m := by
      have hh := Nat.mod_add_div (c.val+m) 2
      dsimp only [k]
      omega
    let jv : ℕ := if k < m then k+m else k
    have hjlo : m+2 ≤ jv := by
      have hclt := c.isLt
      dsimp only [jv]
      split_ifs <;> omega
    have hjhi : jv < n := by
      have hclt := c.isLt
      dsimp only [jv]
      split_ifs <;> omega
    have hjtwice : 2*jv=c.val+m ∨ 2*jv=c.val+m+n := by
      dsimp only [jv]
      split_ifs <;> omega
    let j : Fin n := ⟨jv,hjhi⟩
    have hj1 : j ≠ 1 := by intro hh; have := congrArg Fin.val hh; change jv=(1 : Fin n).val at this; omega
    have hj2 : j ≠ 2 := by intro hh; have := congrArg Fin.val hh; change jv=(2 : Fin n).val at this; omega
    refine Or.inr ⟨j,hjlo,?_⟩
    rw [he]
    unfold evenStrictBase perturbedBoard
    rw [Equiv.swap_apply_of_ne_of_ne hj1 hj2]
    have hjval : (j : ℤ)=(jv : ℤ) := rfl
    rw [hjval]
    rcases hjtwice with hh | hh
    · apply center_eq_of_translate (m-1) _ _ 0
      · omega
      · constructor <;> omega
    · apply center_eq_of_translate (m-1) _ _ (-1)
      · omega
      · constructor <;> omega

theorem even_ordinary_token_bound (hn : 3 ≤ n) {c : Fin n} {d : Fin n → ℤ}
    (hd : IsLift even (c : ℤ) d) {g : List Letter} (hg : ScanTrace d g)
    (i : Fin n) (hi : 3 ≤ i.val) :
    2*(i : ℤ)-(n : ℤ)-1-((n : ℤ)-1)*d i ≤ (paidRotations c g : ℤ) := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hi1 : i ≠ 1 := by intro hh; have := congrArg Fin.val hh; omega
  have hi2 : i ≠ 2 := by intro hh; have := congrArg Fin.val hh; omega
  have hq : -(even : State n).symm i=i-1 := by
    change -(1-Equiv.swap (1 : Fin n) 2 i)=i-1
    rw [Equiv.swap_apply_of_ne_of_ne hi1 hi2]
    ring
  have hqval : ((i-1 : Fin n) : ℤ)=(i : ℤ)-1 := by
    rw [Fin.intCast_val_sub_eq_sub_add_ite]
    have hle : (1 : Fin n) ≤ i := by change (1 : Fin n).val ≤ i.val; omega
    simp only [hle,ite_true,hv1,Nat.cast_one,Nat.cast_zero,add_zero]
  have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd i
  rw [hq,hqval] at ht
  have hip : ((i.val-1 : ℕ) : ℤ)=(i : ℤ)-1 := by omega
  rw [hip] at ht
  unfold targets at ht
  nlinarith

#print axioms even_strict_minimum_location
end LX.Antipode
