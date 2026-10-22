import LX.EvenStrictBase

namespace LX.CenteredLift
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem swap_perturbed_mass_drop (h : ℕ) (hn : 3 ≤ n) (C : ℤ) :
    (∑ i : Fin n,reflectionBoard h C i)-
      (if reflectionBoard h C (2 : Fin n)=(n : ℤ)-h-1 then (n : ℤ) else 0) ≤
        ∑ i : Fin n,perturbedBoard h C (Equiv.swap 1 2) i := by
  let ρ : State n := Equiv.swap 1 2
  let e : Fin n → ℤ := reflectionBoard h C
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hp (i : Fin n) : e i+((i : ℤ)-(ρ i : ℤ))-
      (if i=2 ∧ e 2=(n : ℤ)-h-1 then (n : ℤ) else 0) ≤ perturbedBoard h C ρ i := by
    have hex : C-2*(i : ℤ)+((i : ℤ)-(ρ i : ℤ))=C-(ρ i : ℤ)-(i : ℤ) := by ring
    by_cases hi2 : i=2
    · subst i
      have hh := center_perturb_lower (n := n) h (C-2*(2 : Fin n).val)
        ((2 : Fin n).val-(ρ 2 : ℤ)) (by simp only [ρ,Equiv.swap_apply_right,hv1,hv2]; omega)
      rw [hex] at hh
      convert hh using 1 <;>
        simp only [true_and,Nat.cast_ite,Nat.cast_zero,e,reflectionBoard,perturbedBoard]
    · have hδ : (i : ℤ)-(ρ i : ℤ) ≤ 0 := by
        by_cases hi1 : i=1
        · subst i; simp only [ρ,Equiv.swap_apply_left,hv1,hv2]; omega
        · simp only [ρ,Equiv.swap_apply_of_ne_of_ne hi1 hi2,sub_self,le_refl]
      have hb : e i < (n : ℤ)-h := (center_bounds (n := n) h (C-2*(i : ℤ))).2
      have hh := le_center_of_below_top (n := n) h (e i+((i : ℤ)-(ρ i : ℤ))) (by omega)
      dsimp only [e,reflectionBoard] at hh
      rw [← center_add,hex] at hh
      simpa only [hi2,false_and,ite_false,sub_zero,e,reflectionBoard,perturbedBoard] using hh
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hp i)
  have hδ : (∑ i : Fin n,((i : ℤ)-(ρ i : ℤ)))=0 := by
    rw [Finset.sum_sub_distrib,Equiv.sum_comp ρ (fun i : Fin n => (i : ℤ)),sub_self]
  have hloss : (∑ i : Fin n,if i=2 ∧ e 2=(n : ℤ)-h-1 then (n : ℤ) else 0)=
      if e 2=(n : ℤ)-h-1 then (n : ℤ) else 0 := by simp [ite_and]
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,hδ,hloss,add_zero] using hs

end LX.CenteredLift

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LX.CenteredLift LRX.AffineLift
variable {n : ℕ} [NeZero n]

theorem even_strict_reflection_mass (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (c : Fin n) :
    (∑ i : Fin n,reflectionBoard (m-1) ((c : ℤ)+1) i)=(n : ℤ)*(((c : ℤ)+m)%2) := by
  have hp (i : Fin n) : reflectionBoard (m-1) ((c : ℤ)+1) i=reflectionBoard m (c : ℤ) i+1 := by
    unfold reflectionBoard
    rw [center_predecessor m (by omega)]
    congr 2
    ring
  simp only [hp,Finset.sum_add_distrib,even_reflection_board_sum m (by omega) hn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  ring

theorem even_strict_top_phase (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m) (c : Fin n)
    (ht : reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n)=(n : ℤ)-(m-1 : ℕ)-1) :
    c=((m+3 : ℕ) : Fin n) := by
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have he := center_cast (n := n) (m-1) ((c : ℤ)+1-2*((2 : Fin n) : ℤ))
  change (reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n) : Fin n)=_ at he
  rw [ht] at he
  have htop : (n : ℤ)-(m-1 : ℕ)-1=(m : ℤ) := by omega
  rw [htop] at he
  simp only [hv2,Nat.cast_ofNat,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_one,
    Int.cast_ofNat,Int.cast_natCast,Fin.cast_val_eq_self,Nat.cast_add] at he ⊢
  linear_combination -he

theorem even_strict_phase_parity (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) :
    c=((m+3 : ℕ) : Fin n) ∨ (c.val+m)%2=0 := by
  by_cases hc : c=((m+3 : ℕ) : Fin n)
  · exact Or.inl hc
  · right
    have he := even_strict_lift_unique m (by omega) hn c hd hlo
    have hz := hd.1
    rw [he] at hz
    have hs := swap_perturbed_mass_drop (m-1) (by omega : 3 ≤ n) ((c : ℤ)+1)
    rw [even_strict_reflection_mass m hm hn c] at hs
    have hnt : ¬reflectionBoard (m-1) ((c : ℤ)+1) (2 : Fin n)=(n : ℤ)-(m-1 : ℕ)-1 :=
      fun ht => hc (even_strict_top_phase m hm hn c ht)
    rw [ite_eq_right hnt,sub_zero] at hs
    change (n : ℤ)*(((c : ℤ)+m)%2) ≤ ∑ i,evenStrictBase m c i at hs
    rw [hz] at hs
    have hn' : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
    have hmod : ((c : ℤ)+m)%2=0 := by
      have hr := Int.emod_nonneg ((c : ℤ)+m) (by decide : (2 : ℤ) ≠ 0)
      nlinarith
    have hcmod : ((c.val+m)%2 : ℕ)=0 := by
      have hcast : (((c.val+m)%2 : ℕ) : ℤ)=0 := by
        simpa only [Int.natCast_emod,Nat.cast_add,Nat.cast_ofNat] using hmod
      omega
    exact hcmod

theorem even_strict_phase_ne_boundary (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : IsLift even (c : ℤ) d)
    (hlo : ∀ i,1-(m : ℤ) ≤ d i) : c ≠ ((m+2 : ℕ) : Fin n) := by
  intro hc
  subst c
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have h12 : (1 : Fin n) ≠ 2 := by intro hh; have := congrArg Fin.val hh; omega
  have hb1 : evenBase m (((m+2 : ℕ)) : Fin n) 1= -(m : ℤ) := by
    rw [even_boundary_base m hm hn]
    simp only [evenException,hv1,ite_eq_right (by decide : ¬1=0),ite_eq_left (by decide : 1 ≤ 2)]
    ring
  have hb2 : evenBase m (((m+2 : ℕ)) : Fin n) 2= -(m : ℤ) := by
    rw [even_boundary_base m hm hn]
    simp only [evenException,hv2,ite_eq_right (by decide : ¬2=0),ite_eq_left (by decide : 2 ≤ 2)]
    ring
  rcases even_lift_single_raise m (by omega) hn (((m+2 : ℕ)) : Fin n) hd
      (fun i => by have := hlo i; omega) with he | ⟨a,ha⟩
  · have hh := hlo 1
    rw [he,hb1] at hh
    omega
  · by_cases ha1 : a=1
    · subst a
      have hh := hlo 2
      rw [ha] at hh
      simp only [raiseAt,ite_eq_right (Ne.symm h12),Nat.cast_zero,add_zero,hb2] at hh
      omega
    · have hh := hlo 1
      rw [ha] at hh
      simp only [raiseAt,ite_eq_right (Ne.symm ha1),Nat.cast_zero,add_zero,hb1] at hh
      omega

#print axioms even_strict_phase_parity
#print axioms even_strict_phase_ne_boundary
end LX.Antipode
