import LX.AntipodeCandidates
import LX.DirectedTokenLower
import LX.FiniteLowerDeadline
import LX.LiftedScanBridge
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- The endpoint residue pays the exact extra rotation missing from the
plain token budget. All quantities come from the same literal word. -/
theorem ScanTrace.paid_token_bound (hn : 2 ≤ n) {p : State n} {c : Fin n}
    {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift p (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) :
    (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*targets d i+((-p.symm i : Fin n) : ℤ) ≤
      (paidRotations c g : ℤ) := by
  have hz (j : Fin n) : run (paidWord c g) d j=0 := by
    simp only [paidWord,run_append,run_left_apply]
    exact hg.run_zero _
  have hcount : (paidWord c g).count .l=paidRotations c g := by simp [paidWord,paidRotations]
  have ht := DirectedTokenLower.word_cursor_lower hn (paidWord c g) i
  rw [LiftedScan.exact_positions_of_zero hn d (paidWord c g) hz i,
    DirectedTokenLower.cursor_eq_left_count,hcount] at ht
  let T : ℤ := (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*targets d i
  let R : ℤ := (paidRotations c g : ℤ)
  have hnonneg : 0 ≤ R-T := by change T ≤ R at ht; omega
  have hF : (targets d i : Fin n)=p.symm i+c := by
    simpa only [targets,Int.cast_add,Int.cast_natCast,Fin.cast_val_eq_self] using
      LRX.AffineLift.lift_residue hd i
  have hphase := paid_rotations_phase c g
  have hcast : ((R-T : ℤ) : Fin n)= -p.symm i := by
    simp only [R,T,Int.cast_sub,Int.cast_mul,Int.cast_natCast,Fin.natCast_self,
      Int.cast_one,hF,hphase]
    ring
  have hr := Int.emod_nonneg (R-T) (show (n : ℤ) ≠ 0 by exact_mod_cast NeZero.ne n)
  have hq := Int.ediv_nonneg hnonneg (show (0 : ℤ) ≤ n by positivity)
  have he := Int.ediv_mul_add_emod (R-T) (n : ℤ)
  have hval : (((R-T : ℤ) : Fin n) : ℤ) ≤ R-T := by
    simp only [Fin.val_intCast,Int.toNat_of_nonneg hr]
    have hm := mul_nonneg hq (show (0 : ℤ) ≤ n by positivity)
    omega
  rw [hcast] at hval
  change T+((-p.symm i : Fin n) : ℤ) ≤ R
  omega

end LX.AffineScan

namespace LX.Antipode
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- At height m, every ordinary position already pays the even target.
Only the two transposed positions can escape this estimate. -/
theorem even_bottom_ordinary_paid (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g) (i : Fin n) (hi : 3 ≤ i.val)
    (hdi : d i= -(m : ℤ)) :
    3*m^2-4*m+3 ≤ inversions d+paidRotations c g := by
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hi1 : i ≠ 1 := by intro he; have := congrArg Fin.val he; omega
  have hi2 : i ≠ 2 := by intro he; have := congrArg Fin.val he; omega
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
  simp only [targets,hdi] at ht
  have hip : ((i.val-1 : ℕ) : ℤ)=(i : ℤ)-1 := by omega
  rw [hip] at ht
  have hI := even_lift_inversions_lower m hm hn hd
  have hI' : (m : ℤ)*(m-1) ≤ (inversions d : ℤ)+1 := by
    have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    have hh : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions d : ℤ)+1 := by exact_mod_cast hI
    rwa [hm1] at hh
  have hn' : (n : ℤ)=2*m := by omega
  have hi' : (3 : ℤ) ≤ i := by omega
  have hlen : 3*(m : ℤ)^2-4*m+3 ≤ (inversions d : ℤ)+paidRotations c g := by nlinarith
  have hsub : ((3*m^2-4*m : ℕ) : ℤ)=3*(m : ℤ)^2-4*m := by
    rw [Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)]
    push_cast
    rfl
  exact_mod_cast (show ((3*m^2-4*m+3 : ℕ) : ℤ) ≤ (inversions d : ℤ)+paidRotations c g by
    push_cast; rw [hsub]; exact hlen)

theorem even_unpaid_bottom_positions (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-4*m+3)
    (i : Fin n) (hdi : d i= -(m : ℤ)) : i.val=1 ∨ i.val=2 := by
  by_cases hi0 : i.val=0
  · have ht := hg.paid_token_bound (by omega : 2 ≤ n) hd i
    have hqnonneg : (0 : ℤ) ≤ ((-(even : State n).symm i : Fin n) : ℤ) := by positivity
    simp only [targets,hdi,hi0,Nat.zero_sub,Nat.cast_zero,zero_add,mul_zero,zero_sub] at ht
    have hI := even_lift_inversions_lower m hm hn hd
    have hI' : (m : ℤ)*((m-1 : ℕ) : ℤ) ≤ (inversions d : ℤ)+1 := by exact_mod_cast hI
    have hu' : (inversions d : ℤ)+(paidRotations c g : ℤ) < ((3*m^2-4*m+3 : ℕ) : ℤ) := by
      exact_mod_cast hu
    have hm1 : ((m-1 : ℕ) : ℤ)=(m : ℤ)-1 := by omega
    rw [hm1] at hI'
    rw [Nat.cast_add,Nat.cast_sub (by nlinarith : 4*m ≤ 3*m^2)] at hu'
    push_cast at hu'
    have hn' : (n : ℤ)=2*m := by omega
    have hm' : (3 : ℤ) ≤ m := by omega
    nlinarith
  · by_contra hnot
    have hh := even_bottom_ordinary_paid m hm hn hd hg i (by omega) hdi
    omega

theorem even_unpaid_boundary_phase (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {c : Fin n} {d : Fin n → ℤ} (hd : LRX.AffineLift.IsLift even (c : ℤ) d)
    {g : List Letter} (hg : ScanTrace d g)
    (hu : inversions d+paidRotations c g < 3*m^2-4*m+3)
    (he : ∃ i,d i= -(m : ℤ)) : c=((m+2 : ℕ) : Fin n) := by
  obtain ⟨i,hdi⟩ := he
  have hpos := even_unpaid_bottom_positions m hm hn hd hg hu i hdi
  have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
  have hv2 : (2 : Fin n).val=2 := Nat.mod_eq_of_lt (by omega : 2 < n)
  have hsum : i+(Equiv.swap (1 : Fin n) 2) i=3 := by
    rcases hpos with hi | hi
    · have he : i=1 := Fin.ext (by omega)
      subst i
      simp only [Equiv.swap_apply_left]
      norm_num
    · have he : i=2 := Fin.ext (by omega)
      subst i
      simp only [Equiv.swap_apply_right]
      norm_num
  have hh := LRX.AffineLift.lift_residue hd i
  rw [hdi] at hh
  simp only [Int.cast_natCast,Fin.cast_val_eq_self] at hh
  simp only [even,Equiv.symm_symm,Equiv.Perm.mul_apply,LRX.WordReflection.reflection_apply] at hh
  have hnfin : (2 : Fin n)*(m : Fin n)=0 := by
    have hz : (n : Fin n)=0 := Fin.natCast_self n
    have hc := congrArg (fun t : ℕ => (t : Fin n)) hn
    rw [hz] at hc
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using hc.symm
  simp only [Int.cast_neg,Int.cast_natCast,Nat.cast_add,Nat.cast_ofNat] at hh ⊢
  linear_combination -hh+hsum-hnfin


#print axioms even_unpaid_bottom_positions
#print axioms even_unpaid_boundary_phase
end LX.Antipode
