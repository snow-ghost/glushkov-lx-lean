import LX.EvenOneFixedObstruction

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Charge an initial rotation and retain the exact final orientation.
The added prefix does not have to be part of a greedy scan trace. -/
theorem prefix_head_word_at_cursor (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ) (r : Fin n)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d r < h)
    (T : ℕ) (hT : r.val+h*(n-1)-1 ≤ T) :
    ∃ v : List Letter,p*eval v=1 ∧
      v.length=inversions d+T+((c : Fin n)-(T : Fin n)).val := by
  let u : List Letter := List.replicate r.val .l
  let e := run u d
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have he : e=LRX.RotationWords.localDisplacement d r := by
    funext i
    exact run_left_apply r.val d i
  have hei : Function.Injective (labels e) := run_injective hn u d hi
  have heb : ∑ i,e i=0 := (run_sum u d).trans hd.1
  have hem (i : Fin n) : backwardDepth e i ≤ h := by
    rw [he,recentered_backward_depth]
    exact hmax _
  have heh : backwardDepth e 0 < h := by
    rw [he,recentered_backward_depth]
    simpa only [LRX.AffineLift.rotation_power_apply,Fin.val_zero,Nat.cast_zero,
      Fin.cast_val_eq_self,zero_add] using hhead
  obtain ⟨w,hw⟩ := exists_scan_trace hn e heb hei
  have hL := (hw.rotations_le_deadline hn heb hei).trans
    (scan_deadline_head_reserve hn e hei h hem heh)
  have hX := hw.exchange_count hn heb hei
  have hIe : inversions e=inversions d := left_run_inversions hn d hd.1 hi r.val
  rw [hIe] at hX
  let v := u++w
  have hprod : 1 ≤ h*(n-1) := by
    have hh : 1 ≤ h := by omega
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hvL : v.count .l ≤ T := by
    simp only [v,u,List.count_append,List.count_replicate,beq_self_eq_true,ite_true]
    omega
  have hvX : v.count .x=inversions d := by simp [v,u,hX,List.count_replicate]
  have hvzero (i : Fin n) : run v d i=0 := by
    rw [show v=u++w from rfl,run_append]
    exact hw.run_zero i
  let z := v++List.replicate (T-v.count .l) .l
  have hzL : z.count .l=T := by
    simp only [z,List.count_append,List.count_replicate,beq_self_eq_true,ite_true]
    omega
  have hzX : z.count .x=inversions d := by simp [z,hvX,List.count_replicate]
  have hzzero (i : Fin n) : run z d i=0 := by
    simp only [z,run_append,run_left_apply]
    exact hvzero _
  have hzlen : z.length=T+inversions d := by rw [length_eq_counts,hzL,hzX]
  refine ⟨paidWord (c : Fin n) z,sorting_word_of_zero hn p (c : Fin n) d hl z hzzero,?_⟩
  simp only [paidWord,List.length_append,List.length_replicate,hzlen,hzL]
  omega

end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan LRX.FiniteCuts
variable {n : ℕ} [NeZero n]

theorem one_fixed_nonmaximal_elsewhere (p : State n) (a r : Fin n)
    (hf : (fixedPositions (permutation p a)).card=1) (hr : r ≠ a) :
    backwardDepth (displacement p a) r < height p a := by
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  by_contra hnot
  have he : backwardDepth (displacement p a) r=height p a := by have := hmax r; omega
  have hd := maximum_depth_displacement (is_lift p a) r (by intro i; rw [he]; exact hmax i)
  rw [he,displacement_offset] at hd
  have hz : cyclicOffset p a r=0 := Fin.ext (by simp only [Fin.val_zero]; omega)
  exact hr (one_fixed_last_offset p a hf r (sub_eq_zero.mp hz))

/-- The small terminal corner is paid by starting the scan just after the
unique fixed position, with the prefix and final orientation both explicit. -/
theorem even_one_fixed_corner_word (p : State n) (a : Fin n) (hn22 : 22 ≤ n)
    (hn : n=2*height p a+2) (hf : (fixedPositions (permutation p a)).card=1)
    (hcorner : a.val+(-p a).val < 8) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := by
  let r : Fin n := ⟨a.val+1,by omega⟩
  have hr : r ≠ a := by intro he; have hv := congrArg Fin.val he; dsimp [r] at hv; omega
  let T := height p a*(n-1)+a.val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i)
    (one_fixed_nonmaximal_elsewhere p a r hf hr) T (by dsimp [r,T]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)= -p a := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+a.val := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ)+((-p a).val : ℤ) := by
    exact_mod_cast hlen
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+2 := by exact_mod_cast hn
  have hc : (a.val : ℤ)+((-p a).val : ℤ) ≤ 7 := by omega
  exact ⟨w,hw,by nlinarith⟩

/-- When the unique fixed position is at the initial head, one rotation
is sufficient and aligns exactly with h*(n-1). No full lap is charged. -/
theorem even_one_fixed_head_price (p : State n) (hn4 : 4 ≤ n)
    (hn : n=2*height p 0+2) (hf : (fixedPositions (permutation p 0)).card=1) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+4*(((-p 0).val : ℤ)+1-anchorReserve p 0) := by
  have hv : (1 : Fin n).val=1 := by simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hne : (1 : Fin n) ≠ 0 := by intro h; have hh := congrArg Fin.val h; rw [hv,Fin.val_zero] at hh; omega
  let T := height p 0*(n-1)
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p 0)
    (displacement p 0) (is_lift p 0) (height p 0) 1
    (fun i => by exact_mod_cast (candidate_price_components p 0).2 i)
    (one_fixed_nonmaximal_elsewhere p 0 1 hf hne) T (by rw [hv]; dsimp [T]; omega)
  have hphase : (phase p 0 : Fin n)-(T : Fin n)= -p 0 := by
    dsimp only [T,phase]
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.val_zero,Nat.cast_zero,Int.cast_zero,
      Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase] at hlen
  have hTi : (T : ℤ)=(height p 0 : ℤ)*((n : ℤ)-1) := by
    simp only [T,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p 0) : ℤ)+(T : ℤ)+((-p 0).val : ℤ) := by
    exact_mod_cast hlen
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p 0 : ℤ)+2 := by exact_mod_cast hn
  nlinarith

/-- The corner obstruction disappears, and the head case satisfies the
same large cyclic-offset condition as the backward case. -/
theorem even_unpaid_one_fixed_cyclic_gap (hn4 : 4 ≤ n) (p : State n)
    (m : ℕ) (hn : n=2*m)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n,GlobalMinimum p a ∧ height p a+1=m ∧
      (fixedPositions (permutation p a)).card=1 ∧
      (m : ℤ)*(m-1)-inversions (displacement p a)+31 ≤ ((a-p a).val : ℤ) ∧
      (a=0 ∨ (0 < (p a).val ∧ (p a).val < a.val)) := by
  have hn22 : 22 ≤ n := by
    by_contra hnot
    obtain ⟨w,hw,hprice⟩ := exists_head_reserve_quadratic_word hn4 p⁻¹
    apply hunpaid
    refine ⟨w,by rw [hw,mul_inv_cancel],?_⟩
    have hs : (n : ℤ)<22 := by omega
    nlinarith
  obtain ⟨a,ha,hh,hf,hcases⟩ := even_unpaid_one_fixed_geometry hn4 p m hn hunpaid
  refine ⟨a,ha,hh,hf,?_⟩
  rcases hcases with he | hcorner | hback
  · subst a
    obtain ⟨w,hw,hprice⟩ := even_one_fixed_head_price p hn4 (by omega) hf
    have hp : ¬4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := fun hp => hunpaid ⟨w,hw,hp⟩
    have hr : anchorReserve p 0=(m : ℤ)*(m-1)-inversions (displacement p 0) := by
      unfold anchorReserve
      have hn' : (n : ℤ)=2*(m : ℤ) := by exact_mod_cast hn
      have hh' : (height p 0 : ℤ)+1=m := by exact_mod_cast hh
      nlinarith
    rw [hr] at hprice
    exact ⟨by simp only [zero_sub]; omega,Or.inl rfl⟩
  · exact False.elim (hunpaid (even_one_fixed_corner_word p a hn22 (by omega) hf hcorner))
  · refine ⟨?_,Or.inr ⟨hback.1,hback.2.1⟩⟩
    rw [Fin.coe_sub_iff_le.mpr (show p a ≤ a from le_of_lt hback.2.1)]
    have hp := hback.2.2
    omega

#print axioms even_one_fixed_corner_word
#print axioms even_one_fixed_head_price
#print axioms even_unpaid_one_fixed_cyclic_gap
end LX.AnchoredPhases
