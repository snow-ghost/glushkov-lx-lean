import LX.EvenSecondFewFixed

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- At the lower even height, reserving one extra lap aligns the final
orientation. The remaining cost is exactly the cyclic offset minus the
strip reserve, with no bound on fixed-point multiplicity. -/
theorem even_second_orientation_price (p : State n) (a : Fin n)
    (hh : 0 < height p a) (hn : n=2*height p a+4) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ)=3*(n : ℤ)^2-8*n+
        4*((((a-p a).val : ℕ) : ℤ)-anchorReserve p a) := by
  obtain ⟨r,_,hhead⟩ := exists_head_with_count (displacement p a) (height p a) hh
  let T := height p a*(n-1)+n+(a-p a).val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T]; have := r.isLt; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)=0 := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+n+((a-p a).val : ℤ) := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  refine ⟨w,hw,?_⟩
  unfold anchorReserve
  have hn' : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
  nlinarith

theorem even_second_unpaid_cyclic_gap (p : State n) (a : Fin n)
    (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    anchorReserve p a+32 ≤ ((a-p a).val : ℤ) := by
  have hh : 0 < height p a := by
    by_contra hnot
    have hz : height p a=0 := by omega
    obtain ⟨w,hw,hprice⟩ := candidate_word_bound (by omega : 2 ≤ n) p a
    rw [hz] at hprice
    norm_num at hprice
    have hn' : n=4 := by omega
    apply hunpaid
    refine ⟨w,hw,?_⟩
    rw [hn'] at *
    norm_num at *
    omega
  obtain ⟨w,hw,hprice⟩ := even_second_orientation_price p a hh hn
  have hnot : ¬4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32 := fun hp => hunpaid ⟨w,hw,hp⟩
  omega

/-- If a nonmaximal head occurs before the final orientation allowance is
exhausted, the initial rotations are absorbed entirely by that allowance. -/
theorem even_second_head_before_phase_word (p : State n) (a r : Fin n)
    (hn : n=2*height p a+4) (hr : r.val ≤ (a-p a).val+1)
    (hhead : backwardDepth (displacement p a) r < height p a) :
    ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n := by
  let T := height p a*(n-1)+(a-p a).val
  obtain ⟨w,hw,hlen⟩ := prefix_head_word_at_cursor (by omega : 2 ≤ n) p (phase p a)
    (displacement p a) (is_lift p a) (height p a) r
    (fun i => by exact_mod_cast (candidate_price_components p a).2 i) hhead T
    (by dsimp [T]; omega)
  have hphase : (phase p a : Fin n)-(T : Fin n)=0 := by
    dsimp only [T,phase]
    rw [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n)]
    simp only [Fin.natCast_self,Fin.cast_val_eq_self,Nat.cast_one,Int.cast_sub,Int.cast_natCast]
    ring
  rw [hphase,Fin.val_zero,add_zero] at hlen
  have hTi : (T : ℤ)=(height p a : ℤ)*((n : ℤ)-1)+((a-p a).val : ℤ) := by
    simp only [T,Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  have hlen' : (w.length : ℤ)=(inversions (displacement p a) : ℤ)+(T : ℤ) := by exact_mod_cast hlen
  have hcap := (candidate_price_components p a).1
  have hn' : (n : ℤ)=2*(height p a : ℤ)+4 := by exact_mod_cast hn
  have hgap := (a-p a).isLt
  exact ⟨w,hw,by nlinarith⟩

/-- The unpaid lower-height source fixes an entire initial interval whose
length is controlled by its actual final phase, not only a constant prefix. -/
theorem even_second_unpaid_phase_prefix (p : State n) (a : Fin n)
    (hn : n=2*height p a+4)
    (hunpaid : ¬ ∃ w : List Letter,p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    anchorReserve p a+32 ≤ ((a-p a).val : ℤ) ∧
      ∀ i : Fin n,i.val ≤ (a-p a).val+1 → permutation p a i=i := by
  refine ⟨even_second_unpaid_cyclic_gap p a hn hunpaid,?_⟩
  intro i hi
  by_contra hnot
  have hne : backwardDepth (displacement p a) i ≠ height p a :=
    fun he => hnot ((depth_eq_height_iff_fixed p a i).mp he)
  have hh := (candidate_price_components p a).2 i
  obtain ⟨w,hw,hprice⟩ := even_second_head_before_phase_word p a i hn hi (by omega)
  exact hunpaid ⟨w,hw,by linarith⟩

#print axioms even_second_orientation_price
#print axioms even_second_head_before_phase_word
#print axioms even_second_unpaid_phase_prefix
end LX.AnchoredPhases
