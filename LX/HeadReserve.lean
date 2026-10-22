import LX.FirstLapFormula
import LX.DepthCrowding
import LX.HeightReduction

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem maximum_depth_displacement {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (i : Fin n)
    (hmax : ∀ j, backwardDepth d j ≤ backwardDepth d i) :
    d i= -(backwardDepth d i : ℤ) := by
  have hh := displacement_add_depth hd i
  have hn := maximum_depth_nonpositive_crossings d i hmax
  have hz (j : Fin n) : (LRX.AffineLift.crossing d i j).toNat=0 := by have := hn j; omega
  simp only [hz,Nat.cast_zero,Finset.sum_const_zero] at hh
  omega

theorem first_lap_depth_le_pred (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h) :
    ∀ i, backwardDepth (sweep d (n-1)) i ≤ h-1 := by
  intro i
  rw [first_lap_depth_formula hn d hi]
  split_ifs with hi0
  · omega
  · unfold emittedDepth
    split_ifs
    · have hh := hmax i
      simp only [atDepth,Fin.cast_val_eq_self]
      omega
    · have hh := (prefix_minimum_le_iff (atDepth d) (i.val-1)
        (prefixMinimum (atDepth d) (i.val-1))).mp le_rfl 0 (by omega)
      change _ ≤ backwardDepth d 0 at hh
      omega

theorem queue_deadline_le (d : Fin n → ℤ) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) : queueDeadline d ≤ (n-1)*h := by
  unfold queueDeadline
  apply Finset.sup_le
  intro i _
  split_ifs with hz
  · omega
  · have hi := i.isLt
    have hh := Nat.mul_le_mul_left (n-1) (hmax i)
    have he : backwardDepth d i-1+1=backwardDepth d i := by omega
    rw [← he,Nat.mul_add,Nat.mul_one] at hh
    omega

/-- A head below the maximum depth saves a whole lap in the stopping bound. -/
theorem scan_deadline_head_reserve (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hi : Function.Injective (labels d)) (h : ℕ)
    (hmax : ∀ i, backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h) :
    scanDeadline d ≤ h*(n-1)-1 := by
  have hq := queue_deadline_le (sweep d (n-1)) (h-1)
    (first_lap_depth_le_pred hn d hi h hmax hhead)
  have hp : 1 ≤ h := by omega
  have he : (n-1)+(n-1)*(h-1)=h*(n-1) := by
    have hh : h-1+1=h := by omega
    calc
      _ = (h-1+1)*(n-1) := by ring
      _ = _ := by rw [hh]
  unfold scanDeadline
  omega

theorem left_run_inversions (hn : 2 ≤ n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (hi : Function.Injective (labels d)) (k : ℕ) :
    inversions (run (List.replicate k .l) d)=inversions d := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,run,step]
    rw [ih (rotate d) (by rw [rotate_sum,hb]) (rotate_injective d hi),rotate_inversions hn d hb hi]

#print axioms scan_deadline_head_reserve
end LX.AffineScan

namespace LX.AnchoredPhases
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.FiniteCuts LX.AffineScan
variable {n : ℕ} [NeZero n]

/-- The earliest descending position of the anchored finite permutation has
nonmaximal depth and is reached within n-h initial rotations. -/
theorem early_head_reserve (p : State n) (a : Fin n) (hh : 0 < height p a) :
    ∃ r : Fin n, r.val ≤ n-height p a ∧ backwardDepth (displacement p a) r < height p a := by
  let S := descendingPositions (permutation p a)
  have hS : S.Nonempty := Finset.card_pos.mp hh
  let r := S.min' hS
  have hr : r ∈ S := Finset.min'_mem S hS
  have hsub : S ⊆ Finset.Ici r := by
    intro i hi
    exact Finset.mem_Ici.mpr (Finset.min'_le S i hi)
  have hc := Finset.card_le_card hsub
  rw [Fin.card_Ici] at hc
  have hmax (i : Fin n) : backwardDepth (displacement p a) i ≤ height p a := by
    exact_mod_cast (candidate_price_components p a).2 i
  refine ⟨r,by change height p a ≤ n-r.val at hc; omega,?_⟩
  by_contra hnot
  have he : backwardDepth (displacement p a) r=height p a := by have := hmax r; omega
  have hd := maximum_depth_displacement (is_lift p a) r (by intro i; rw [he]; exact hmax i)
  rw [he] at hd
  have hr' : (permutation p a r).val < r.val := (mem_descendingPositions _ _).mp hr
  simp only [displacement,clockwiseRepresentative,ite_eq_left hr'] at hd
  have hn := r.isLt
  omega

/-- The initial rotation to a nonmaximal head is charged in full, as is the
final orientation. This bound does not assume that the chosen phase is majorized. -/
theorem candidate_head_reserve_word (hn : 2 ≤ n) (p : State n) (a : Fin n)
    (hh : 0 < height p a) :
    ∃ v : List Letter, p*eval v=1 ∧
      (v.length : ℤ) ≤ (height p a : ℤ)*(n-height p a-1)+
        (height p a+2)*(n-1)-height p a := by
  obtain ⟨r,hr,hhead⟩ := early_head_reserve p a hh
  let d := displacement p a
  let u : List Letter := List.replicate r.val .l
  let e := run u d
  have hd := is_lift p a
  have hl (i : Fin n) : labels d i=p i+(phase p a : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using LRX.AffineLift.lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  have he : e=LRX.RotationWords.localDisplacement d r := by
    funext i
    exact run_left_apply r.val d i
  have hei : Function.Injective (labels e) := run_injective hn u d hi
  have heb : ∑ i,e i=0 := (run_sum u d).trans hd.1
  have hem (i : Fin n) : backwardDepth e i ≤ height p a := by
    rw [he,recentered_backward_depth]
    exact_mod_cast (candidate_price_components p a).2 _
  have heh : backwardDepth e 0 < height p a := by
    rw [he,recentered_backward_depth]
    simpa only [LRX.AffineLift.rotation_power_apply,Fin.val_zero,Nat.cast_zero,
      Fin.cast_val_eq_self,zero_add] using hhead
  obtain ⟨w,hw⟩ := exists_scan_trace hn e heb hei
  have hL := (hw.rotations_le_deadline hn heb hei).trans
    (scan_deadline_head_reserve hn e hei (height p a) hem heh)
  have hX := hw.exchange_count hn heb hei
  have hIe : inversions e=inversions d := left_run_inversions hn d hd.1 hi r.val
  rw [hIe] at hX
  let v := paidWord (phase p a : Fin n) (u++w)
  have hv : p*eval v=1 := by
    apply sorting_word_of_zero hn p (phase p a : Fin n) d hl
    intro i
    rw [run_append]
    exact hw.run_zero i
  refine ⟨v,hv,?_⟩
  have hlen : v.length=r.val+w.count .l+w.count .x+
      ((phase p a : Fin n)-((u++w).count .l : Fin n)).val := by
    simp only [v,paidWord,List.length_append,List.length_replicate,u,length_eq_counts]
    omega
  have hp := ((phase p a : Fin n)-((u++w).count .l : Fin n)).isLt
  have hx := (candidate_price_components p a).1
  have hprod : 1 ≤ height p a*(n-1) := by
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hLc : (w.count .l : ℤ) ≤ (height p a : ℤ)*((n : ℤ)-1)-1 := by
    have hnat : w.count .l+1 ≤ height p a*(n-1) := by omega
    have hnat' : (w.count .l : ℤ)+1 ≤ (height p a : ℤ)*((n-1 : ℕ) : ℤ) := by exact_mod_cast hnat
    have hn' : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
    rw [hn'] at hnat'
    omega
  rw [hlen,hX]
  change (↑(r.val+w.count Letter.l+inversions d+_) : ℤ) ≤ _
  push_cast
  change (inversions d : ℤ) ≤ _ at hx
  have hh' : (height p a : ℤ) ≤ n := by have := height_lt p a; omega
  have hr' : (r.val : ℤ) ≤ (n : ℤ)-height p a := by omega
  nlinarith

/-- One less unit of height separation suffices after paying an initial
rotation to a nonmaximal head. This includes the second odd height branch. -/
theorem height_five_word (hn : 2 ≤ n) (p : State n) (a : Fin n)
    (ha : 2*height p a+5 ≤ n) :
    ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n := by
  by_cases hz : height p a=0
  · obtain ⟨w,hw,hprice⟩ := candidate_word_bound hn p a
    rw [hz] at hprice
    norm_num at hprice
    refine ⟨w,hw,?_⟩
    have hn5 : (5 : ℤ) ≤ n := by omega
    nlinarith [sq_nonneg ((n : ℤ)-5)]
  · obtain ⟨w,hw,hprice⟩ := candidate_head_reserve_word hn p a (by omega)
    refine ⟨w,hw,?_⟩
    have ha' : 2*(height p a : ℤ)+5 ≤ n := by exact_mod_cast ha
    have ht := mul_nonneg (Nat.cast_nonneg n : (0 : ℤ) ≤ n)
      (show (0 : ℤ) ≤ (n : ℤ)-2*height p a-5 by omega)
    nlinarith [sq_nonneg ((n : ℤ)-2*height p a-5)]

/-- Only the first odd height branch remains: the second is now paid by a
literal LX word with the required quadratic and linear terms. -/
theorem odd_unpaid_single_height (p : State n) (h : ℕ) (hn : n=2*h+1) (hn4 : 4 ≤ n)
    (hunpaid : ¬ ∃ w : List Letter, p*eval w=1 ∧
      4*(w.length : ℤ) < 3*(n : ℤ)^2-8*n+4*32) :
    ∃ a : Fin n, (∀ b, height p a ≤ height p b) ∧ height p a+1=h := by
  obtain ⟨a,ha,hcases⟩ := odd_unpaid_height_cases p h hn hn4 hunpaid
  refine ⟨a,ha,?_⟩
  rcases hcases with hfirst | hsecond
  · exact hfirst
  · obtain ⟨w,hw,hprice⟩ := height_five_word (by omega : 2 ≤ n) p a (by omega)
    exact False.elim (hunpaid ⟨w,hw,by linarith⟩)

#print axioms early_head_reserve
#print axioms candidate_head_reserve_word
#print axioms height_five_word
#print axioms odd_unpaid_single_height
end LX.AnchoredPhases
