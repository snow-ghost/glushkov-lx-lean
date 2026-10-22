import LX.PhaseExchangePrice
import LX.HeadReserve

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.AffineLift
variable {n : ℕ} [NeZero n]

def raiseMinimum (d : Fin n → ℤ) (a : Fin n) : Fin n → ℤ :=
  phaseShift d (Finset.univ.erase a)

theorem raise_minimum_apply (d : Fin n → ℤ) (a i : Fin n) :
    raiseMinimum d a i=d i-1+if i=a then (n : ℤ) else 0 := by
  have hn : 1 ≤ n := NeZero.pos n
  unfold raiseMinimum phaseShift
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,Finset.mem_erase,Finset.mem_univ,and_true]
  by_cases hi : i=a <;> simp [hi] <;> ring

theorem raise_minimum_lift {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) :
    IsLift p (c+(n : ℤ)-1) (raiseMinimum d a) := by
  have hh := shift_lift hd (Finset.univ.erase a)
  have hn : 1 ≤ n := NeZero.pos n
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one,raiseMinimum,add_sub_assoc] using hh

/-- One chosen minimum can be lifted through the seam even when other minima
remain. The exchange change is independent of which tied minimum was chosen. -/
theorem raise_minimum_inversions {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : IsLift p c d) (a : Fin n) (hmin : ∀ i,d a ≤ d i)
    (hwidth : ∀ i j,d i-d j < (n : ℤ)) :
    (inversions (raiseMinimum d a) : ℤ)-inversions d=(n : ℤ)-1+2*d a := by
  have htop : ∀ i ∈ Finset.univ.erase a, ∀ j ∉ Finset.univ.erase a, d j ≤ d i := by
    intro i _ j hj
    have he : j=a := by simpa only [Finset.mem_erase,Finset.mem_univ,and_true,not_not] using hj
    rw [he]
    exact hmin i
  have hx := top_phase_inversions hd (Finset.univ.erase a) hwidth htop
  have hs := Finset.sum_erase_add Finset.univ d (Finset.mem_univ a)
  rw [hd.1] at hs
  have hn : 1 ≤ n := NeZero.pos n
  simp only [Finset.card_erase_of_mem (Finset.mem_univ a),Finset.card_univ,Fintype.card_fin,
    Nat.cast_sub hn,Nat.cast_one] at hx
  change (inversions (raiseMinimum d a) : ℤ)-inversions d=_ at hx
  nlinarith

theorem maximum_displacement_depth_zero (d : Fin n → ℤ) (a : Fin n)
    (hmax : ∀ i,d i ≤ d a) : backwardDepth d a=0 := by
  unfold backwardDepth
  apply Finset.sum_eq_zero
  intro j _
  have hj := hmax j
  have hval := (j-a).isLt
  have hn : (0 : ℤ)<n := by exact_mod_cast NeZero.pos n
  have hq : crossingNumerator d a j/(n : ℤ)<1 := by
    apply (Int.ediv_lt_iff_lt_mul hn).mpr
    unfold crossingNumerator
    omega
  simp only [crossing,neg_neg]
  omega

theorem raise_minimum_depth_zero (d : Fin n → ℤ) (a : Fin n)
    (hwidth : ∀ i j,d i-d j < (n : ℤ)) : backwardDepth (raiseMinimum d a) a=0 := by
  apply maximum_displacement_depth_zero
  intro i
  rw [raise_minimum_apply,raise_minimum_apply,ite_eq_left rfl]
  by_cases hi : i=a
  · subst i
    simp
  · rw [ite_eq_right hi]
    have hh := hwidth i a
    omega

theorem raise_unique_minimum_lower (d : Fin n → ℤ) (a : Fin n)
    (hmin : ∀ i,d a ≤ d i) (hunique : ∀ i,d i=d a → i=a) :
    ∀ i,d a ≤ raiseMinimum d a i := by
  intro i
  rw [raise_minimum_apply]
  by_cases hi : i=a
  · subst i
    rw [ite_eq_left rfl]
    have := NeZero.pos n
    omega
  · rw [ite_eq_right hi]
    have hh := hmin i
    have he : d i≠d a := fun he => hi (hunique i he)
    omega

/-- A literal word with every rotation charged, for any valid lift with a
head below the common depth bound. -/
theorem realized_head_reserve_word (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ)
    (hmax : ∀ i,backwardDepth d i ≤ h) (hhead : backwardDepth d 0 < h) :
    ∃ w : List Letter,p*eval w=1 ∧
      (w.length : ℤ) ≤ inversions d+((h : ℤ)+1)*((n : ℤ)-1)-1 := by
  have hl (i : Fin n) : labels d i=p i+(c : Fin n) := by
    simpa only [labels,Equiv.symm_symm] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.injective (add_right_cancel hij)
  obtain ⟨w,hw,hsort⟩ := exists_realized_scan hn p c d hd
  have hL := (hw.rotations_le_deadline hn hd.1 hi).trans
    (scan_deadline_head_reserve hn d hi h hmax hhead)
  refine ⟨paidWord (c : Fin n) w,hsort,?_⟩
  rw [hw.paid_length hn hd.1 hi,paidRotations]
  have hp := ((c : Fin n)-(w.count .l : Fin n)).isLt
  have hprod : 1 ≤ h*(n-1) := by
    have hh : 1 ≤ h := by omega
    have hn1 : 1 ≤ n-1 := by omega
    nlinarith
  have hr : (w.count .l : ℤ)+1 ≤ (h : ℤ)*((n : ℤ)-1) := by
    have hh : w.count .l+1 ≤ h*(n-1) := by omega
    have hn' : ((n-1 : ℕ) : ℤ)=(n : ℤ)-1 := by omega
    have hh' : (w.count .l : ℤ)+1 ≤ (h : ℤ)*((n-1 : ℕ) : ℤ) := by exact_mod_cast hh
    rwa [hn'] at hh'
  push_cast
  nlinarith

/-- If the unique minimum occupies the head, a one-phase change removes that
obstruction without increasing the maximum depth. -/
theorem unique_head_phase_rescue (hn : 2 ≤ n) (p : State n) (c : ℤ)
    (d : Fin n → ℤ) (hd : IsLift p.symm c d) (h : ℕ) (hh : 0 < h)
    (hzero : d 0= -(h : ℤ)) (hmin : ∀ i,d 0 ≤ d i)
    (hunique : ∀ i,d i=d 0 → i=0) (hwidth : ∀ i j,d i-d j < (n : ℤ)) :
    ∃ w : List Letter,p*eval w=1 ∧
      (w.length : ℤ) ≤ inversions d+((h : ℤ)+2)*((n : ℤ)-1)-2*h-1 := by
  let e := raiseMinimum d 0
  have he := raise_minimum_lift hd 0
  have hmax (i : Fin n) : backwardDepth e i ≤ h := by
    have hc := backward_depth_le_strip he (h : ℤ) (by
      intro j
      rw [← hzero]
      exact raise_unique_minimum_lower d 0 hmin hunique j) i
    exact_mod_cast hc
  have hhead : backwardDepth e 0 < h := by
    rw [show backwardDepth e 0=0 from raise_minimum_depth_zero d 0 hwidth]
    exact hh
  obtain ⟨w,hw,hprice⟩ := realized_head_reserve_word hn p (c+(n : ℤ)-1) e he h hmax hhead
  have hx := raise_minimum_inversions hd 0 hmin hwidth
  rw [hzero] at hx
  change (inversions e : ℤ)-inversions d=_ at hx
  exact ⟨w,hw,by nlinarith⟩

#print axioms raise_minimum_inversions
#print axioms raise_minimum_depth_zero
#print axioms unique_head_phase_rescue
end LX.AffineScan
