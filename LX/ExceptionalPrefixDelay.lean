import LX.DepthCrowding
import LX.FiniteLowerDeadline
import LX.QueueDeadlineLower
import Mathlib

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

/-- Every tail target at least one period ahead contributes an inverted
predecessor of the head. -/
theorem tail_head_depth_lower (d : Fin n → ℤ) (a : Fin n)
    (ht : ∀ i : Fin n,a ≤ i → targets d 0+n ≤ targets d i) :
    n-a.val ≤ backwardDepth d 0 := by
  have hn : (0 : ℤ) < n := by exact_mod_cast NeZero.pos n
  have hh (i : Fin n) : (if a ≤ i then 1 else 0) ≤
      ((targets d i-targets d 0)/(n : ℤ)).toNat := by
    split_ifs with hi
    · have htarget := ht i hi
      have hq := Int.ediv_le_ediv hn
        (show (n : ℤ) ≤ targets d i-targets d 0 by omega)
      rw [Int.ediv_self (ne_of_gt hn)] at hq
      omega
    · exact Nat.zero_le _
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hh i)
  have hset : (Finset.univ.filter fun i : Fin n => a ≤ i)=Finset.Ici a := by ext; simp
  convert hsum using 1 <;>
    simp only [Finset.sum_boole,hset,Fin.card_Ici,← backward_depth_head] <;> rfl

theorem neg_displacement_le_depth {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) (i : Fin n) :
    -d i ≤ (backwardDepth d i : ℤ) := by
  have hh := displacement_add_depth hd i
  have hs : (0 : ℤ) ≤ ∑ j : Fin n,((LRX.AffineLift.crossing d i j).toNat : ℤ) :=
    Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)
  omega

/-- Exceptional lift in the even antipode family. This definition alone
does not assert that it is the only unpaid bounded lift. -/
def evenException (m : ℕ) (i : Fin n) : ℤ :=
  if i.val=0 then 4-(m : ℤ)
  else if i.val ≤ 2 then 1-(m : ℤ)
  else if i.val ≤ m+1 then (m : ℤ)+4-2*i.val
  else 3*(m : ℤ)+4-2*i.val

/-- Exceptional lift in the odd antipode family. -/
def oddException (m : ℕ) (i : Fin n) : ℤ :=
  if i.val=0 then 2-(m : ℤ)
  else if i.val=1 then -(m : ℤ)
  else if i.val=2 then 0
  else if i.val ≤ m+1 then (m : ℤ)+4-2*i.val
  else 3*(m : ℤ)+4-2*i.val

private theorem lift_labels_injective {p : State n} {c : ℤ} {d : Fin n → ℤ}
    (hd : LRX.AffineLift.IsLift p c d) : Function.Injective (labels d) := by
  have hl (i : Fin n) : labels d i=p.symm i+(c : Fin n) := by
    simpa only [labels] using LRX.AffineLift.lift_residue hd i
  intro i j hij
  rw [hl,hl] at hij
  exact p.symm.injective (add_right_cancel hij)

/-- The even exceptional lift needs one more rotation than the token
budget permits. The phase condition will turn that one into a full lap. -/
theorem even_exception_rotation_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LRX.AffineLift.IsLift p c (evenException (n := n) m))
    (w : List Letter) (hw : ∀ i,run w (evenException (n := n) m) i=0) :
    (n-1)*(m-2)+2 ≤ w.count .l := by
  have hn2 : 2 ≤ n := by omega
  have hcast (k : ℕ) (hk : k < n) : (k : Fin n).val=k := Nat.mod_eq_of_lt hk
  have hhead : m-2 ≤ backwardDepth (evenException (n := n) m) 0 := by
    have hh := tail_head_depth_lower (evenException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro i hi
      have hil : i.val < n := i.isLt
      have hip : m+2 ≤ i.val := hi
      simp only [targets,evenException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : i.val ≠ 0),ite_eq_right (by omega : ¬i.val ≤ 2),
        ite_eq_right (by omega : ¬i.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-2 by omega] using hh
  have hpref : ∀ k < 3,m-2 ≤ atDepth (evenException (n := n) m) k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k; exact hhead
    · have hh := neg_displacement_le_depth hd (k : Fin n)
      simp only [evenException,hcast k (by omega),ite_eq_right hk0,
        ite_eq_left (by omega : k ≤ 2)] at hh
      change m-2 ≤ backwardDepth (evenException (n := n) m) (k : Fin n)
      omega
  have hr : ∀ i : Fin 3,atTarget (evenException (n := n) m) i.val ≤ atTarget (evenException (n := n) m) 3 := by
    intro i
    have hil := i.isLt
    simp only [atTarget,evenException,hcast i.val (by omega),hcast 3 (by omega)]
    split_ifs <;> omega
  have hh := prefix_record_rotation_lower hn2 (evenException (n := n) m) hd.1
    (lift_labels_injective hd) 3 (m-2) (by omega) (by omega) (by omega) hr hpref w hw
  omega

/-- The same one-rotation obstruction in the odd exceptional lift. -/
theorem odd_exception_rotation_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LRX.AffineLift.IsLift p c (oddException (n := n) m))
    (w : List Letter) (hw : ∀ i,run w (oddException (n := n) m) i=0) :
    (n-1)*(m-1)+1 ≤ w.count .l := by
  have hn2 : 2 ≤ n := by omega
  have hcast (k : ℕ) (hk : k < n) : (k : Fin n).val=k := Nat.mod_eq_of_lt hk
  have hhead : m-1 ≤ backwardDepth (oddException (n := n) m) 0 := by
    have hh := tail_head_depth_lower (oddException (n := n) m) (⟨m+2,by omega⟩ : Fin n) (by
      intro i hi
      have hil : i.val < n := i.isLt
      have hip : m+2 ≤ i.val := hi
      simp only [targets,oddException,Fin.val_zero,Nat.cast_zero,ite_true,zero_add]
      rw [ite_eq_right (by omega : i.val ≠ 0),ite_eq_right (by omega : i.val ≠ 1),
        ite_eq_right (by omega : i.val ≠ 2),ite_eq_right (by omega : ¬i.val ≤ m+1)]
      omega)
    simpa only [show n-(m+2)=m-1 by omega] using hh
  have hpref : ∀ k < 2,m-1 ≤ atDepth (oddException (n := n) m) k := by
    intro k hk
    by_cases hk0 : k=0
    · subst k; exact hhead
    · have hk1 : k=1 := by omega
      subst k
      have hh := neg_displacement_le_depth hd (1 : Fin n)
      have hv1 : (1 : Fin n).val=1 := Nat.mod_eq_of_lt (by omega : 1 < n)
      simp only [oddException,hv1,ite_eq_right (by decide : ¬1=0),ite_true] at hh
      change m-1 ≤ backwardDepth (oddException (n := n) m) (1 : Fin n)
      omega
  have hr : ∀ i : Fin 2,atTarget (oddException (n := n) m) i.val ≤ atTarget (oddException (n := n) m) 2 := by
    intro i
    have hil := i.isLt
    simp only [atTarget,oddException,hcast i.val (by omega),hcast 2 (by omega)]
    split_ifs <;> omega
  have hh := prefix_record_rotation_lower hn2 (oddException (n := n) m) hd.1
    (lift_labels_injective hd) 2 (m-1) (by omega) (by omega) (by omega) hr hpref w hw
  omega

/-- The extra rotation forces a full phase period in the even family. -/
theorem even_exception_paid_rotation_lower (m : ℕ) (hm : 3 ≤ m) (hn : n=2*m)
    {p : State n} {c : ℤ} (hd : LRX.AffineLift.IsLift p c (evenException (n := n) m))
    {g : List Letter} (hg : ScanTrace (evenException (n := n) m) g) :
    (n-1)*(m-2)+1+n ≤ paidRotations ((m+3 : ℕ) : Fin n) g := by
  have hh := even_exception_rotation_lower m hm hn hd g hg.run_zero
  have hrot : g.count .l ≤ paidRotations ((m+3 : ℕ) : Fin n) g := by
    simp only [paidRotations]; omega
  have he : (n-1)*(m-2)+1=n*(m-3)+(m+3) := by
    have hnsub : n-1+1=n := by omega
    have hm2 : m-2+2=m := by omega
    have hm3 : m-3+3=m := by omega
    nlinarith
  have hphase : (((n-1)*(m-2)+1 : ℕ) : Fin n)=((m+3 : ℕ) : Fin n) := by
    rw [he]
    simp only [Nat.cast_add,Nat.cast_mul,Fin.natCast_self,zero_mul,zero_add]
  exact phase_order_gap _ _ _ hphase (paid_rotations_phase _ _) (by omega)

/-- The extra rotation forces a full phase period in the odd family. -/
theorem odd_exception_paid_rotation_lower (m : ℕ) (hm : 2 ≤ m) (hn : n=2*m+1)
    {p : State n} {c : ℤ} (hd : LRX.AffineLift.IsLift p c (oddException (n := n) m))
    {g : List Letter} (hg : ScanTrace (oddException (n := n) m) g) :
    (n-1)*(m-1)+n ≤ paidRotations ((m+2 : ℕ) : Fin n) g := by
  have hh := odd_exception_rotation_lower m hm hn hd g hg.run_zero
  have hrot : g.count .l ≤ paidRotations ((m+2 : ℕ) : Fin n) g := by
    simp only [paidRotations]; omega
  have he : (n-1)*(m-1)=n*(m-2)+(m+2) := by
    have hnsub : n-1+1=n := by omega
    have hm1 : m-1+1=m := by omega
    have hm2 : m-2+2=m := by omega
    nlinarith
  have hphase : (((n-1)*(m-1) : ℕ) : Fin n)=((m+2 : ℕ) : Fin n) := by
    rw [he]
    simp only [Nat.cast_add,Nat.cast_mul,Fin.natCast_self,zero_mul,zero_add]
  exact phase_order_gap _ _ _ hphase (paid_rotations_phase _ _) (by omega)

#print axioms even_exception_rotation_lower
#print axioms odd_exception_rotation_lower
#print axioms even_exception_paid_rotation_lower
#print axioms odd_exception_paid_rotation_lower
end LX.AffineScan
