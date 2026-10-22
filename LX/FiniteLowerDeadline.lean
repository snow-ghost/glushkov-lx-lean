import LX.FiniteGreedyPrices
import LX.GreedyLowerCertificate

namespace LX.AffineScan
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

theorem paid_rotations_phase (c : Fin n) (g : List Letter) :
    (paidRotations c g : Fin n)=c := by
  simp only [paidRotations,Nat.cast_add,Fin.cast_val_eq_self]
  ring

theorem phase_order_gap (c : Fin n) (u v : ℕ) (hu : (u : Fin n)=c)
    (hv : (v : Fin n)=c) (hlt : u < v) : u+n ≤ v := by
  have hu' : u % n=c.val := by have h := congrArg Fin.val hu; simpa using h
  have hv' : v % n=c.val := by have h := congrArg Fin.val hv; simpa using h
  have hd := Nat.mod_add_div u n
  have he := Nat.mod_add_div v n
  have hnpos := NeZero.pos n
  have hq : u/n+1 ≤ v/n := by
    by_contra hnot
    have hm := Nat.mul_le_mul_left n (show v/n ≤ u/n by omega)
    omega
  have hm := Nat.mul_le_mul_left n hq
  rw [Nat.mul_add,Nat.mul_one] at hm
  omega

/-- Last cursor in this phase that could still give a price below B. -/
def lowerDeadline (n I B c : ℕ) : ℕ := c+n*((B-I-1-c)/n)

theorem lower_deadline_phase (I B : ℕ) (c : Fin n) :
    (lowerDeadline n I B c.val : Fin n)=c := by
  simp [lowerDeadline,Nat.cast_add,Nat.cast_mul]

theorem lower_deadline_next_paid (I B : ℕ) (c : Fin n)
    (hcheap : I+c.val < B) : B ≤ I+lowerDeadline n I B c.val+n := by
  have hd := Nat.mod_add_div (B-I-1-c.val) n
  have hr := Nat.mod_lt (B-I-1-c.val) (NeZero.pos n)
  unfold lowerDeadline
  omega

theorem lower_deadline_unpaid (I B : ℕ) (c : Fin n)
    (hcheap : I+c.val < B) : I+lowerDeadline n I B c.val < B := by
  have hd := Nat.mod_add_div (B-I-1-c.val) n
  unfold lowerDeadline
  omega

/-- A computable certificate: either the starting phase already costs
enough, or the greedy board is nonzero at the last affordable cursor. -/
def LowerDeadlineCertificate (B : ℕ) (c : Fin n) (d : Fin n → ℤ) : Prop :=
  B ≤ inversions d+c.val ∨
    ¬∀ i,saturatedSweep d (lowerDeadline n (inversions d) B c.val) i=0

theorem deadline_certificate_price (hn : 2 ≤ n) (B : ℕ) (c : Fin n) (d : Fin n → ℤ)
    (hb : ∑ i,d i=0) (g : List Letter)
    (hg : ScanTrace d g) (hc : LowerDeadlineCertificate B c d) :
    B ≤ inversions d+paidRotations c g := by
  have hphase := paid_rotations_phase c g
  have hcmin : c.val ≤ paidRotations c g := by
    have he := congrArg Fin.val hphase
    simp only [Fin.val_natCast] at he
    rw [← he]
    exact Nat.mod_le _ _
  by_cases hcheap : B ≤ inversions d+c.val
  · omega
  · have hnot := hc.resolve_left hcheap
    obtain ⟨i,hi0⟩ := not_forall.mp hnot
    let T := lowerDeadline n (inversions d) B c.val
    have hzero : ∀ j,run (paidWord c g) d j=0 := by
      intro j
      simp only [paidWord,run_append,run_left_apply]
      exact hg.run_zero _
    have hrot := rotations_gt_of_greedy_nonzero hn d hb T i hi0 (paidWord c g) hzero
    have hcount : (paidWord c g).count .l=paidRotations c g := by
      simp [paidWord,paidRotations]
    rw [hcount] at hrot
    have hgap := phase_order_gap c T (paidRotations c g) (lower_deadline_phase _ _ c) hphase hrot
    have hnext := lower_deadline_next_paid (inversions d) B c (by omega)
    change B ≤ inversions d+T+n at hnext
    omega

end LX.AffineScan

namespace LX
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open AffineScan LRX.AffineLift
variable {n : ℕ} [NeZero n]

/-- Kernel-checkable lower certificate over n phases and finite subsets.
The previous shortest-word reduction proves completeness of the domain. -/
theorem length_lower_of_deadline_certificates (hn : 2 ≤ n) (p : State n) (B : ℕ)
    (hc : ∀ (c : Fin n) (S : Finset (Fin n)),BinaryLift.ValidSelection p c S →
      LowerDeadlineCertificate B c (BinaryLift.displacement p c S)) : B ≤ length p := by
  apply (length_lower_iff_selected_greedy_prices hn p B).mpr
  intro c S g hS hg
  have hd := BinaryLift.selected_lift p c S hS
  exact deadline_certificate_price hn B c _ hd.1 g hg (hc c S hS)

/-- Failure of the certificate constructs a literal word below B. Thus
the finite test is exact, rather than only a sufficient lower-bound test. -/
theorem failed_deadline_certificate_word (hn : 2 ≤ n) (p : State n) (B : ℕ)
    (c : Fin n) (d : Fin n → ℤ) (hd : IsLift p (c : ℤ) d)
    (hc : ¬LowerDeadlineCertificate B c d) :
    ∃ w : List Letter,eval w=p ∧ w.length < B := by
  classical
  have hcheap : inversions d+c.val < B := by
    have hh : ¬B ≤ inversions d+c.val := fun h => hc (Or.inl h)
    omega
  let T := lowerDeadline n (inversions d) B c.val
  have hz : ∀ i,saturatedSweep d T i=0 := by
    by_contra h
    exact hc (Or.inr h)
  have hl (i : Fin n) : labels d i=p.symm i+c := by
    simpa only [labels,Int.cast_natCast,Fin.cast_val_eq_self] using lift_residue hd i
  have hi : Function.Injective (labels d) := by
    intro i j hij
    rw [hl,hl] at hij
    exact p.symm.injective (add_right_cancel hij)
  obtain ⟨g,hg⟩ := exists_scan_trace hn d hd.1 hi
  have hT : g.count .l ≤ T := hg.rotations_le_of_compare_zero hn T hz
  obtain ⟨w,hw,_,hlen⟩ := hg.word_at_cursor_zero hn p.symm c hd.1 hi hl T hT
  have hphase : (T : Fin n)=c := lower_deadline_phase _ _ c
  rw [hphase,sub_self,Fin.val_zero,add_zero] at hlen
  have he : p⁻¹*eval w=1 := by simpa only [Equiv.Perm.inv_def] using hw
  refine ⟨w,(inv_mul_eq_one.mp he).symm,?_⟩
  rw [hlen]
  exact lower_deadline_unpaid _ _ c hcheap

theorem length_lower_iff_deadline_certificates (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    B ≤ length p ↔ ∀ (c : Fin n) (S : Finset (Fin n)),BinaryLift.ValidSelection p c S →
      LowerDeadlineCertificate B c (BinaryLift.displacement p c S) := by
  constructor
  · intro hB c S hS
    by_contra hnot
    obtain ⟨w,hw,hlen⟩ := failed_deadline_certificate_word hn p B c _
      (BinaryLift.selected_lift p c S hS) hnot
    have hh := length_le_word (n := n) w
    rw [hw] at hh
    omega
  · exact length_lower_of_deadline_certificates hn p B

theorem length_upper_iff_deadline_failure (hn : 2 ≤ n) (p : State n) (B : ℕ) :
    length p ≤ B ↔ ∃ (c : Fin n) (S : Finset (Fin n)),BinaryLift.ValidSelection p c S ∧
      ¬LowerDeadlineCertificate (B+1) c (BinaryLift.displacement p c S) := by
  classical
  constructor
  · intro hB
    by_contra hnone
    have hall : ∀ (c : Fin n) (S : Finset (Fin n)),BinaryLift.ValidSelection p c S →
        LowerDeadlineCertificate (B+1) c (BinaryLift.displacement p c S) := by
      intro c S hS
      by_contra hnot
      exact hnone ⟨c,S,hS,hnot⟩
    have hh := length_lower_of_deadline_certificates hn p (B+1) hall
    omega
  · rintro ⟨c,S,hS,hnot⟩
    obtain ⟨w,hw,hlen⟩ := failed_deadline_certificate_word hn p (B+1) c _
      (BinaryLift.selected_lift p c S hS) hnot
    have hh := length_le_word (n := n) w
    rw [hw] at hh
    omega

#print axioms length_lower_of_deadline_certificates
#print axioms length_lower_iff_deadline_certificates
#print axioms length_upper_iff_deadline_failure
end LX
