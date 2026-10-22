import LRX.BufferProgram

/-! Paid signed rotations and shortest cyclic offsets. No change of cursor is
introduced without an explicit L/R word and its length. -/
namespace LRX.RotationWords
open scoped Fin.IntCast Fin.NatCast Fin.CommRing
variable {n : ℕ} [NeZero n]

def spin : ℤ → List Letter
  | .ofNat k => List.replicate k .l
  | .negSucc k => List.replicate (k+1) .r

omit [NeZero n] in
theorem spin_length (z : ℤ) : (spin z).length=z.natAbs := by
  cases z <;> simp [spin]

theorem spin_eval (z : ℤ) : eval (n := n) (spin z)=(L n)^z := by
  cases z <;> simp [spin, eval, Letter.eval, R, zpow_negSucc, inv_pow]

omit [NeZero n] in
theorem spin_no_exchange (z : ℤ) : ∀ a ∈ spin z, a ≠ Letter.x := by
  cases z <;> simp [spin]

theorem no_exchange_positions (w : List Letter) (hw : ∀ a ∈ w, a ≠ Letter.x)
    (s : LiftedModel.Configuration n) :
    (LiftedModel.run w s).position=s.position ∧
      (LiftedModel.run w s).physical.tokens=s.physical.tokens := by
  induction w generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons a w ih =>
    have ha := hw a (by simp)
    have ht := ih (fun b hb => hw b (by simp [hb])) (LiftedModel.step a s)
    cases a with
    | l => simpa only [LiftedModel.run, LiftedModel.step, PhysicalModel.step] using ht
    | r => simpa only [LiftedModel.run, LiftedModel.step, PhysicalModel.step] using ht
    | x => exact False.elim (ha rfl)

theorem spin_cursor (z : ℤ) (s : LiftedModel.Configuration n) :
    (LiftedModel.run (spin z) s).cursor=s.cursor+z := by
  rw [LiftedModel.cursor_run]
  cases z <;> simp [spin, LiftedModel.increment]
  omega

theorem spin_positions (z : ℤ) (s : LiftedModel.Configuration n) :
    (LiftedModel.run (spin z) s).position=s.position :=
  (no_exchange_positions (spin z) (spin_no_exchange z) s).1

theorem spin_tokens (z : ℤ) (s : LiftedModel.Configuration n) :
    (LiftedModel.run (spin z) s).physical.tokens=s.physical.tokens :=
  (no_exchange_positions (spin z) (spin_no_exchange z) s).2

omit [NeZero n] in
theorem spin_rotations (z : ℤ) : BufferProgram.rotations (spin z)=z.natAbs := by
  cases z <;> simp [spin, BufferProgram.rotations]

omit [NeZero n] in
theorem spin_exchanges (z : ℤ) : BufferProgram.exchanges (spin z)=0 := by
  cases z <;> simp [spin, BufferProgram.exchanges]

def shortOffset (c : Fin n) : ℤ := if 2*c.val ≤ n then (c : ℤ) else (c : ℤ)-(n : ℤ)

def toPort (c : Fin n) : List Letter := spin (shortOffset c)

theorem rotation_period : L n ^ n=1 := by
  apply Equiv.ext
  intro i
  simp [AffineLift.rotation_power_apply]

theorem toPort_eval (c : Fin n) : eval (toPort c)=L n^c.val := by
  rw [toPort, spin_eval]
  unfold shortOffset
  split_ifs <;> simp [zpow_sub, rotation_period]

omit [NeZero n] in
theorem short_offset_cost (c : Fin n) : (shortOffset c).natAbs=min c.val (n-c.val) := by
  have hc := c.isLt
  unfold shortOffset
  split_ifs with h
  · change c.val=min c.val (n-c.val)
    omega
  · have hz : (c : ℤ)-(n : ℤ) ≤ 0 := by
      have hh : (c : ℤ) < n := by exact_mod_cast hc
      omega
    have habs := Int.natCast_natAbs ((c : ℤ)-(n : ℤ))
    rw [abs_of_nonpos hz] at habs
    omega

omit [NeZero n] in
theorem toPort_length (c : Fin n) : (toPort c).length=min c.val (n-c.val) := by
  rw [toPort, spin_length, short_offset_cost]

omit [NeZero n] in
theorem toPort_length_le (c : Fin n) : (toPort c).length ≤ n/2 := by
  rw [toPort_length]
  omega

theorem short_offset_cast (c : Fin n) : (shortOffset c : Fin n)=c := by
  unfold shortOffset
  split_ifs <;> simp [Int.cast_sub]

theorem spin_increment (z : ℤ) : ((spin z).map LiftedModel.increment).sum=z := by
  cases z <;> simp [spin, LiftedModel.increment]
  omega

#print axioms spin_positions
#print axioms toPort_eval
#print axioms toPort_length_le
end LRX.RotationWords
