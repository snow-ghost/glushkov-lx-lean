import LRX.BufferMachine

/-! A certified compiler of legal periodic-buffer programs into literal LRX
words. Integer positions are preserved; rotations and exchanges are counted
separately. Legality of a cycle-scheduling algorithm remains a later obligation. -/
namespace LRX.BufferProgram
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing

structure Logical (n : ℕ) where
  buffer : Fin n
  coord : Fin n → ℤ
  head : ℤ

inductive Command (n : ℕ) where
  | forward | backward | exchange (token : Fin n)
  deriving DecidableEq

variable {n : ℕ} [NeZero n]

def logicalStep (c : Command n) (t : Logical n) : Logical n := match c with
  | .forward => ⟨t.buffer, Function.update t.coord t.buffer (t.coord t.buffer+1), t.head+1⟩
  | .backward => ⟨t.buffer, Function.update t.coord t.buffer (t.coord t.buffer-1), t.head-1⟩
  | .exchange j => ⟨j, t.coord, t.head⟩

def Admissible (c : Command n) (t : Logical n) : Prop := match c with
  | .forward | .backward => True
  | .exchange j => j ≠ t.buffer ∧ (t.coord j-t.head)%BufferMachine.slots n=0

def word : Command n → List Letter
  | .forward => [.x,.l]
  | .backward => [.r,.x]
  | .exchange _ => [.x]

def compile : List (Command n) → List Letter
  | [] => []
  | c :: cs => word c ++ compile cs

def logicalRun : List (Command n) → Logical n → Logical n
  | [], t => t
  | c :: cs, t => logicalRun cs (logicalStep c t)

def Valid : List (Command n) → Logical n → Prop
  | [], _ => True
  | c :: cs, t => Admissible c t ∧ Valid cs (logicalStep c t)

omit [NeZero n] in
theorem logicalRun_append (u v : List (Command n)) (t : Logical n) :
    logicalRun (u++v) t = logicalRun v (logicalRun u t) := by
  induction u generalizing t with
  | nil => rfl
  | cons c u ih => exact ih (logicalStep c t)

omit [NeZero n] in
theorem valid_append (u v : List (Command n)) (t : Logical n) :
    Valid (u++v) t ↔ Valid u t ∧ Valid v (logicalRun u t) := by
  induction u generalizing t with
  | nil => simp [Valid, logicalRun]
  | cons c u ih => simp [Valid, logicalRun, ih, and_assoc]

omit [NeZero n] in
theorem compile_append (u v : List (Command n)) : compile (u++v) = compile u ++ compile v := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [compile, ih, List.append_assoc]

def Matches (s : LiftedModel.Configuration n) (t : Logical n) : Prop :=
  s.cursor=t.head ∧ BufferMachine.Represents s t.buffer t.coord

theorem step_correct (hn : 2 ≤ n) (c : Command n)
    {s : LiftedModel.Configuration n} {t : Logical n}
    (hm : Matches s t) (hv : Admissible c t) :
    Matches (LiftedModel.run (word c) s) (logicalStep c t) := by
  cases c with
  | forward =>
    refine ⟨?_, BufferMachine.forward_represents hn hm.2⟩
    change (BufferMachine.forward s).cursor=t.head+1
    rw [BufferMachine.forward_cursor, hm.1]
  | backward =>
    refine ⟨?_, BufferMachine.backward_represents hn hm.2⟩
    change (BufferMachine.backward s).cursor=t.head-1
    rw [BufferMachine.backward_cursor, hm.1]
  | exchange j =>
    refine ⟨?_, BufferMachine.exchange_represents_at hn hm.2 hv.1 ?_⟩
    · change (BufferMachine.exchange s).cursor=t.head
      rw [BufferMachine.exchange_cursor, hm.1]
    · rw [hm.1]; exact hv.2

/-- Every admitted command sequence is a genuine word execution preserving the
full logical/physical correspondence, including all integer winding data. -/
theorem compile_correct (hn : 2 ≤ n) (cs : List (Command n))
    {s : LiftedModel.Configuration n} {t : Logical n}
    (hm : Matches s t) (hv : Valid cs t) :
    Matches (LiftedModel.run (compile cs) s) (logicalRun cs t) := by
  induction cs generalizing s t with
  | nil => exact hm
  | cons c cs ih =>
    rw [compile, LiftedModel.run_append]
    exact ih (step_correct hn c hm hv.1) hv.2

def rotationCost : Command n → ℕ
  | .forward | .backward => 1
  | .exchange _ => 0

def rotations (w : List Letter) : ℕ := (w.filter (fun a => a ≠ .x)).length

def exchanges (w : List Letter) : ℕ := (w.filter (fun a => a = .x)).length

omit [NeZero n] in
@[simp] theorem rotations_append (u v : List Letter) : rotations (u++v)=rotations u+rotations v := by
  simp [rotations]

omit [NeZero n] in
@[simp] theorem exchanges_append (u v : List Letter) : exchanges (u++v)=exchanges u+exchanges v := by
  simp [exchanges]

omit [NeZero n] in
@[simp] theorem rotations_word (c : Command n) : rotations (word c)=rotationCost c := by
  cases c <;> simp [word, rotations, rotationCost]

omit [NeZero n] in
@[simp] theorem exchanges_word (c : Command n) : exchanges (word c)=1 := by
  cases c <;> simp [word, exchanges]

omit [NeZero n] in
@[simp] theorem length_word (c : Command n) : (word c).length=1+rotationCost c := by
  cases c <;> rfl

omit [NeZero n] in
theorem rotations_compile (cs : List (Command n)) :
    rotations (compile cs) = (cs.map rotationCost).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [compile, ih]

omit [NeZero n] in
theorem exchanges_compile (cs : List (Command n)) :
    exchanges (compile cs) = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [compile, ih, add_comm]

omit [NeZero n] in
theorem length_compile (cs : List (Command n)) :
    (compile cs).length = cs.length + (cs.map rotationCost).sum := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [compile, ih]; omega

#print axioms compile_correct
#print axioms rotations_compile
#print axioms length_compile
end LRX.BufferProgram
