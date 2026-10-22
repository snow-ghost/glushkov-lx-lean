import LRX.LiftedModel
import LRX.PeriodicBuffer

/-! Exact periodic buffer macros connected to the literal lifted LRX executor.
The buffer identity, integer logical positions and integer head are retained. -/
namespace LRX.BufferMachine
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LiftedModel

abbrev slots (n : ℕ) : ℤ := (n : ℤ)-1

variable {n : ℕ} [NeZero n]

structure Represents (s : Configuration n) (b : Fin n) (y : Fin n → ℤ) : Prop where
  aligned : Aligned s
  head : (y b-s.cursor) % slots n = 0
  positions : ∀ i, s.position i = if i=b then PeriodicBuffer.buffer (slots n) s.cursor (y i)
    else PeriodicBuffer.passive (slots n) s.cursor (y i)

omit [NeZero n] in
theorem slots_pos (hn : 2 ≤ n) : 0 < slots n := by
  dsimp [slots]; omega

theorem buffer_position {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) : s.position b = PeriodicBuffer.buffer (slots n) s.cursor (y b) := by
  simpa using h.positions b

theorem passive_position {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) {i : Fin n} (hi : i ≠ b) :
    s.position i = PeriodicBuffer.passive (slots n) s.cursor (y i) := by
  simpa [hi] using h.positions i

theorem buffer_at {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) : s.physical.tokens s.physical.cursor = b := by
  rw [← h.aligned.1]
  apply (token_at_iff h.aligned b s.cursor).mpr
  rw [buffer_position h]
  simpa only [slots, sub_add_cancel] using PeriodicBuffer.buffer_at_cursor (slots n) s.cursor (y b)

theorem next_label_iff (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) {i : Fin n} (hi : i ≠ b) :
    s.physical.tokens (s.physical.cursor+1) = i ↔ (y i-s.cursor)%slots n=0 := by
  have ht := token_at_iff h.aligned i (s.cursor+1)
  simp only [Int.cast_add, Int.cast_one, h.aligned.1] at ht
  rw [ht, passive_position h hi]
  simpa only [slots, sub_add_cancel] using PeriodicBuffer.passive_next_iff (slots_pos hn) s.cursor (y i)

theorem prev_label_iff (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) {i : Fin n} (hi : i ≠ b) :
    s.physical.tokens (s.physical.cursor-1) = i ↔ (y i-(s.cursor-1))%slots n=0 := by
  have ht := token_at_iff h.aligned i (s.cursor-1)
  simp only [Int.cast_sub, Int.cast_one, h.aligned.1] at ht
  rw [ht, passive_position h hi]
  simpa only [slots, sub_add_cancel] using PeriodicBuffer.passive_prev_iff (slots_pos hn) s.cursor (y i)

def forward (s : Configuration n) : Configuration n := run [.x,.l] s

def backward (s : Configuration n) : Configuration n := run [.r,.x] s

def exchange (s : Configuration n) : Configuration n := step .x s

@[simp] theorem forward_cursor (s : Configuration n) : (forward s).cursor = s.cursor+1 := by
  simp [forward, run, step, increment]

@[simp] theorem backward_cursor (s : Configuration n) : (backward s).cursor = s.cursor-1 := by
  simp [backward, run, step, increment, sub_eq_add_neg]

@[simp] theorem exchange_cursor (s : Configuration n) : (exchange s).cursor = s.cursor := by
  simp [exchange, step, increment]

theorem forward_position (s : Configuration n) (i : Fin n) :
    (forward s).position i = s.position i + (if i=s.physical.tokens s.physical.cursor then 1 else 0)
      - (if i=s.physical.tokens (s.physical.cursor+1) then 1 else 0) := by rfl

theorem backward_position (s : Configuration n) (i : Fin n) :
    (backward s).position i = s.position i + (if i=s.physical.tokens (s.physical.cursor-1) then 1 else 0)
      - (if i=s.physical.tokens s.physical.cursor then 1 else 0) := by
  simp [backward, run, step, PhysicalModel.step]
  rfl

theorem exchange_position (s : Configuration n) (i : Fin n) :
    (exchange s).position i = s.position i + (if i=s.physical.tokens s.physical.cursor then 1 else 0)
      - (if i=s.physical.tokens (s.physical.cursor+1) then 1 else 0) := by rfl


theorem next_ne_buffer (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) : s.physical.tokens (s.physical.cursor+1) ≠ b := by
  rw [← buffer_at h]
  intro he
  exact neighboring_positions_distinct hn s.physical.cursor (s.physical.tokens.injective he).symm

theorem prev_ne_buffer (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) : s.physical.tokens (s.physical.cursor-1) ≠ b := by
  rw [← buffer_at h]
  intro he
  have he' := s.physical.tokens.injective he
  have hh := neighboring_positions_distinct hn (s.physical.cursor-1)
  apply hh
  simpa only [sub_add_cancel] using he'

theorem forward_represents (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) :
    Represents (forward s) b (Function.update y b (y b+1)) := by
  refine ⟨run_aligned hn [.x,.l] h.aligned, ?_, ?_⟩
  · simp only [Function.update_self, forward_cursor]
    rw [show y b+1-(s.cursor+1)=y b-s.cursor by ring]
    exact h.head
  · intro i
    rw [forward_position, buffer_at h, forward_cursor]
    by_cases hi : i=b
    · subst i
      have hne := (next_ne_buffer hn h).symm
      simp [hne, buffer_position h, PeriodicBuffer.buffer_forward]
    · have hiff : (i=s.physical.tokens (s.physical.cursor+1)) ↔ (y i-s.cursor)%slots n=0 :=
        eq_comm.trans (next_label_iff hn h hi)
      simp only [Function.update_of_ne hi, ite_eq_right hi]
      rw [passive_position h hi, PeriodicBuffer.passive_forward (slots_pos hn)]
      simp only [add_zero, hiff]

theorem backward_represents (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) :
    Represents (backward s) b (Function.update y b (y b-1)) := by
  refine ⟨run_aligned hn [.r,.x] h.aligned, ?_, ?_⟩
  · simp only [Function.update_self, backward_cursor]
    rw [show y b-1-(s.cursor-1)=y b-s.cursor by ring]
    exact h.head
  · intro i
    rw [backward_position, buffer_at h, backward_cursor]
    by_cases hi : i=b
    · subst i
      have hne := (prev_ne_buffer hn h).symm
      simp [hne, buffer_position h, PeriodicBuffer.buffer_backward]
    · have hiff : (i=s.physical.tokens (s.physical.cursor-1)) ↔
          (y i-(s.cursor-1))%slots n=0 := eq_comm.trans (prev_label_iff hn h hi)
      simp only [Function.update_of_ne hi, ite_eq_right hi]
      rw [passive_position h hi, PeriodicBuffer.passive_backward (slots_pos hn)]
      simp only [sub_zero, hiff]

/-- Hand the buffer to the actual token at the logical head, retaining every y. -/
theorem exchange_represents (hn : 2 ≤ n) {s : Configuration n} {b : Fin n} {y : Fin n → ℤ}
    (h : Represents s b y) :
    Represents (exchange s) (s.physical.tokens (s.physical.cursor+1)) y := by
  let j := s.physical.tokens (s.physical.cursor+1)
  have hne : j ≠ b := next_ne_buffer hn h
  have hj : (y j-s.cursor)%slots n=0 := (next_label_iff hn h hne).mp rfl
  refine ⟨step_aligned hn .x h.aligned, ?_, ?_⟩
  · simpa only [exchange_cursor] using hj
  · intro i
    rw [exchange_position, buffer_at h, exchange_cursor]
    change s.position i + (if i=b then 1 else 0) - (if i=j then 1 else 0) =
      if i=j then PeriodicBuffer.buffer (slots n) s.cursor (y i)
      else PeriodicBuffer.passive (slots n) s.cursor (y i)
    by_cases hi : i=j
    · subst i
      simp only [ite_eq_right hne]
      rw [passive_position h hne, PeriodicBuffer.head_gap hj]
      simp
    · by_cases hb : i=b
      · subst i
        simp only [ite_eq_right hi]
        rw [buffer_position h, PeriodicBuffer.head_gap h.head]
        simp
      · simp only [ite_eq_right hi, ite_eq_right hb, add_zero, sub_zero]
        exact passive_position h hb

theorem exchange_represents_at (hn : 2 ≤ n) {s : Configuration n} {b j : Fin n}
    {y : Fin n → ℤ} (h : Represents s b y) (hne : j ≠ b)
    (hj : (y j-s.cursor)%slots n=0) : Represents (exchange s) j y := by
  have he := (next_label_iff hn h hne).mpr hj
  simpa only [he] using exchange_represents hn h

#print axioms forward_represents
#print axioms backward_represents
#print axioms exchange_represents_at
end LRX.BufferMachine
