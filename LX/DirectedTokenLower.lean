import LX.WordMetric
import LRX.LiftedModel
import LRX.AffineReducedPrice

namespace LX.DirectedTokenLower
open scoped BigOperators Fin.IntCast Fin.NatCast Fin.CommRing
open LRX.LiftedModel
variable {n : ℕ} [NeZero n]

/-- A token cannot make repeated net backward progress without paying
forward cursor turns. This invariant allows arbitrary detours and swaps. -/
def TokenBudget (s : Configuration n) : Prop :=
  ∀ i : Fin n,(n : ℤ)*(i.val-1 : ℕ) ≤ s.cursor+((n : ℤ)-1)*s.position i

theorem token_budget_step (hn : 2 ≤ n) (a : Letter) (s : Configuration n)
    (hs : Aligned s) (hb : TokenBudget s) : TokenBudget (step a.toLRX s) := by
  intro i
  have hi := hb i
  have hn' : (2 : ℤ) ≤ n := by exact_mod_cast hn
  cases a with
  | l =>
    simp only [Letter.toLRX,step,increment]
    linarith
  | x =>
    by_cases hleft : i=s.physical.tokens s.physical.cursor
    · have hright : i ≠ s.physical.tokens (s.physical.cursor+1) := by
        intro he
        exact neighboring_positions_distinct hn s.physical.cursor
          (s.physical.tokens.injective (hleft.symm.trans he))
      simp only [Letter.toLRX,step,increment,ite_eq_left hleft,ite_eq_right hright,sub_zero,add_zero]
      nlinarith only [hi,hn']
    · by_cases hright : i=s.physical.tokens (s.physical.cursor+1)
      · have hz : (s.position i : Fin n)=(s.cursor : Fin n)+1 := by
          rw [hs.2 i,hright,Equiv.symm_apply_apply,hs.1]
        have hmod : ((s.cursor+((n : ℤ)-1)*s.position i+1 : ℤ) : Fin n)=0 := by
          simp only [Int.cast_add,Int.cast_mul,Int.cast_sub,Int.cast_natCast,
            Fin.natCast_self,Int.cast_one,hz]
          ring
        have hdiv : (n : ℤ) ∣ s.cursor+((n : ℤ)-1)*s.position i+1 :=
          Int.modEq_zero_iff_dvd.mp ((cast_eq_iff_modEq _ 0).mp (by simpa using hmod))
        obtain ⟨k,hk⟩ := hdiv
        have hklo : ((i.val-1 : ℕ) : ℤ)+1 ≤ k := by
          by_contra hnot
          have hle : k ≤ ((i.val-1 : ℕ) : ℤ) := by omega
          have hmul := mul_le_mul_of_nonneg_left hle (show (0 : ℤ) ≤ n by omega)
          nlinarith only [hi,hk,hmul]
        have hmul := mul_le_mul_of_nonneg_left hklo (show (0 : ℤ) ≤ n by omega)
        simp only [Letter.toLRX,step,increment,ite_eq_right hleft,ite_eq_left hright,add_zero]
        nlinarith only [hk,hmul]
      · simpa only [Letter.toLRX,step,increment,ite_eq_right hleft,ite_eq_right hright,add_zero,sub_zero] using hi

theorem token_budget_initial : TokenBudget (initial (n := n)) := by
  intro i
  have hi : (i : ℤ) < n := by exact_mod_cast i.isLt
  simp only [initial,zero_add]
  by_cases hz : i.val=0
  · simp [hz]
  · rw [Nat.cast_sub (by omega : 1 ≤ i.val)]
    push_cast
    nlinarith only [hi]

theorem token_budget_run (hn : 2 ≤ n) (w : List Letter) (s : Configuration n)
    (hs : Aligned s) (hb : TokenBudget s) : TokenBudget (run (w.map Letter.toLRX) s) := by
  induction w generalizing s with
  | nil => exact hb
  | cons a w ih =>
    exact ih (step a.toLRX s) (step_aligned hn a.toLRX hs) (token_budget_step hn a s hs hb)

/-- An unconditional rotation lower bound for every token of every
literal LX word, expressed in its exact integer endpoint. -/
theorem word_cursor_lower (hn : 2 ≤ n) (w : List Letter) (i : Fin n) :
    (n : ℤ)*(i.val-1 : ℕ)-((n : ℤ)-1)*(run (w.map Letter.toLRX) (initial (n := n))).position i ≤
      (run (w.map Letter.toLRX) (initial (n := n))).cursor := by
  have hb := token_budget_run hn w initial initial_aligned token_budget_initial i
  omega

theorem cursor_eq_left_count (w : List Letter) :
    (run (w.map Letter.toLRX) (initial (n := n))).cursor=(w.count .l : ℤ) := by
  rw [cursor_run]
  simp only [initial,zero_add,List.map_map]
  induction w with
  | nil => rfl
  | cons a w ih => cases a <;> simp [Letter.toLRX,increment,ih,add_comm]

theorem rotations_eq_left_count (w : List Letter) :
    LRX.BufferProgram.rotations (w.map Letter.toLRX)=w.count .l := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | l => simpa [LRX.BufferProgram.rotations,Letter.toLRX] using congrArg Nat.succ ih
    | x => simpa [LRX.BufferProgram.rotations,Letter.toLRX] using ih

/-- Swap cancellation preserves the endpoint and all paid rotations;
therefore its exact inversion price is a lower bound for every LX word. -/
theorem word_inversion_cursor_lower (hn : 2 ≤ n) (w : List Letter) :
    (inversionCount (run (w.map Letter.toLRX) (initial (n := n))).position : ℤ)+
      (run (w.map Letter.toLRX) (initial (n := n))).cursor ≤ (w.length : ℤ) := by
  obtain ⟨v,_,_,_,_,hlen,hsub⟩ := affine_reduction_exact hn (w.map Letter.toLRX)
  have hb := hsub.length_le
  rw [hlen,rotations_eq_left_count,List.length_map] at hb
  rw [cursor_eq_left_count]
  exact_mod_cast hb

/-- The actual directed word supplies both lower costs simultaneously;
the rotation and exchange minima are never taken from different words. -/
theorem word_token_total_lower (hn : 2 ≤ n) (w : List Letter) (i : Fin n) :
    (inversionCount (run (w.map Letter.toLRX) (initial (n := n))).position : ℤ)+
      (n : ℤ)*(i.val-1 : ℕ)-
        ((n : ℤ)-1)*(run (w.map Letter.toLRX) (initial (n := n))).position i ≤
      (w.length : ℤ) := by
  have hc := word_cursor_lower hn w i
  have ht := word_inversion_cursor_lower hn w
  omega

#print axioms token_budget_step
#print axioms word_cursor_lower
#print axioms word_inversion_cursor_lower
#print axioms word_token_total_lower
end LX.DirectedTokenLower
