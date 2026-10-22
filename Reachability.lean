import LRX.BlockExchange
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Induction

/-! Native reachability, without a bound on the length of its witness.
Adjacent exchanges are lifted under prefixes, not native rotations of shorter lists. -/
namespace LRX.GraphReachability
open LRX.BlockExchange
variable {α : Type*}

theorem rotate_prefix_left (p q : List α) :
    run (List.replicate p.length Op.L) (p ++ q) = q ++ p := by
  induction p generalizing q with
  | nil => simp [run]
  | cons a p ih =>
    simpa [List.replicate_succ, run, step, left, List.append_assoc] using ih (q ++ [a])

theorem rotate_suffix_right (p q : List α) :
    run (List.replicate p.length Op.R) (q ++ p) = p ++ q := by
  induction p using List.reverseRecOn generalizing q with
  | nil => simp [run]
  | append_singleton p a ih =>
    rw [List.length_append, List.length_singleton, ← List.append_assoc]
    simp only [List.replicate_succ, run, step, right_append]
    change run (List.replicate p.length Op.R) ((a :: q) ++ p) = _
    rw [ih]
    simp only [List.append_assoc, List.singleton_append]

def adjWord (k : Nat) : List Op :=
  List.replicate k Op.L ++ [Op.X] ++ List.replicate k Op.R

theorem adjWord_spec (p q : List α) (a b : α) :
    run (adjWord p.length) (p ++ a :: b :: q) = p ++ b :: a :: q := by
  unfold adjWord
  rw [run_append, run_append, rotate_prefix_left]
  simp only [run, step, List.cons_append, swap]
  exact rotate_suffix_right p (b :: a :: q)

theorem adjWord_length (k : Nat) : (adjWord k).length = 2*k+1 := by
  simp [adjWord]
  omega

inductive AdjacentTrace : List α → List α → Prop where
  | refl (s) : AdjacentTrace s s
  | exchange (p q) (a b) : AdjacentTrace (p ++ a :: b :: q) (p ++ b :: a :: q)
  | trans {s t u} : AdjacentTrace s t → AdjacentTrace t u → AdjacentTrace s u

theorem AdjacentTrace.cons (a : α) {s t : List α} (h : AdjacentTrace s t) :
    AdjacentTrace (a :: s) (a :: t) := by
  induction h with
  | refl s => exact .refl _
  | exchange p q b c => exact .exchange (a :: p) q b c
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem trace_of_perm {xs ys : List α} (h : xs.Perm ys) : AdjacentTrace xs ys := by
  induction h with
  | nil => exact .refl _
  | cons a h ih => exact ih.cons a
  | swap a b s => exact .exchange [] s b a
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

theorem AdjacentTrace.exists_word {xs ys : List α} (h : AdjacentTrace xs ys) :
    ∃ w, run w xs = ys := by
  induction h with
  | refl s => exact ⟨[], rfl⟩
  | exchange p q a b => exact ⟨adjWord p.length, adjWord_spec p q a b⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨u, hu⟩ := ih₁
    obtain ⟨v, hv⟩ := ih₂
    exact ⟨u ++ v, by rw [run_append, hu, hv]⟩

theorem exists_word_of_perm {xs ys : List α} (h : xs.Perm ys) :
    ∃ w, LRX.BlockExchange.run w xs = ys :=
  (trace_of_perm h).exists_word

#print axioms exists_word_of_perm
#print axioms adjWord_spec
end LRX.GraphReachability
