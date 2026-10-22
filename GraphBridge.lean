import LRX.Cycle11StructuralBridge
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace LRX.GraphBridge
open LRX.BlockExchange LRX.Cycle11StructuralBridge LRX.ReducedPrice

def Vertex (n : ℕ) := { xs : List (Fin n) // xs.Perm (List.finRange n) }

def invOp : Op → Op
  | .L => .R
  | .R => .L
  | .X => .X

theorem inverse_step {α : Type*} (op : Op) (xs : List α) :
    step (invOp op) (step op xs) = xs := by
  cases op with
  | L => exact right_left xs
  | R => exact left_right xs
  | X => cases xs with
    | nil => rfl
    | cons a xs => cases xs <;> rfl

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj u v := u ≠ v ∧ ∃ op, step op u.val = v.val
  symm := by
    constructor
    intro u v h
    obtain ⟨hne, op, hop⟩ := h
    refine ⟨Ne.symm hne, invOp op, ?_⟩
    rw [← hop]
    exact inverse_step op u.val
  loopless := by constructor; intro u h; exact h.1 rfl

def root (n : ℕ) : Vertex n := ⟨List.finRange n, List.Perm.refl _⟩

def stepV {n : ℕ} (op : Op) (u : Vertex n) : Vertex n :=
  ⟨step op u.val, (step_perm op u.val).trans u.property⟩

def runV {n : ℕ} (w : List Op) (u : Vertex n) : Vertex n :=
  ⟨run w u.val, (run_perm w u.val).trans u.property⟩

theorem walk_word {n : ℕ} {u v : Vertex n} (p : (graph n).Walk u v) :
    ∃ w, run w u.val = v.val ∧ w.length = p.length := by
  induction p with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons u v z h p ih =>
    obtain ⟨op, hop⟩ := h.2
    obtain ⟨w, hw, hl⟩ := ih
    refine ⟨op :: w, ?_, ?_⟩
    · simpa only [run, hop] using hw
    · simp only [List.length_cons, SimpleGraph.Walk.length_cons, hl]

theorem left_ne {α : Type*} (xs : List α) (hd : xs.Nodup) (hl : 2 ≤ xs.length) :
    left xs ≠ xs := by
  cases xs with
  | nil => simp at hl
  | cons a xs => cases xs with
    | nil => simp at hl
    | cons b t =>
      intro heq
      have hab : b = a := List.cons.inj heq |>.1
      have hne : a ≠ b := by intro hab; subst b; simp at hd
      exact hne hab.symm

theorem step_ne {n : ℕ} (hn : 2 ≤ n) (op : Op) (u : Vertex n) : stepV op u ≠ u := by
  have hd : u.val.Nodup := u.property.nodup_iff.mpr (List.nodup_finRange n)
  have hl : 2 ≤ u.val.length := by simpa only [u.property.length_eq, List.length_finRange] using hn
  intro heq
  have heq' : step op u.val = u.val := congrArg Subtype.val heq
  cases op with
  | L => exact left_ne u.val hd hl heq'
  | R =>
    have hh := congrArg left heq'
    have : left u.val = u.val := by simpa only [step, left_right] using hh.symm
    exact left_ne u.val hd hl this
  | X =>
    rcases u with ⟨xs, hp⟩
    cases xs with
    | nil => simp at hl
    | cons a xs => cases xs with
      | nil => simp at hl
      | cons b t =>
        have hab : b = a := List.cons.inj heq' |>.1
        have hne : a ≠ b := by intro hab; subst b; simp at hd
        exact hne hab.symm

#print axioms walk_word
#print axioms step_ne

theorem word_walk {n : ℕ} (hn : 2 ≤ n) (w : List Op) (u : Vertex n) :
    ∃ p : (graph n).Walk u (runV w u), p.length = w.length := by
  induction w generalizing u with
  | nil => exact ⟨.nil, rfl⟩
  | cons op w ih =>
    obtain ⟨p, hp⟩ := ih (stepV op u)
    have hadj : (graph n).Adj u (stepV op u) :=
      ⟨Ne.symm (step_ne hn op u), op, rfl⟩
    exact ⟨.cons hadj p, by change p.length + 1 = w.length + 1; omega⟩

#print axioms word_walk
end LRX.GraphBridge
