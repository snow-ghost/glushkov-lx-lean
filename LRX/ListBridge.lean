import LRX.WordMetric
import GraphLower

namespace LRX.ListBridge
open BlockExchange

def toVertex {n : ℕ} (p : State n) : GraphBridge.Vertex n :=
  ⟨List.ofFn p, by simpa only [List.ofFn_eq_map] using p.map_finRange_perm⟩

theorem toVertex_injective {n : ℕ} : Function.Injective (toVertex (n := n)) := by
  intro p q h
  exact Equiv.ext (congrFun (List.ofFn_injective (congrArg Subtype.val h)))

def fromVertex {n : ℕ} (u : GraphBridge.Vertex n) : State n :=
  let hlen : u.val.length = n := u.property.length_eq.trans (List.length_finRange)
  (finCongr hlen.symm).trans
    (List.Nodup.getEquivOfForallMemList u.val
      (u.property.nodup_iff.mpr (List.nodup_finRange n))
      (fun x => u.property.mem_iff.mpr (List.mem_finRange x)))

theorem toVertex_fromVertex {n : ℕ} (u : GraphBridge.Vertex n) :
    toVertex (fromVertex u) = u := by
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [toVertex, List.length_ofFn]
    exact u.property.length_eq.trans (List.length_finRange) |>.symm
  · intro i hi hj
    simp [toVertex, fromVertex, List.getElem_ofFn]

def vertexEquiv (n : ℕ) : State n ≃ GraphBridge.Vertex n where
  toFun := toVertex
  invFun := fromVertex
  left_inv p := toVertex_injective (toVertex_fromVertex (toVertex p))
  right_inv := toVertex_fromVertex


theorem left_ofFn {n : ℕ} [NeZero n] (p : State n) :
    left (List.ofFn p) = List.ofFn (p * L n) := by
  rw [LowerBoundNativeTrace.left_rotate]
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp [List.getElem_rotate, L, Fin.add_def]

theorem right_ofFn {n : ℕ} [NeZero n] (p : State n) :
    right (List.ofFn p) = List.ofFn (p * R n) := by
  have h := left_ofFn (p * R n)
  have he : p * R n * L n = p := by simp [R, mul_assoc]
  rw [he] at h
  have hh := congrArg right h
  simpa only [ReducedPrice.right_left] using hh.symm

theorem swap_ofFn {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) :
    swap (List.ofFn p) = List.ofFn (p * X n) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hnk : n = k + 2 := by omega
  clear hk
  subst n
  simp only [List.ofFn_succ, swap, Equiv.Perm.mul_apply, X]
  congr 1


def toOp : Letter → Op
  | .l => .L
  | .r => .R
  | .x => .X

def ofOp : Op → Letter
  | .L => .l
  | .R => .r
  | .X => .x

@[simp] theorem toOp_ofOp (o : Op) : toOp (ofOp o) = o := by cases o <;> rfl

theorem step_ofFn {n : ℕ} [NeZero n] (hn : 2 ≤ n) (p : State n) (c : Letter) :
    step (toOp c) (List.ofFn p) = List.ofFn (p * c.eval (n := n)) := by
  cases c with
  | l => exact left_ofFn p
  | r => exact right_ofFn p
  | x => exact swap_ofFn hn p

/-- Literal words and their final orientations agree in both models. -/
theorem run_ofFn {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (w : List Letter) (p : State n) :
    run (w.map toOp) (List.ofFn p) = List.ofFn (p * eval (n := n) w) := by
  induction w generalizing p with
  | nil => simp [run]
  | cons c w ih =>
    rw [List.map_cons, run, step_ofFn hn, ih, eval_cons, mul_assoc]

/-- The archived list graph and the permutation Cayley graph are isomorphic,
with all three unit-cost generators and the complete linear orientation. -/
def graphIso (n : ℕ) [NeZero n] (hn : 2 ≤ n) :
    LRX.graph n ≃g GraphBridge.graph n where
  toEquiv := vertexEquiv n
  map_rel_iff' := by
    intro a b
    change (toVertex a ≠ toVertex b ∧ ∃ o, step o (List.ofFn a) = List.ofFn b) ↔ _
    rw [adj_iff_letter]
    constructor
    · rintro ⟨hne, o, ho⟩
      refine ⟨fun h => hne (congrArg toVertex h), ofOp o, ?_⟩
      apply toVertex_injective
      apply Subtype.ext
      change List.ofFn (a * (ofOp o).eval (n := n)) = List.ofFn b
      rw [← step_ofFn hn, toOp_ofOp]
      exact ho
    · rintro ⟨hne, c, hc⟩
      refine ⟨fun h => hne (toVertex_injective h), toOp c, ?_⟩
      rw [step_ofFn hn, hc]

end LRX.ListBridge
