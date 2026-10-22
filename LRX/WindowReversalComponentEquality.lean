import LRX.WindowReversalComponents
import LRX.InvariantCutRecenter

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n]

/-- A replacement entirely on one side of a zero cut preserves that cut. -/
theorem replace_zero_port_outside_window (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i)) (r : Fin n)
    (hz : portLoad (displacement p) r = 0)
    (hside : r.val+1 ≤ W.offset ∨ W.offset+b ≤ r.val+1) :
    portLoad (displacement (replace W p f g)) r = 0 := by
  have hh : halfLoad p (r.val+1) = 0 := by
    rw [port_load_eq_twice_half] at hz
    omega
  have hc := (half_load_zero_iff_invariant_cut p (r.val+1)).mp hh
  have hnew : ∀ i : Fin n, (replace W p f g i).val < r.val+1 ↔ i.val < r.val+1 := by
    intro i
    by_cases hi : Contains W i
    · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
      rw [replace_embed W p f g hmatch]
      have hj := j.isLt
      have hg := (g j).isLt
      change W.offset+(g j).val < r.val+1 ↔ W.offset+j.val < r.val+1
      rcases hside with hside | hside <;> omega
    · rw [replace_outside W p f g i hi]
      exact hc i
  rw [port_load_eq_twice_half,(half_load_zero_iff_invariant_cut _ _).mpr hnew]
  simp

/-- Reversing an invariant window with positive internal ports cannot merge
original load components: exactly the same ports remain positive. -/
theorem replace_reversal_positive_port_iff (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (hloaded : ∀ r : Fin n, W.offset < r.val+1 → r.val+1 < W.offset+b →
      0 < portLoad (displacement p) r) (r : Fin n) :
    0 < portLoad (displacement (replace W p f Fin.revPerm)) r ↔
      0 < portLoad (displacement p) r := by
  constructor
  · intro hr
    by_contra h
    have hn := port_load_nonneg (displacement p) r
    have hz : portLoad (displacement p) r = 0 := by omega
    have hside : r.val+1 ≤ W.offset ∨ W.offset+b ≤ r.val+1 := by
      by_contra hs
      have hh := hloaded r (by omega) (by omega)
      omega
    have hh := replace_zero_port_outside_window W p f Fin.revPerm hmatch r hz hside
    omega
  · intro hr
    exact hr.trans_le (replace_reversal_port_load_mono W p f hmatch r)

/-- The load graph is unchanged as an unweighted graph. -/
theorem replace_reversal_load_path_iff (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (hloaded : ∀ r : Fin n, W.offset < r.val+1 → r.val+1 < W.offset+b →
      0 < portLoad (displacement p) r) (a c : Fin n) :
    CycleFootprint.LoadPath (displacement (replace W p f Fin.revPerm)) a c ↔
      CycleFootprint.LoadPath (displacement p) a c := by
  constructor
  · intro hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | @tail y z hp he ih =>
      apply ih.tail
      rcases he with ⟨he,hh⟩ | ⟨he,hh⟩
      · exact Or.inl ⟨he,(replace_reversal_positive_port_iff W p f hmatch hloaded y).mp hh⟩
      · exact Or.inr ⟨he,(replace_reversal_positive_port_iff W p f hmatch hloaded z).mp hh⟩
  · exact replace_reversal_load_path W p f hmatch

theorem replace_reversal_component_eq (W : Window n b) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (hloaded : ∀ r : Fin n, W.offset < r.val+1 → r.val+1 < W.offset+b →
      0 < portLoad (displacement p) r) (a : Fin n) :
    CycleFootprint.component (displacement (replace W p f Fin.revPerm)) a =
      CycleFootprint.component (displacement p) a := by
  ext c
  simp only [CycleFootprint.mem_component]
  exact replace_reversal_load_path_iff W p f hmatch hloaded a c

#print axioms replace_reversal_positive_port_iff
#print axioms replace_reversal_component_eq
end LRX.FiniteWindow
