import LRX.SuffixWindowLoad
import LRX.CanonicalPositivePaths

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b : ℕ} [NeZero n] [NeZero b]

theorem suffix_load_path_ordered (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (a c : Fin b) (hac : a.val ≤ c.val) :
    CycleFootprint.LoadPath (displacement p) (embed W a) (embed W c) ↔
      CycleFootprint.LoadPath (displacement f) a c := by
  have heac : (embed W a).val ≤ (embed W c).val := by dsimp [embed]; omega
  rw [canonical_load_path_iff p _ _ heac,canonical_load_path_iff f _ _ hac]
  constructor
  · intro h r ha hc
    have hr := h (embed W r) (by dsimp [embed]; omega) (by dsimp [embed]; omega)
    rw [suffix_port_load W hend p f hmatch] at hr
    exact hr
  · intro h r ha hc
    have hr : Contains W r := by
      dsimp [embed] at ha hc
      have hc' := c.isLt
      unfold Contains
      omega
    obtain ⟨j,rfl⟩ := (contains_iff W r).mp hr
    rw [suffix_port_load W hend p f hmatch]
    apply h j <;> dsimp [embed] at ha hc <;> omega

theorem suffix_load_path_iff (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (a c : Fin b) :
    CycleFootprint.LoadPath (displacement p) (embed W a) (embed W c) ↔
      CycleFootprint.LoadPath (displacement f) a c := by
  by_cases hac : a.val ≤ c.val
  · exact suffix_load_path_ordered W hend p f hmatch a c hac
  · have h := suffix_load_path_ordered W hend p f hmatch c a (by omega)
    constructor
    · intro hp
      exact CycleFootprint.load_path_symm _ (h.mp (CycleFootprint.load_path_symm _ hp))
    · intro hp
      exact CycleFootprint.load_path_symm _ (h.mpr (CycleFootprint.load_path_symm _ hp))

/-- A component starting in the invariant suffix cannot leave it. -/
theorem suffix_load_path_stays (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i))
    (a : Fin b) (x : Fin n)
    (hp : CycleFootprint.LoadPath (displacement p) (embed W a) x) : Contains W x := by
  by_cases ho : W.offset = 0
  · unfold Contains
    have hx := x.isLt
    constructor <;> omega
  · let r : Fin n := ⟨W.offset-1,by have := W.fits; have := NeZero.pos b; omega⟩
    have hr : r.val+1 = W.offset := by dsimp [r]; omega
    have hz : portLoad (displacement p) r = 0 := by
      rw [port_load_eq_twice_half,hr]
      have hh := suffix_half_load W hend p f hmatch 0
      simp only [Nat.add_zero,half_load_zero] at hh
      rw [hh]
      simp
    have hs := zero_port_path_side p.symm r hz hp
    have hax : r.val < x.val := by
      have ha : ¬(embed W a).val ≤ r.val := by dsimp [embed]; omega
      omega
    unfold Contains
    have hx := x.isLt
    constructor <;> omega

/-- Component cardinalities are preserved by the physical suffix embedding. -/
theorem suffix_component_card (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b) (hmatch : ∀ i, p (embed W i) = embed W (f i)) (a : Fin b) :
    (CycleFootprint.component (displacement f) a).card =
      (CycleFootprint.component (displacement p) (embed W a)).card := by
  classical
  refine Finset.card_bij (fun i _ => embed W i) ?_ ?_ ?_
  · intro i hi
    exact (CycleFootprint.mem_component _ _ _).mpr
      ((suffix_load_path_iff W hend p f hmatch a i).mpr ((CycleFootprint.mem_component _ _ _).mp hi))
  · intro i _ j _ hij
    exact embed_injective W hij
  · intro x hx
    have hp := (CycleFootprint.mem_component _ _ _).mp hx
    obtain ⟨i,rfl⟩ := (contains_iff W x).mp (suffix_load_path_stays W hend p f hmatch a x hp)
    refine ⟨i,?_,rfl⟩
    exact (CycleFootprint.mem_component _ _ _).mpr ((suffix_load_path_iff W hend p f hmatch a i).mp hp)

#print axioms suffix_load_path_iff
#print axioms suffix_component_card
end LRX.FiniteWindow
