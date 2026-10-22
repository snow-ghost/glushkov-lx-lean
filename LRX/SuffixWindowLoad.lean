import LRX.PositiveWindowWidth

namespace LRX.FiniteWindow
open FiniteCuts RotationWords
variable {n b : ℕ}

/-- A suffix filling has exactly its own forward crossings: the outside
permutation lies entirely before the invariant cut. -/
theorem suffix_forward (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i)) (e : ℕ) :
    forward p (W.offset+e) = (forward f e).image (embed W) := by
  ext j
  letI : NeZero n := ⟨by have := j.isLt; omega⟩
  constructor
  · intro hj
    obtain ⟨hl,hr⟩ := (mem_forward _ _ _).mp hj
    have hm : Contains W j := by
      by_contra h
      have hout := matching_outside W p f hmatch j h
      unfold Contains at hout
      have hp := (p j).isLt
      omega
    obtain ⟨i,rfl⟩ := (contains_iff W j).mp hm
    refine Finset.mem_image.mpr ⟨i,?_,rfl⟩
    rw [mem_forward]
    rw [hmatch] at hr
    dsimp [embed] at hl hr
    constructor <;> omega
  · intro hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
    obtain ⟨hl,hr⟩ := (mem_forward _ _ _).mp hi
    rw [mem_forward,hmatch]
    dsimp [embed]
    constructor <;> omega

theorem suffix_half_load (W : Window n b) (hend : W.offset+b = n)
    (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i)) (e : ℕ) :
    halfLoad p (W.offset+e) = halfLoad f e := by
  unfold halfLoad
  rw [suffix_forward W hend p f hmatch,Finset.card_image_of_injective _ (embed_injective W)]

/-- Exact load transfer includes the final zero port of the suffix. -/
theorem suffix_port_load [NeZero n] [NeZero b]
    (W : Window n b) (hend : W.offset+b = n) (p : State n) (f : State b)
    (hmatch : ∀ i, p (embed W i) = embed W (f i)) (r : Fin b) :
    portLoad (displacement p) (embed W r) = portLoad (displacement f) r := by
  rw [port_load_eq_twice_half,port_load_eq_twice_half]
  have he : (embed W r).val+1 = W.offset+(r.val+1) := by simp [embed]; omega
  rw [he,suffix_half_load W hend p f hmatch]

#print axioms suffix_half_load
#print axioms suffix_port_load
end LRX.FiniteWindow
