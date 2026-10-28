import LX.FiniteCutLoad
import Mathlib

/-! Extend a finite permutation to a contiguous window of a larger ambient
permutation, fixing every external label. No ambient size is changed. -/
namespace LX.Core.FiniteWindow
variable {n b : ℕ}

structure Window (n b : ℕ) where
  offset : ℕ
  fits : offset+b ≤ n

def embed (W : Window n b) (i : Fin b) : Fin n := ⟨W.offset+i.val, by have := W.fits; omega⟩

def Contains (W : Window n b) (j : Fin n) : Prop :=
  W.offset ≤ j.val ∧ j.val < W.offset+b

instance (W : Window n b) : DecidablePred (Contains W) := fun j => inferInstanceAs (Decidable (W.offset ≤ j.val ∧ j.val < W.offset+b))

def windowEquiv (W : Window n b) : Fin b ≃ {j : Fin n // Contains W j} where
  toFun i := ⟨embed W i, by unfold Contains embed; simp⟩
  invFun j := ⟨j.val.val-W.offset, by have := j.property; unfold Contains at this; omega⟩
  left_inv i := by apply Fin.ext; simp [embed]
  right_inv j := by
    apply Subtype.ext
    apply Fin.ext
    have := j.property
    unfold Contains at this
    dsimp [embed]
    omega

def permutation (W : Window n b) (p : State b) : State n := p.extendDomain (windowEquiv W)

theorem embed_injective (W : Window n b) : Function.Injective (embed W) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  dsimp [embed] at this
  omega

theorem contains_embed (W : Window n b) (i : Fin b) : Contains W (embed W i) :=
  (windowEquiv W i).property

theorem contains_iff (W : Window n b) (j : Fin n) : Contains W j ↔ ∃ i, embed W i=j := by
  constructor
  · intro h
    refine ⟨(windowEquiv W).symm ⟨j,h⟩, ?_⟩
    exact congrArg Subtype.val ((windowEquiv W).apply_symm_apply ⟨j,h⟩)
  · rintro ⟨i,rfl⟩
    exact contains_embed W i

@[simp] theorem permutation_embed (W : Window n b) (p : State b) (i : Fin b) :
    permutation W p (embed W i)=embed W (p i) := p.extendDomain_apply_image (windowEquiv W) i

theorem permutation_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    permutation W p j=j := p.extendDomain_apply_not_subtype (windowEquiv W) hj

@[simp] theorem permutation_symm (W : Window n b) (p : State b) :
    (permutation W p).symm=permutation W p.symm := rfl


theorem displacement_embed (W : Window n b) (p : State b) (i : Fin b) :
    FiniteCuts.displacement (permutation W p) (embed W i)=FiniteCuts.displacement p i := by
  unfold FiniteCuts.displacement
  rw [permutation_embed]
  simp [embed]

theorem displacement_outside (W : Window n b) (p : State b) (j : Fin n) (hj : ¬Contains W j) :
    FiniteCuts.displacement (permutation W p) j=0 := by
  simp [FiniteCuts.displacement,permutation_outside W p j hj]

#print axioms displacement_embed
end LX.Core.FiniteWindow
