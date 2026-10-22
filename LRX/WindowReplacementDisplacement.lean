import LRX.WindowReversalLoad
import LRX.ReflectionComponentCapacity

namespace LRX.FiniteWindow
open FiniteCuts
variable {n b : ℕ}

theorem replace_displacement_embed (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (i : Fin b) :
    displacement (replace W p f g) (embed W i)=displacement g i := by
  unfold displacement
  rw [replace_embed W p f g hmatch]
  simp [embed]

theorem replace_displacement_outside (W : Window n b) (p : State n) (f g : State b)
    (i : Fin n) (hi : ¬Contains W i) :
    displacement (replace W p f g) i=displacement p i := by
  unfold displacement
  rw [replace_outside W p f g i hi]

theorem finite_displacement_le_size (g : State b) (i : Fin b) :
    |displacement g i| ≤ (b : ℤ)-1 := by
  have hi := i.isLt
  have hg := (g i).isLt
  unfold displacement
  rw [abs_le]
  constructor <;> omega

/-- Filling a narrow invariant window preserves strict shortness. -/
theorem replace_strict_short (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i))
    (hshort : ∀ i, 2*|displacement p i| < (n : ℤ))
    (hwidth : b ≤ (n+1)/2) : ∀ i, 2*|displacement (replace W p f g) i| < (n : ℤ) := by
  intro i
  by_cases hi : Contains W i
  · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hi
    rw [replace_displacement_embed W p f g hmatch]
    have hb := finite_displacement_le_size g j
    omega
  · rw [replace_displacement_outside W p f g i hi]
    exact hshort i

/-- Coordinates at or above level h must be inherited if every new arrow is shorter than h. -/
theorem replace_large_coordinate_inherited (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (h : ℤ)
    (hsmall : ∀ i, |displacement g i| < h) (i : Fin n)
    (hi : h ≤ |displacement (replace W p f g) i|) :
    displacement (replace W p f g) i=displacement p i := by
  by_cases hW : Contains W i
  · obtain ⟨j,rfl⟩ := (contains_iff W i).mp hW
    rw [replace_displacement_embed W p f g hmatch] at hi
    have hh := hsmall j
    omega
  · exact replace_displacement_outside W p f g i hW

/-- A window of size at most h introduces no new coordinates at the extreme levels ±h. -/
theorem replace_extremes_inherited (W : Window n b) (p : State n) (f g : State b)
    (hmatch : ∀ i, p (embed W i)=embed W (f i)) (h : ℤ) (hwidth : (b : ℤ) ≤ h) :
    (∀ i, displacement (replace W p f g) i= -h → displacement p i= -h) ∧
      (∀ i, displacement (replace W p f g) i=h → displacement p i=h) := by
  have hsmall (i : Fin b) : |displacement g i| < h := by
    have hh := finite_displacement_le_size g i
    omega
  constructor
  · intro i hi
    have hh : h ≤ |displacement (replace W p f g) i| := by rw [hi,abs_neg]; exact le_abs_self h
    exact (replace_large_coordinate_inherited W p f g hmatch h hsmall i hh).symm.trans hi
  · intro i hi
    have hh : h ≤ |displacement (replace W p f g) i| := by rw [hi]; exact le_abs_self h
    exact (replace_large_coordinate_inherited W p f g hmatch h hsmall i hh).symm.trans hi

#print axioms replace_strict_short
#print axioms replace_extremes_inherited
end LRX.FiniteWindow
