import LRX.WindowReversalInversionBudget

namespace LRX.FiniteWindow
open FiniteCuts RotationWords

/-- One actual invariant filling, with its own finite size. -/
structure FillingWindow (n : ℕ) where
  size : ℕ
  window : Window n size
  filling : State size

namespace FillingWindow
variable {n : ℕ}

def Matches (A : FillingWindow n) (p : State n) : Prop :=
  ∀ i, p (embed A.window i) = embed A.window (A.filling i)

def Apart (A B : FillingWindow n) : Prop :=
  ∀ i, Contains A.window i → ¬Contains B.window i

def reverseIn (A : FillingWindow n) (p : State n) : State n :=
  replace A.window p A.filling Fin.revPerm

def deficit (A : FillingWindow n) : ℤ :=
  (A.size.choose 2 : ℤ) - (inversionNumber A.filling : ℤ)

theorem matches_after_apart (A B : FillingWindow n) (p : State n)
    (hAB : A.Apart B) (hB : B.Matches p) : B.Matches (A.reverseIn p) := by
  intro i
  rw [reverseIn, replace_outside]
  · exact hB i
  · intro hi
    exact hAB _ hi (contains_embed B.window i)

end FillingWindow

/-- Successive literal replacements of the specified original fillings. -/
def reverseWindows {n : ℕ} : List (FillingWindow n) → State n → State n
  | [], p => p
  | A :: As, p => reverseWindows As (A.reverseIn p)

variable {n : ℕ} [NeZero n]

/-- Joint reversal preserves all load paths and extreme coordinates and has
exactly the sum of the original local inversion increments. -/
theorem reverse_windows_spec (As : List (FillingWindow n)) (p : State n)
    (hmatch : ∀ A ∈ As, A.Matches p)
    (hapart : As.Pairwise FillingWindow.Apart)
    (hwidth : ∀ A ∈ As, A.size ≤ (n-1)/2)
    (hshort : ∀ i, 2*|displacement p i| < (n : ℤ)) :
    (inversionNumber (reverseWindows As p) : ℤ) =
      (inversionNumber p : ℤ) + (As.map FillingWindow.deficit).sum ∧
    (∀ i, 2*|displacement (reverseWindows As p) i| < (n : ℤ)) ∧
    (∀ i, displacement (reverseWindows As p) i = -(((n-1)/2 : ℕ) : ℤ) →
      displacement p i = -(((n-1)/2 : ℕ) : ℤ)) ∧
    (∀ i, displacement (reverseWindows As p) i = (((n-1)/2 : ℕ) : ℤ) →
      displacement p i = (((n-1)/2 : ℕ) : ℤ)) ∧
    (∀ a b, CycleFootprint.LoadPath (displacement p) a b →
      CycleFootprint.LoadPath (displacement (reverseWindows As p)) a b) := by
  induction As generalizing p with
  | nil => simp only [reverseWindows,List.map_nil,List.sum_nil,add_zero]; exact ⟨True.intro,hshort,fun _ h => h,fun _ h => h,fun _ _ h => h⟩
  | cons A As ih =>
    have hm : A.Matches p := hmatch A (List.mem_cons_self ..)
    obtain ⟨hA,hAs⟩ := List.pairwise_cons.mp hapart
    have hmAs : ∀ B ∈ As, B.Matches (A.reverseIn p) := by
      intro B hB
      exact FillingWindow.matches_after_apart A B p (hA B hB)
        (hmatch B (List.mem_cons_of_mem _ hB))
    have hw : A.size ≤ (n-1)/2 := hwidth A (List.mem_cons_self ..)
    have hs : ∀ i, 2*|displacement (A.reverseIn p) i| < (n : ℤ) :=
      replace_strict_short A.window p A.filling Fin.revPerm hm hshort (by omega)
    obtain ⟨hprice,hshort',hneg,hpos,hpaths⟩ := ih (A.reverseIn p) hmAs hAs
      (fun B hB => hwidth B (List.mem_cons_of_mem _ hB)) hs
    have hstep := replace_inversion_price A.window p A.filling Fin.revPerm hm
    rw [inversion_number_reversal] at hstep
    have hstep' : (inversionNumber (A.reverseIn p) : ℤ) + (inversionNumber A.filling : ℤ) =
        (inversionNumber p : ℤ) + (A.size.choose 2 : ℤ) := by exact_mod_cast hstep
    obtain ⟨hn,hp⟩ := replace_extremes_inherited A.window p A.filling Fin.revPerm hm
      (((n-1)/2 : ℕ) : ℤ) (by exact_mod_cast hw)
    refine ⟨?_,hshort',?_,?_,?_⟩
    · simp only [reverseWindows,List.map_cons,List.sum_cons]
      rw [show A.deficit = (A.size.choose 2 : ℤ) - (inversionNumber A.filling : ℤ) from rfl]
      omega
    · intro i hi
      exact hn i (hneg i hi)
    · intro i hi
      exact hp i (hpos i hi)
    · intro a b hab
      exact hpaths a b (replace_reversal_load_path A.window p A.filling hm hab)

#print axioms FillingWindow.matches_after_apart
#print axioms reverse_windows_spec
end LRX.FiniteWindow
